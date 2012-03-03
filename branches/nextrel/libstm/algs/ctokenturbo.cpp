/**
 *  Copyright (C) 2011
 *  University of Rochester Department of Computer Science
 *    and
 *  Lehigh University Department of Computer Science and Engineering
 *
 * License: Modified BSD
 *          Please see the file LICENSE.RSTM for licensing information
 */

/**
 *  CTokenTurbo Implementation
 *
 *    This code is like CToken, except we aggressively check if a thread is the
 *    'oldest', and if it is, we switch to an irrevocable 'turbo' mode with
 *    in-place writes and no validation.
 */

#include "../profiling.hpp"
#include "algs.hpp"
#include "RedoRAWUtils.hpp"
#include <stm/UndoLog.hpp> // STM_DO_MASKED_WRITE

using stm::TxThread;
using stm::timestamp;
using stm::timestamp_max;
using stm::threads;
using stm::threadcount;
using stm::last_complete;
using stm::OrecList;
using stm::WriteSet;
using stm::UNRECOVERABLE;
using stm::orec_t;
using stm::get_orec;
using stm::WriteSetEntry;
using stm::Self;
using stm::OnFirstWrite;
using stm::OnReadWriteCommit;
using stm::OnReadOnlyCommit;
using stm::PreRollback;
using stm::PostRollback;
using stm::GoTurbo;
using stm::CheckTurboMode;

/**
 *  Declare the functions that we're going to implement, so that we can avoid
 *  circular dependencies.
 */
namespace {
  struct CTokenTurbo {
      static TM_FASTCALL bool begin();
      static TM_FASTCALL void* read_ro(STM_READ_SIG(,));
      static TM_FASTCALL void* read_rw(STM_READ_SIG(,));
      static TM_FASTCALL void* read_turbo(STM_READ_SIG(,));
      static TM_FASTCALL void write_ro(STM_WRITE_SIG(,,));
      static TM_FASTCALL void write_rw(STM_WRITE_SIG(,,));
      static TM_FASTCALL void write_turbo(STM_WRITE_SIG(,,));
      static TM_FASTCALL void commit_ro();
      static TM_FASTCALL void commit_rw();
      static TM_FASTCALL void commit_turbo();

      static stm::scope_t* rollback(STM_ROLLBACK_SIG(,));
      static bool irrevoc();
      static void onSwitchTo();
      static NOINLINE void validate(uintptr_t finish_cache);
  };

  /**
   *  CTokenTurbo begin:
   */
  bool
  CTokenTurbo::begin()
  {
      Self.allocator.onTxBegin();

      // get time of last finished txn
      Self.ts_cache = last_complete.val;

      // switch to turbo mode?
      //
      // NB: this only applies to transactions that aborted after doing a write
      if (Self.ts_cache == ((uintptr_t)Self.order - 1))
          GoTurbo(read_turbo, write_turbo, commit_turbo);

      return false;
  }

  /**
   *  CTokenTurbo commit (read-only):
   */
  void
  CTokenTurbo::commit_ro()
  {
      Self.r_orecs.reset();
      Self.order = -1;
      OnReadOnlyCommit();
  }

  /**
   *  CTokenTurbo commit (writing context):
   *
   *  Only valid with pointer-based adaptivity
   */
  void
  CTokenTurbo::commit_rw()
  {
      // we need to transition to fast here, but not till our turn
      while (last_complete.val != ((uintptr_t)Self.order - 1)) {
          if (TxThread::tmbegin != begin)
              Self.tmabort();
      }
      // validate
      foreach (OrecList, i, Self.r_orecs) {
          // read this orec
          uintptr_t ivt = (*i)->v.all;
          // if it has a timestamp of ts_cache or greater, abort
          if (ivt > Self.ts_cache)
              Self.tmabort();
      }
      // writeback
      if (Self.writes.size() != 0) {
          // mark every location in the write set, and perform write-back
          foreach (WriteSet, i, Self.writes) {
              orec_t* o = get_orec(i->addr);
              o->v.all = Self.order;
              CFENCE; // WBW
              *i->addr = i->val;
          }
      }

      CFENCE; // wbw between writeback and last_complete.val update
      last_complete.val = Self.order;

      // set status to committed...
      Self.order = -1;

      // commit all frees, reset all lists
      Self.r_orecs.reset();
      Self.writes.reset();
      OnReadWriteCommit( read_ro, write_ro, commit_ro);
  }

  /**
   *  CTokenTurbo commit (turbo mode):
   */
  void
  CTokenTurbo::commit_turbo()
  {
      CFENCE; // wbw between writeback and last_complete.val update
      last_complete.val = Self.order;

      // set status to committed...
      Self.order = -1;

      // commit all frees, reset all lists
      Self.r_orecs.reset();
      Self.writes.reset();
      OnReadWriteCommit( read_ro, write_ro, commit_ro);
  }

  /**
   *  CTokenTurbo read (read-only transaction)
   */
  void*
  CTokenTurbo::read_ro(STM_READ_SIG(addr,))
  {
      void* tmp = *addr;
      CFENCE; // RBR between dereference and orec check

      // get the orec addr, read the orec's version#
      orec_t* o = get_orec(addr);
      uintptr_t ivt = o->v.all;
      // abort if this changed since the last time I saw someone finish
      if (ivt > Self.ts_cache)
          Self.tmabort();

      // log orec
      Self.r_orecs.insert(o);

      // possibly validate before returning
      if (last_complete.val > Self.ts_cache) {
          uintptr_t finish_cache = last_complete.val;
          foreach (OrecList, i, Self.r_orecs) {
              // read this orec
              uintptr_t ivt_inner = (*i)->v.all;
              // if it has a timestamp of ts_cache or greater, abort
              if (ivt_inner > Self.ts_cache)
                  Self.tmabort();
          }
          // now update the ts_cache to remember that at this time, we were
          // still valid
          Self.ts_cache = finish_cache;
      }
      return tmp;
  }

  /**
   *  CTokenTurbo read (writing transaction)
   */
  void*
  CTokenTurbo::read_rw(STM_READ_SIG(addr,mask))
  {
      // check the log for a RAW hazard, we expect to miss
      WriteSetEntry log(STM_WRITE_SET_ENTRY(addr, NULL, mask));
      bool found = Self.writes.find(log);
      REDO_RAW_CHECK(found, log, mask);

      void* tmp = *addr;
      REDO_RAW_CLEANUP(tmp, found, log, mask);
      CFENCE; // RBR between dereference and orec check

      // get the orec addr, read the orec's version#
      orec_t* o = get_orec(addr);
      uintptr_t ivt = o->v.all;
      // abort if this changed since the last time I saw someone finish
      if (ivt > Self.ts_cache)
          Self.tmabort();

      // log orec
      Self.r_orecs.insert(o);

      // validate, and if we have writes, then maybe switch to fast mode
      if (last_complete.val > Self.ts_cache)
          validate( last_complete.val);
      return tmp;
  }

  /**
   *  CTokenTurbo read (read-turbo mode)
   */
  void*
  CTokenTurbo::read_turbo(STM_READ_SIG(addr,))
  {
      return *addr;
  }

  /**
   *  CTokenTurbo write (read-only context)
   */
  void
  CTokenTurbo::write_ro(STM_WRITE_SIG(addr,val,mask))
  {
      // we don't have any writes yet, so we need to get an order here
      Self.order = 1 + faiptr(&timestamp.val);

      // record the new value in a redo log
      Self.writes.insert(WriteSetEntry(STM_WRITE_SET_ENTRY(addr, val, mask)));

      OnFirstWrite( read_rw, write_rw, commit_rw);

      // go turbo?
      //
      // NB: we test this on first write, but not subsequent writes, because up
      //     until now we didn't have an order, and thus weren't allowed to use
      //     turbo mode
      validate( last_complete.val);
  }

  /**
   *  CTokenTurbo write (writing context)
   */
  void
  CTokenTurbo::write_rw(STM_WRITE_SIG(addr,val,mask))
  {
      // record the new value in a redo log
      Self.writes.insert(WriteSetEntry(STM_WRITE_SET_ENTRY(addr, val, mask)));
  }

  /**
   *  CTokenTurbo write (turbo mode)
   */
  void
  CTokenTurbo::write_turbo(STM_WRITE_SIG(addr,val,mask))
  {
      // mark the orec, then update the location
      orec_t* o = get_orec(addr);
      o->v.all = Self.order;
      CFENCE;
      STM_DO_MASKED_WRITE(addr, val, mask);
  }

  /**
   *  CTokenTurbo unwinder:
   *
   *    NB: self-aborts in Turbo Mode are not supported.  We could add undo
   *        logging to address this, and add it in Pipeline too.
   */
  stm::scope_t*
  CTokenTurbo::rollback(STM_ROLLBACK_SIG( except, len))
  {
      PreRollback();
      // we cannot be in turbo mode
      if (CheckTurboMode( read_turbo))
          UNRECOVERABLE("Attempting to abort a turbo-mode transaction!");

      // Perform writes to the exception object if there were any... taking the
      // branch overhead without concern because we're not worried about
      // rollback overheads.
      STM_ROLLBACK(Self.writes, except, len);

      Self.r_orecs.reset();
      Self.writes.reset();
      // NB: we can't reset pointers here, because if the transaction
      //     performed some writes, then it has an order.  If it has an
      //     order, but restarts and is read-only, then it still must call
      //     commit_rw to finish in-order
      return PostRollback();
  }

  /**
   *  CTokenTurbo in-flight irrevocability:
   */
  bool CTokenTurbo::irrevoc()
  {
      UNRECOVERABLE("CTokenTurbo Irrevocability not yet supported");
      return false;
  }

  /**
   *  CTokenTurbo validation
   */
  void CTokenTurbo::validate(uintptr_t finish_cache)
  {
      foreach (OrecList, i, Self.r_orecs) {
          // read this orec
          uintptr_t ivt = (*i)->v.all;
          // if it has a timestamp of ts_cache or greater, abort
          if (ivt > Self.ts_cache)
              Self.tmabort();
      }
      // now update the finish_cache to remember that at this time, we were
      // still valid
      Self.ts_cache = finish_cache;

      // and if we are now the oldest thread, transition to fast mode
      if (Self.ts_cache == ((uintptr_t)Self.order - 1)) {
          if (Self.writes.size() != 0) {
              // mark every location in the write set, and perform write-back
              foreach (WriteSet, i, Self.writes) {
                  orec_t* o = get_orec(i->addr);
                  o->v.all = Self.order;
                  CFENCE; // WBW
                  *i->addr = i->val;
              }
              GoTurbo(read_turbo, write_turbo, commit_turbo);
          }
      }
  }

  /**
   *  Switch to CTokenTurbo:
   *
   *    The timestamp must be >= the maximum value of any orec.  Some algs use
   *    timestamp as a zero-one mutex.  If they do, then they back up the
   *    timestamp first, in timestamp_max.
   *
   *    Also, last_complete must equal timestamp
   *
   *    Also, all threads' order values must be -1
   */
  void
  CTokenTurbo::onSwitchTo()
  {
      timestamp.val = MAXIMUM(timestamp.val, timestamp_max.val);
      last_complete.val = timestamp.val;
      for (uint32_t i = 0; i < threadcount.val; ++i)
          threads[i]->order = -1;
  }
}

namespace stm {
  /**
   *  CTokenTurbo initialization
   */
  template<>
  void initTM<CTokenTurbo>()
  {
      // set the name
      stms[CTokenTurbo].name      = "CTokenTurbo";

      // set the pointers
      stms[CTokenTurbo].begin     = ::CTokenTurbo::begin;
      stms[CTokenTurbo].commit    = ::CTokenTurbo::commit_ro;
      stms[CTokenTurbo].read      = ::CTokenTurbo::read_ro;
      stms[CTokenTurbo].write     = ::CTokenTurbo::write_ro;
      stms[CTokenTurbo].rollback  = ::CTokenTurbo::rollback;
      stms[CTokenTurbo].irrevoc   = ::CTokenTurbo::irrevoc;
      stms[CTokenTurbo].switcher  = ::CTokenTurbo::onSwitchTo;
      stms[CTokenTurbo].privatization_safe = true;
  }
}
