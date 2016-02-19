/**
 *  Copyright (C) 2011
 *  University of Rochester Department of Computer Science
 *    and
 *  Lehigh University Department of Computer Science and Engineering
 *
 * License: Modified BSD
 *          Please see the file LICENSE.RSTM for licensing information
 */

#include "../profiling.hpp"
#include "algs.hpp"
#include "RedoRAWUtils.hpp"

using stm::UNRECOVERABLE;
using stm::TxThread;
using stm::ABORTED;
using stm::ACTIVE;
using stm::WriteSet;
using stm::WriteSetEntry;
using stm::timestamp;
using stm::timestamp_max;
using stm::threads;
using stm::threadcount;
using stm::greedy_ts;
using stm::SWISS_PHASE2;
using stm::orec_t;
using stm::get_orec;
using stm::id_version_t;
using stm::nanorec_t;
using stm::NanorecList;
using stm::OrecList;
using wlpdstm::Log;


/**
 *  This is a good-faith implementation of SwissTM.
 *
 *  What that means, precisely, has to do with how we translate the SwissTM
 *  algorithm to allow /algorithmic/ comparisons with OrecEager and LLT.
 *  Specifically, we decided in the past that OrecEager and LLT would not use
 *  any of the clever 'lock is a pointer into my writeset' tricks that were
 *  proposed in the TinySTM paper, and so we don't use those tricks here,
 *  either.  The cost is minimal (actually, with the RSTM WriteSet hash, the
 *  tricks are typically not profitable anyway), but it is worth stating, up
 *  front, that we do not adhere to this design point.
 *
 *  Additionally, orec management differs slightly here from in OrecEager and
 *  LLT.  In those systems, we use "2-word" orecs, where the acquirer writes
 *  the old orec value in the second word after acquiring the first word.
 *  This halves the cost of logging, as the list of held locks only gives
 *  orec addresses, not the old values.  However, in SwissTM, there is a
 *  tradeoff where on one hand, having rlocks separate from wlocks can
 *  decrease cache misses for read-only transactions, but on the other hand
 *  doing so doubles logging overhead for read locking by writers at commit
 *  time.  It would be odd to use the 2-word orecs for read locks and not for
 *  write locks, but a more efficient technique is to use the second word of
 *  2-word orecs as the rlock, and then use traditional 2-word lock logging,
 *  where the old lock value is also stored.
 *
 *  Other changes are typically small.  The biggest deals with adding
 *  detection of remote aborts, which wasn't discussed in the paper.
 *
 *  NB: we could factor some CM code out of the RO codepath.  We could also
 *  make the phase2 switch cause a thread to use different function pointers.
 */

namespace
{

const uintptr_t SUCCESS = 0;
const uintptr_t VALIDATION_FAILED = 1;

  struct SwissHT
  {
      static TM_FASTCALL bool begin(TxThread*);
      static TM_FASTCALL void* read(STM_READ_SIG(,,));
      static TM_FASTCALL void write(STM_WRITE_SIG(,,,));
      static TM_FASTCALL void local_write(STM_WRITE_SIG(,,,));
      static TM_FASTCALL void commit(STM_COMMIT_SIG(,));
      static  uintptr_t commit_ht(STM_COMMIT_SIG(,));
      static void end(STM_COMMIT_SIG(tx,));

      static stm::scope_t* rollback(STM_ROLLBACK_SIG(,,,));
      static bool irrevoc(STM_IRREVOC_SIG(,));
      static void onSwitchTo();
      static void cm_start(TxThread*);
      static void cm_on_rollback(TxThread*);
      static void cm_on_write(TxThread*);
      static bool cm_should_abort(TxThread*, uintptr_t owner_id);
      static NOINLINE uintptr_t validate_commit(TxThread*);
      static NOINLINE intptr_t validate_inflight(TxThread*);
  };


  void* helper(void* data){

	TxThread *tx;
	uintptr_t validate_ts_ht = 0;
	bool abort = false;

	while (!(tx = stm::threads[(intptr_t)data].data))
	{
		CFENCE;
	}

	while(tx->running){
		//sem_wait(&tlstm::TxMixinv::prog_thread[ptid].semaphore);
		//while (tlstm::TxMixinv::prog_thread[ptid].requires_validation == false) {
			//_mm_monitor(&tlstm::TxMixinv::prog_thread[ptid].requires_validation, 0, 0);
			//if(tlstm::TxMixinv::prog_thread[ptid].requires_validation == false) {
			//	_mm_mwait(0, 0);
			//}
			//tlstm::TxMixinv::prog_thread[ptid].validated = false;
			//tlstm::TxMixinv::prog_thread[ptid].requires_validation = false;
			//if(!tlstm::TxMixinv::ExtendTx(ptid)){
			//	for (int i = 0; i < tlstm::TxMixinv::specdepth; i++) {
			//		tlstm::TxMixinv::prog_thread[ptid].owners[i]->abort_transaction = true;
			//	}
			//}

			//tlstm::TxMixinv::prog_thread[ptid].validated = true;
		//}

		if(tx->commits_done.val == tx->commits_requested.val){
			//wait if the worker thread is explicitly aborting a transaction
			while(tx->abort_required.val){
			  CFENCE;
			}
		}

		bool should_commit = tx->commits_done.val < tx->commits_requested.val;

		if(!should_commit){
			if(!abort){
				if(tx->validate_ts > validate_ts_ht){
					uintptr_t newts = timestamp.val;
					validate_ts_ht = tx->validate_ts;

					if (SwissHT::validate_inflight(tx) == VALIDATION_FAILED){
					  abort = true;
					  continue;
					}

					tx->start_time = newts;
				}
			}
		} else {
			if(!abort){
				//before committing a read only transaction we need to check if it is valid
				if(!tx->writesets[tx->tx_first_index].data->size()){
					if(tx->validate_ts > validate_ts_ht){
						if (SwissHT::validate_inflight(tx) == VALIDATION_FAILED){
						  abort = true;
						}
					}
				}

				if(!abort)
					abort = tx->commit_ht(tx);
			}

			if(abort) {
				if (tx->nanorecs_v[tx->tx_first_index]->size()) {
					  foreach_ptr(NanorecList, i, tx->nanorecs_v[tx->tx_first_index]) {
						  i->o->v.all = i->v;
					  }
				  }

				tx->num_aborts++;
				abort = false;
			}

			  tx->writesets[tx->tx_first_index].data->reset();
			  tx->r_orecs_v[tx->tx_first_index]->clear();
			  tx->nanorecs_v[tx->tx_first_index]->reset();

			tx->commits_done.val++;
			tx->tx_first_index = tx->commits_done.val % TxThread::SPECULATIVE_TXS;
		}
		CFENCE;
	}

	return 0;
  }

  /**
   * begin swiss transaction: set to active, notify allocator, get start
   * time, and notify CM
   */
  bool SwissHT::begin(TxThread* tx)
  {
	  tx->tx_last_index = tx->commits_requested.val % TxThread::SPECULATIVE_TXS;
	  //tx->scopes[tx->tx_last_index] = tx->scope;

	  //assert(tx->writesets[tx->tx_last_index].data->size() == 0);
	  //assert(tx->nanorecs_v[tx->tx_last_index]->size() == 0);

      tx->alive = ACTIVE;
      tx->allocator.onTxBegin();
      tx->start_time = timestamp.val;
      cm_start(tx);
      return false;
  }

  // word based transactional read
  void* SwissHT::read(STM_READ_SIG(tx,addr,mask))
  {
	  //if (tx->alive == ABORTED)
	  //                  tx->tmabort(tx);
	  //if((uintptr_t)addr < 0xffff){
		//  tx->tmabort(tx);
	  //}

      // get orec address
      orec_t* o = get_orec(addr);

      // do I own the orec?
      if (o->v.all == tx->my_lock_v[tx->tx_last_index].all) {
          CFENCE; // order orec check before possible read of *addr
          // if this address is in my writeset, return looked-up value, else
          // do a direct read from memory
          WriteSetEntry log(STM_WRITE_SET_ENTRY(addr, NULL, mask));
          bool found = tx->writesets[tx->tx_last_index].data->find(log);
          REDO_RAW_CHECK(found, log, mask);

          void* val = *addr;
          REDO_RAW_CLEANUP(val, found, log, mask);
          return val;
      }

      while (true) {
          // get a consistent read of the value, during a period where the
          // read version is unchanging and not locked
          uintptr_t rver1 = o->p;
          CFENCE;
          void* tmp = *addr;
          CFENCE;
          uintptr_t rver2 = o->p;
          // deal with inconsistent reads
          if ((rver1 != rver2) || (rver1 == UINT_MAX)) {
              // bad read: we'll go back to top, but first make sure we didn't
              // get aborted
              if (tx->alive == ABORTED)
                  tx->tmabort(tx);
              continue;
          }
          // the read was good: log the orec
          tx->r_orecs_v[tx->tx_last_index]->insert(o);

          // do we need to extend our timestamp?
          if (rver1 > tx->start_time) {
              /*uintptr_t newts = timestamp.val;
              CFENCE;
              if(validate_inflight(tx) == VALIDATION_FAILED)
            	  tx->tmabort(tx);
              CFENCE;
              tx->start_time = newts;*/
        	  tx->validate_ts = timestamp.val;
          }
          return tmp;
      }
  }

  /**
   *  SwissTM write
   */
  void SwissHT::write(STM_WRITE_SIG(tx,addr,val,mask))
  {
      // put value in redo log
      tx->writesets[tx->tx_last_index].data->insert(WriteSetEntry(STM_WRITE_SET_ENTRY(addr, val, mask)));

      // get the orec addr
      orec_t* o = get_orec(addr);

      // if I'm already the lock holder, we're done!
      if (o->v.all == tx->my_lock_v[tx->tx_last_index].all)
          return;

      while(o->v.fields.lock && o->v.fields.id/TxThread::SPECULATIVE_TXS == tx->my_lock_v[tx->tx_last_index].fields.id/TxThread::SPECULATIVE_TXS){
    	  if(tx->alive == ABORTED)
    		  tx->tmabort(tx);
    	  CFENCE;
      }

      while (true) {
          // look at write lock
          id_version_t ivt;
          ivt.all = o->v.all;
          // if locked, CM will either tell us to self-abort, or to continue
          if (ivt.fields.lock) {
              if (cm_should_abort(tx, ivt.fields.id/TxThread::SPECULATIVE_TXS))
                  tx->tmabort(tx);
              // check liveness before continuing
              if (tx->alive == ABORTED)
                  tx->tmabort(tx);
              continue;
          }

          // if I can't lock it, start over
          if (!bcasptr(&o->v.all, ivt.all, tx->my_lock_v[tx->tx_last_index].all)) {
              // check liveness before continuing
              if (tx->alive == ABORTED)
                  tx->tmabort(tx);
              continue;
          }

          // log this lock acquire
          tx->nanorecs_v[tx->tx_last_index]->insert(nanorec_t(o, o->p));

          // if read version too high, validate and extend ts
          if (o->p > tx->start_time) {
              tx->validate_ts = timestamp.val;

              /*uintptr_t newts = timestamp.val;
				CFENCE;
				if(validate_inflight(tx) == VALIDATION_FAILED)
				  tx->tmabort(tx);
				CFENCE;
				tx->start_time = newts;*/
          }

          // notify CM & return
          cm_on_write(tx);
          return;
      }
  }

  void SwissHT::local_write(STM_WRITE_SIG(tx,addr,val,mask))
  {
	  *addr = val;
  }

  void SwissHT::commit(STM_COMMIT_SIG(tx,))
    {

  	  tx->commits_requested.val++;

  	  bool waited = false;
  	//if (tx->alive == ABORTED)
  	  //                tx->tmabort(tx);
	  //if(tx->abort_transaction){
		//  tx->tmabort(tx);
	  //}

  	  while(tx->commits_requested.val - tx->commits_done.val == TxThread::SPECULATIVE_TXS){
  		  if(!waited){
  			  tx->wait_commit++;
  			  waited = true;
  		  }
/*
  		  if(tx->abort_transaction){
  			  tx->tmabort(tx);
  		  }*/
  		  CFENCE;
  	  }
/*
  	  while(tx->dirty_commit != tx->commits_done){
  		  tx->writesets[tx->dirty_commit % TxThread::SPECULATIVE_TXS]->reset();
  		  tx->local_writesets[tx->dirty_commit % TxThread::SPECULATIVE_TXS]->reset();
//  		  tx->r_orecs_v[tx->dirty_commit % TxThread::SPECULATIVE_TXS]->clear();
//  		  tx->nanorecs_v[tx->dirty_commit % TxThread::SPECULATIVE_TXS]->clear();
  		  tx->dirty_commit++;
  	  }*/
    }

  /**
   *  commit a read-write transaction
   *
   *  Note: we don't check if we've been remote aborted here, because there
   *  are no while/continue patterns in this code.  If someone asked us to
   *  abort, we can ignore them... either we commit and zero our state,
   *  or we abort anyway.
   */
  uintptr_t SwissHT::commit_ht(STM_COMMIT_SIG(tx,upper_stack_bound))
  {
      // read-only case
      if (!tx->writesets[tx->tx_first_index].data->size()) {
          //tx->r_orecs_v[tx->tx_first_index]->clear();
          OnReadOnlyCommit(tx);
          return SUCCESS;
      }

      // writing case:

      // first, grab all read locks covering the write set
      foreach_ptr(NanorecList, i, tx->nanorecs_v[tx->tx_first_index]) {
          i->o->p = UINT_MAX;
      }

      // increment the global timestamp, and maybe validate
      tx->end_time = 1 + faiptr(&timestamp.val);
      if (tx->end_time > (tx->start_time + 1)){
          uintptr_t ret = validate_commit(tx);
          if(ret == VALIDATION_FAILED){
        	  return VALIDATION_FAILED;
          }
      }

      // run the redo log
      tx->writesets[tx->tx_first_index].data->writeback(STM_WHEN_PROTECT_STACK(upper_stack_bound));

      // now release all read and write locks covering the writeset
      foreach_ptr(NanorecList, i, tx->nanorecs_v[tx->tx_first_index]) {
    	  i->o->p = tx->end_time;
          CFENCE;
          i->o->v.all = tx->end_time;
      }

      // clean up
      //it's easier to cleanup writesets on the worker threads
     // tx->writesets[tx->tx_first_index].data->reset();
      //tx->r_orecs_v[tx->tx_first_index]->clear();
      //tx->nanorecs_v[tx->tx_first_index]->reset();
      OnReadWriteCommit(tx);

      return SUCCESS;
  }

  // rollback a transaction
  stm::scope_t*
  SwissHT::rollback(STM_ROLLBACK_SIG(tx, upper_stack_bound, except, len))
  {
	  tx->abort_required.val = 1;

	  	  //while(tx->abort_transaction == false){
	  		//  CFENCE;
	  	  //}

	        stm::PreRollback(tx);

	        // Perform writes to the exception object if there were any... taking the
	        // branch overhead without concern because we're not worried about
	        // rollback overheads.
	        //STM_ROLLBACK(tx->writesets[tx->tx_last_index], upper_stack_bound, except, len);
	        //pthread_mutex_lock(&tx->mutex);

	        //for(int i = tx->commits_requested; i >= tx->commits_done; i--){
	      	  //int index = i % TxThread::SPECULATIVE_TXS;

	  		  //tx->local_writesets[tx->tx_last_index]->writeback();
	  		  //tx->local_writesets[tx->tx_last_index]->reset();
	  		  //ValueListEntry entry(0,0);
	  		  //while(tx->read_queues[i]->try_dequeue(entry));
	      	  tx->writesets[tx->tx_last_index].data->rollback();

	  	      // now release all read and write locks covering the writeset... often,
	  	      // we didn't acquire the read locks, but it's harmless to do it like
	  	      // this
	  	      if (tx->nanorecs_v[tx->tx_last_index]->size()) {
	  	          foreach_ptr(NanorecList, i, tx->nanorecs_v[tx->tx_last_index]) {
	  	        	  i->o->v.all = i->v;
	  	          }
	  	      }

	  	      tx->writesets[tx->tx_last_index].data->reset();
	  	      tx->r_orecs_v[tx->tx_last_index]->clear();
	  	      tx->nanorecs_v[tx->tx_last_index]->reset();
//	        }

	        //printf("aborting %d\n", tx->commits_requested);

	        tx->commits_requested.val = tx->commits_done.val;

	        // contention management on rollback
	        cm_on_rollback(tx);

	        tx->abort_required.val = 0;
	//        tx->abort_transaction = false;
	        CFENCE;

	        return PostRollback(tx);

	        //return tx->scopes[tx->tx_first_index];
  }

  // Validate a transaction's read set
  //
  // for in-flight transactions, write locks don't provide a fallback when
  // read-lock validation fails
  intptr_t SwissHT::validate_inflight(TxThread* tx)
  {
      foreach_log_ptr(wlpdstm::Log<orec_t*>, i, tx->r_orecs_v[tx->tx_last_index]) {
          if ((*i)->p > tx->start_time)
              return VALIDATION_FAILED;
      }
      return SUCCESS;
  }

  // validate a transaction's write set
  //
  // for committing transactions, there is a backup plan wh read-lock
  // validation fails
  uintptr_t SwissHT::validate_commit(TxThread* tx)
  {
      foreach_log_ptr(wlpdstm::Log<orec_t*>, i, tx->r_orecs_v[tx->tx_first_index]) {
          if ((*i)->p > tx->start_time) {
              if ((*i)->v.all != tx->my_lock_v[tx->tx_first_index].all) {
            	  foreach_ptr(NanorecList, i, tx->nanorecs_v[tx->tx_first_index]) {
                	  i->o->p = i->v;
                  }
                  return VALIDATION_FAILED;
              }
          }
      }
      return SUCCESS;
  }

  // cotention managers
  void SwissHT::cm_start(TxThread* tx)
  {
      if (!tx->consec_aborts)
          tx->cm_ts = UINT_MAX;
  }

  void SwissHT::cm_on_write(TxThread* tx)
  {
      if ((tx->cm_ts == UINT_MAX) && (tx->writesets[tx->tx_last_index].data->size() == SWISS_PHASE2))
          tx->cm_ts = 1 + faiptr(&greedy_ts.val);
  }

  bool SwissHT::cm_should_abort(TxThread* tx, uintptr_t owner_id)
  {
      // if caller has MAX priority, it should self-abort
      if (tx->cm_ts == UINT_MAX)
          return true;

      // self-abort if owner's priority lower than mine
      TxThread* owner = threads[owner_id - 1].data;
      if (owner->cm_ts < tx->cm_ts)
          return true;

      // request owner to remote abort
      owner->alive = ABORTED;
      return false;
  }

  void SwissHT::cm_on_rollback(TxThread* tx)
  {
      exp_backoff(tx);
  }

  /*** Become irrevocable via abort-and-restart */
  bool SwissHT::irrevoc(STM_IRREVOC_SIG(,)) { return false; }

  /***  Keep SwissTM metadata healthy */
  void SwissHT::onSwitchTo()
  {
      timestamp.val = MAXIMUM(timestamp.val, timestamp_max.val);
  }

  void SwissHT::end(STM_COMMIT_SIG(tx,)){
  	  while(tx->commits_done.val < tx->commits_requested.val){
  		  //if(tx->alive == stm::ABORTED){
  		//	  tx->tmabort(tx);
  		  //}
  		  CFENCE;
  	  }
    }
}

namespace stm {
  /**
   *  Every STM must provide an 'initialize' function that specifies how the
   *  algorithm is to be used when adaptivity is off.
   *
   *  Some of this is a bit ugly right now, but when we fix the way adaptive
   *  policies work it will clean itself.
   */
  template<>
  void initTM<SwissHT>()
  {
      // set the name
      stms[SwissHT].name      = "SwissHT";

      // set the pointers
      stms[SwissHT].begin     = ::SwissHT::begin;
      stms[SwissHT].commit    = ::SwissHT::commit;
      stms[SwissHT].read      = ::SwissHT::read;
      stms[SwissHT].write     = ::SwissHT::write;
      stms[SwissHT].local_write     = ::SwissHT::local_write;
      stms[SwissHT].rollback  = ::SwissHT::rollback;
      stms[SwissHT].irrevoc   = ::SwissHT::irrevoc;
      stms[SwissHT].switcher  = ::SwissHT::onSwitchTo;
      stms[SwissHT].privatization_safe = false;
      stms[SwissHT].helper = helper;
      stms[SwissHT].helperThreads = TxThread::numThreads;
      stms[SwissHT].commit_ht = SwissHT::commit_ht;
      stms[SwissHT].end = SwissHT::end;
  }
}
