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
 *  NOrecHTO Implementation
 *
 *    This STM was published by Dalessandro et al. at PPoPP 2010.  The
 *    algorithm uses a single sequence lock, along with value-based validation,
 *    for concurrency control.  This variant offers semantics at least as
 *    strong as Asymmetric Lock Atomicity (ALA).
 */

#include "../cm.hpp"
#include "algs.hpp"
#include "RedoRAWUtils.hpp"

// Don't just import everything from stm. This helps us find bugs.
using stm::TxThread;
using stm::timestamp;
using stm::threads;
using stm::WriteSetEntry;
using stm::ValueList;
using stm::ValueListEntry;

namespace {

  const uintptr_t SUCCESS = 0;
  const uintptr_t VALIDATION_FAILED = 1;
  NOINLINE uintptr_t validate(TxThread*, int);
  bool irrevoc(STM_IRREVOC_SIG(,));
  void onSwitchTo();

  template <class CM>
  struct NOrecHTO_Generic
  {
      static TM_FASTCALL bool begin(TxThread*);
      static TM_FASTCALL void commit(STM_COMMIT_SIG(,));
      static uintptr_t commit_ht(STM_COMMIT_SIG(,));
      static TM_FASTCALL void commit_ro(STM_COMMIT_SIG(,));
      static TM_FASTCALL void commit_rw(STM_COMMIT_SIG(,));
      static TM_FASTCALL void* read_ro(STM_READ_SIG(,,));
      static TM_FASTCALL void* read_rw(STM_READ_SIG(,,));
      static TM_FASTCALL void write_ro(STM_WRITE_SIG(,,,));
      static TM_FASTCALL void write_rw(STM_WRITE_SIG(,,,));
      static TM_FASTCALL void local_write(STM_WRITE_SIG(,,,));
      static stm::scope_t* rollback(STM_ROLLBACK_SIG(,,,));
      static void end(STM_COMMIT_SIG(tx,));
      static void initialize(int id, const char* name);
  };

  uintptr_t
  validate(TxThread* tx, int index)
  {
      while (true) {
          // read the lock until it is even
          uintptr_t s = timestamp.val;
          if ((s & 1) == 1)
              continue;

          // check the read set
          //CFENCE;
          // don't branch in the loop---consider it backoff if we fail
          // validation early
          bool valid = true;
          //pthread_mutex_lock(&tx->mutex);
          //printf("validate first index: %d size: %d \n", tx->tx_first_index, tx->read_logs[tx->tx_first_index].size());

          //foreach (ValueList, i, *tx->read_logs[tx->tx_first_index])
          /*for (ValueList::iterator i = tx->read_logs[tx->tx_first_index]->begin(),
			   j = tx->read_logs[tx->tx_first_index]->end(); i != j; ++i)
          {*/
          //printf("%d \n", tx->read_logs[tx->tx_first_index]->get_size());
          //CFENCE;
          //int counter = 0;

          for(wlpdstm::Log<ValueListEntry>::iterator iter = tx->read_logs[index]->begin();iter.hasNext();iter.next()) {
          	  ValueListEntry &entry = *iter;
        	  valid &= entry.isValid();
        	  //counter++;
          	  /*if(!valid){
          		  printf("ws size: %d address: %x memory value: %d logged value: %d counter: %d\n",tx->writesets[tx->tx_first_index]->size(), entry.addr, (intptr_t)*entry.addr, (intptr_t)entry.val, counter);//,tx->read_logs[tx->tx_first_index]->size());
          	  //}
          		for(wlpdstm::Log<ValueListEntry>::iterator iter = tx->read_logs[tx->tx_first_index]->begin();iter.hasNext();iter.next()) {
          												  ValueListEntry &entry = *iter;
          												          	  printf("valor: %d\n", (intptr_t)entry.val);
          											  }

          		  WriteSetEntry log(entry.addr, NULL);

				bool found = false;
				int i;
				//for(i=tx->commits_requested-1; i >= tx->commits_done && found == false; i--){
				//					  found = tx->writesets[i % SPECULATIVE_TXS]->find(log);
				//				  }
				for(i=0; i < SPECULATIVE_TXS && found == false; i++){
					  found = tx->writesets[i]->find(log);
				  }

				if(found == true)
					printf("found validate first: %d value: %x done: %d requested: %d\n", i-1, log.val, tx->commits_done, tx->commits_requested);

				break;
          	  }
          	  CFENCE;*/
          }
          //pthread_mutex_unlock(&tx->mutex);

          if (!valid)
              return VALIDATION_FAILED;

          // restart if timestamp changed during read set iteration
          CFENCE;
          if (timestamp.val == s)
              return s;
      }
  }

  bool
  irrevoc(STM_IRREVOC_SIG(tx,upper_stack_bound))
  {
      while (!bcasptr(&timestamp.val, tx->start_times[tx->tx_last_index].val, tx->start_times[tx->tx_last_index].val + 1))
          if ((tx->start_times[tx->tx_last_index].val = validate(tx, tx->tx_last_index)) == VALIDATION_FAILED)
              return false;

      // redo writes
      tx->writesets[tx->tx_last_index].data->writeback(STM_WHEN_PROTECT_STACK(upper_stack_bound));

      //printf("irrevoc\n");

      // Release the sequence lock, then clean up
      CFENCE;
      timestamp.val = tx->start_times[tx->tx_last_index].val + 2;
      tx->read_logs[tx->tx_last_index]->clear();
      tx->writesets[tx->tx_last_index].data->reset();
      return true;
  }

  void
  onSwitchTo() {
      // We just need to be sure that the timestamp is not odd, or else we will
      // block.  For safety, increment the timestamp to make it even, in the event
      // that it is odd.
      if (timestamp.val & 1)
          ++timestamp.val;
  }

  void* helper(void* data){

	TxThread *tx;

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

		if(tx->abort_required.val && tx->tx_first_index == tx->tx_last_index){
			tx->alive = stm::ABORTED;
			//printf("abort 1 %d\n", tx->commits_done);
			//wait until the worker thread aborts the transaction(s)
			while(tx->alive){
			  CFENCE;
			}
		}

		bool should_commit = tx->commits_done.val < tx->commits_requested.val;

		if(should_commit){

			//printf("%d\n", tx->read_logs[tx->tx_first_index]->size());
			if(tx->commit_ht(tx) == SUCCESS){
				//printf("commit first index: %d reads: %d\n", tx->tx_first_index, tx->read_logs[tx->tx_first_index].size());
				/*if(tx->read_logs[tx->tx_first_index]->get_size() != 2){
									  printf("wrong size %d %d\n",tx->read_logs[tx->tx_first_index]->get_size(), tx->commits_done);
									  for(wlpdstm::Log<ValueListEntry>::iterator iter = tx->read_logs[tx->tx_first_index]->begin();iter.hasNext();iter.next()) {
										  ValueListEntry &entry = *iter;
										          	  printf("valor: %d\n", (intptr_t)entry.val);
									  }
				}*/

				  tx->read_logs[tx->tx_first_index]->clear();

				tx->commits_done.val++;
				tx->tx_first_index = tx->commits_done.val % TxThread::SPECULATIVE_TXS;
			}
		}
		CFENCE;
	}

	return 0;
  }

  template <typename CM>
  void
  NOrecHTO_Generic<CM>::initialize(int id, const char* name)
  {
      // set the name
      stm::stms[id].name = name;

      // set the pointers
      stm::stms[id].begin     = NOrecHTO_Generic<CM>::begin;
      stm::stms[id].commit    = NOrecHTO_Generic<CM>::commit;
      stm::stms[id].read      = NOrecHTO_Generic<CM>::read_rw;
      stm::stms[id].write     = NOrecHTO_Generic<CM>::write_rw;
      stm::stms[id].local_write = NOrecHTO_Generic<CM>::local_write;
      stm::stms[id].irrevoc   = irrevoc;
      stm::stms[id].switcher  = onSwitchTo;
      stm::stms[id].privatization_safe = true;
      stm::stms[id].rollback  = NOrecHTO_Generic<CM>::rollback;
      stm::stms[id].helper = helper;
      stm::stms[id].helperThreads = TxThread::numThreads;
      stm::stms[id].commit_ht = NOrecHTO_Generic<CM>::commit_ht;
  }

  template <class CM>
  bool
  NOrecHTO_Generic<CM>::begin(TxThread* tx)
  {
	  tx->tx_last_index = tx->commits_requested.val % TxThread::SPECULATIVE_TXS;
	  tx->scopes[tx->tx_last_index] = tx->scope;

	  tx->alive = stm::ACTIVE;

	  /*if(!tx->read_logs[tx->tx_last_index]->empty())
	  		  printf("%d error: read log\n", tx->commits_requested);
	  if(tx->read_queues[tx->tx_last_index]->size_approx() > 0)
	  		  printf("%d error: read queue\n", tx->commits_requested);
	  if(tx->writesets[tx->tx_last_index]->size() > 0)
	  		  printf("%d error: write log\n", tx->commits_requested);
*/
      // Originally, NOrecHTO required us to wait until the timestamp is odd
      // before we start.  However, we can round down if odd, in which case
      // we don't need control flow here.

      // Sample the sequence lock, if it is even decrement by 1
      tx->start_times[tx->tx_last_index].val = timestamp.val & ~(1L);

      // notify the allocator
      tx->allocator.onTxBegin();

      // notify CM
      CM::onBegin(tx);

      return false;
  }

  template <class CM>
  uintptr_t
  NOrecHTO_Generic<CM>::commit_ht(STM_COMMIT_SIG(tx,upper_stack_bound))
  {
	  /*do{
		  if(tx->abort_transaction)
			  tx->tmabort(tx);
		  CFENCE;
	  }while(tx->requires_validation || !tx->validated);
*/
	  // From a valid state, the transaction increments the seqlock.  Then it
      // does writeback and increments the seqlock again

      // read-only is trivially successful at last read
	  if (!tx->writesets[tx->tx_first_index].data->size()) {
		  //pthread_mutex_lock(&tx->mutex);
          CM::onCommit(tx);
          OnReadOnlyCommit(tx);
          //printf("commit %d - first index: %d size: %d\n",tx->num_ro, tx->tx_first_index, tx->read_logs[tx->tx_first_index]->size());
          //printf("commit %d - last index: %d size: %d\n",tx->num_ro, tx->tx_last_index, tx->read_logs[tx->tx_last_index]->size());

		  //tx->commited = true;

		//pthread_mutex_unlock(&tx->mutex);

		return SUCCESS;
      }

      // get the lock and validate (use RingSTM obstruction-free technique)
      while (!bcasptr(&timestamp.val, tx->start_times[tx->tx_first_index].val, tx->start_times[tx->tx_first_index].val + 1))
          if ((tx->start_times[tx->tx_first_index].val = validate(tx, tx->tx_first_index)) == VALIDATION_FAILED){
        	  tx->alive = stm::ABORTED;
        	  //printf("abort 2 %d\n", tx->commits_done);
        	  //wait until the worker thread aborts the transaction(s)
        	  while(tx->alive){
        		  CFENCE;
        	  }
        	  return VALIDATION_FAILED;
          }
      //pthread_mutex_lock(&tx->mutex);

      tx->writesets[tx->tx_first_index].data->writeback(STM_WHEN_PROTECT_STACK(upper_stack_bound));

      // Release the sequence lock, then clean up
      CFENCE;
      timestamp.val = tx->start_times[tx->tx_first_index].val + 2;
      //pthread_mutex_unlock(&tx->mutex);
      CM::onCommit(tx);

      OnReadWriteCommit(tx);

      return SUCCESS;
  }

  template <class CM>
  void
  NOrecHTO_Generic<CM>::commit(STM_COMMIT_SIG(tx,))
  {
	  /*CFENCE;
	  while((tx->tx_last_index + 1) % SPECULATIVE_TXS == tx->tx_first_index){ //&& !tx->commited){
		  if(tx->abort_transaction)
			  tx->tmabort(tx);
	  }*/
	  tx->commits_requested.val++;

	  bool waited = false;

	  while(tx->commits_requested.val - tx->commits_done.val == TxThread::SPECULATIVE_TXS){
		  if(!waited){
			  tx->wait_commit++;
			  waited = true;
		  }
		  if(tx->alive == stm::ABORTED){
			  tx->tmabort(tx);
		  }
		  CFENCE;
	  }

	  while(tx->dirty_commit != tx->commits_done.val){
		  tx->writesets[tx->dirty_commit % TxThread::SPECULATIVE_TXS].data->reset();
		  tx->local_writesets[tx->dirty_commit % TxThread::SPECULATIVE_TXS].data->reset();
		  //printf("%d\n", tx->commits_done);
		  //printf("size %d\n",tx->writesets[tx->tx_dirty_index]->size());
		  tx->dirty_commit++;
	  }
  }

  template <class CM>
  void*
  NOrecHTO_Generic<CM>::read_ro(STM_READ_SIG(tx,addr,mask))
  {
	  if(tx->alive == stm::ABORTED){
		  tx->tmabort(tx);
	  }

      // read the location to a temp
      void* tmp = *addr;
      CFENCE;

      // A read is valid iff it occurs during a period where the seqlock does
      // not change and is even.  This code also polls for new changes that
      // might necessitate a validation.


      // if the timestamp has changed since the last read, we must validate and
      // restart this read
      while (tx->start_times[tx->tx_last_index].val != timestamp.val) {
          if ((tx->start_times[tx->tx_last_index].val = validate(tx, tx->tx_last_index)) == VALIDATION_FAILED)
              tx->tmabort(tx);
          tmp = *addr;
          CFENCE;
      }
      tx->read_logs[tx->tx_last_index]->insert(STM_VALUE_LIST_ENTRY(addr, tmp, mask));

      return tmp;
  }

  template <class CM>
  void*
  NOrecHTO_Generic<CM>::read_rw(STM_READ_SIG(tx,addr,mask))
  {
      // check the log for a RAW hazard, we expect to miss
      WriteSetEntry log(STM_WRITE_SET_ENTRY(addr, NULL, mask));
      bool found = tx->writesets[tx->tx_last_index].data->find(log);
      REDO_RAW_CHECK(found, log, mask);

      // Use the code from the read-only read barrier. This is complicated by
      // the fact that, when we are byte logging, we may have successfully read
      // some bytes from the write log (if we read them all then we wouldn't
      // make it here). In this case, we need to log the mask for the rest of the
      // bytes that we "actually" need, which is computed as bytes in mask but
      // not in log.mask. This is only correct because we know that a failed
      // find also reset the log.mask to 0 (that's part of the find interface).
      void* val = read_ro(tx, addr STM_MASK(mask & ~log.mask));
      REDO_RAW_CLEANUP(val, found, log, mask);
      return val;
  }

  template <class CM>
  void
  NOrecHTO_Generic<CM>::write_ro(STM_WRITE_SIG(tx,addr,val,mask))
  {
	  //pthread_mutex_lock(&tx->mutex);

      // buffer the write, and switch to a writing context
      tx->writesets[tx->tx_last_index].data->insert(WriteSetEntry(STM_WRITE_SET_ENTRY(addr, val, mask)));
      OnFirstWrite(tx, read_rw, write_rw, commit);

	  //printf("write ts: %d %d %d\n", timestamp.val, tx->writesets[tx->tx_first_index].size(), tx->writesets[tx->tx_last_index].size());
	  //pthread_mutex_unlock(&tx->mutex);

  }

  template <class CM>
  void
  NOrecHTO_Generic<CM>::write_rw(STM_WRITE_SIG(tx,addr,val,mask))
  {
	  //pthread_mutex_lock(&tx->mutex);
	  // just buffer the write
      tx->writesets[tx->tx_last_index].data->insert(WriteSetEntry(STM_WRITE_SET_ENTRY(addr, val, mask)));
      //printf("%x %x %d\n", addr, val, tx->commits_requested);
      //pthread_mutex_unlock(&tx->mutex);

  }

  template <class CM>
    void
    NOrecHTO_Generic<CM>::local_write(STM_WRITE_SIG(tx,addr,val,mask))
  {
	  tx->local_writesets[tx->tx_last_index].data->insert(WriteSetEntry(STM_WRITE_SET_ENTRY(addr, *addr, mask)));
      *addr = val;
  }

  template <class CM>
  stm::scope_t*
  NOrecHTO_Generic<CM>::rollback(STM_ROLLBACK_SIG(tx, upper_stack_bound, except, len))
  {
	  tx->abort_required.val = 1;

	  while(tx->alive == stm::ACTIVE){
		  CFENCE;
	  }

      stm::PreRollback(tx);

      // notify CM
      CM::onAbort(tx);

      // Perform writes to the exception object if there were any... taking the
      // branch overhead without concern because we're not worried about
      // rollback overheads.
      //STM_ROLLBACK(tx->writesets[tx->tx_last_index], upper_stack_bound, except, len);
      //pthread_mutex_lock(&tx->mutex);

      for(uintptr_t i = tx->commits_requested.val; i >= tx->commits_done.val; i--){
    	  uintptr_t index = i % TxThread::SPECULATIVE_TXS;

		  tx->read_logs[index]->clear();
		  tx->local_writesets[index].data->writeback();
		  tx->local_writesets[index].data->reset();
		  //ValueListEntry entry(0,0);
		  //while(tx->read_queues[i]->try_dequeue(entry));
    	  tx->writesets[index].data->rollback();
		  tx->writesets[index].data->reset();
      }

      //printf("aborting %d\n", tx->commits_requested);

      tx->commits_requested.val = tx->commits_done.val;

      stm::PostRollback(tx, read_rw, write_rw, commit);

      tx->abort_required.val = 0;
      tx->alive = stm::ACTIVE;
      //CFENCE;

      return tx->scopes[tx->tx_first_index];
  }

  template <class CM>
    void
    NOrecHTO_Generic<CM>::end(STM_COMMIT_SIG(tx,)){
	  while(tx->commits_done.val < tx->commits_requested.val){
		  if(tx->alive == stm::ABORTED){
			  tx->tmabort(tx);
		  }
		  CFENCE;
	  }
  }
} // (anonymous namespace)

// Register NOrecHTO initializer functions. Do this as declaratively as
// possible. Remember that they need to be in the stm:: namespace.
#define FOREACH_NORECHTO(MACRO)                    \
    MACRO(NOrecHTO, HyperAggressiveCM)             \
    MACRO(NOrecHTOHour, HourglassCM)               \
    MACRO(NOrecHTOBackoff, BackoffCM)              \
    MACRO(NOrecHTOHB, HourglassBackoffCM)

#define INIT_NORECHTO(ID, CM)                      \
    template <>                                 \
    void initTM<ID>() {                         \
        NOrecHTO_Generic<CM>::initialize(ID, #ID);     \
    }

namespace stm {
  FOREACH_NORECHTO(INIT_NORECHTO)
}

#undef FOREACH_NORECHTO
#undef INIT_NORECHTO
