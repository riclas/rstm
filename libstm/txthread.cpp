/**
 *  Copyright (C) 2011
 *  University of Rochester Department of Computer Science
 *    and
 *  Lehigh University Department of Computer Science and Engineering
 *
 * License: Modified BSD
 *          Please see the file LICENSE.RSTM for licensing information
 */

#include <numa.h>
#include <setjmp.h>
#include <iostream>
#include <stm/txthread.hpp>
#include <stm/lib_globals.hpp>
#include "policies/policies.hpp"
#include "algs/tml_inline.hpp"
#include "algs/algs.hpp"
#include "inst.hpp"

using namespace stm;

namespace
{
  /**
   *  The name of the algorithm with which libstm was initialized
   */
  const char* init_lib_name;

  /**
   *  The default mechanism that libstm uses for an abort. An API environment
   *  may also provide its own abort mechanism (see itm2stm for an example of
   *  how the itm shim does this).
   *
   *  This is ugly because rollback has a configuration-dependent signature.
   */
  NORETURN void
  default_abort_handler(TxThread* tx)
  {
      jmp_buf* scope = (jmp_buf*)TxThread::tmrollback(tx
#if defined(STM_PROTECT_STACK)
                                                , TOP_OF_ARGS(1)
#endif
#if defined(STM_ABORT_ON_THROW)
                                                , NULL, 0
#endif
                                               );
      // need to null out the scope
      longjmp(*scope, 1);
  }
} // (anonymous namespace)

namespace stm
{
  /*** BACKING FOR GLOBAL VARS DECLARED IN TXTHREAD.HPP */
  pad_word_t threadcount          = {0}; // thread count
  cache_line_storage<TxThread*>  threads[MAX_THREADS] = {0}; // all TxThreads
  THREAD_LOCAL_DECL_TYPE(TxThread*) Self; // this thread's TxThread

  int TxThread::numThreads;

  uintptr_t TxThread::SPECULATIVE_TXS;

  uintptr_t TxThread::MAX_SPEC_TXS = 4;

  int TxThread::WORKERS_PER_HELPER;

  /**
   *  Constructor sets up the lists and vars
   */
  TxThread::TxThread(uint32_t id)
      : nesting_depth(0),
        allocator(),
        num_commits(0), num_aborts(0), unique_aborts(0), num_restarts(0),
        num_ro(0), scope(NULL), scopes((scope_t * volatile *)malloc(sizeof(scope_t * volatile)*MAX_SPEC_TXS)),
        start_time(0), start_times((pad_word_t*)malloc(sizeof(pad_word_t)*MAX_SPEC_TXS)), end_time(0), validate_ts(0),
        tmlHasLock(false), undo_log(64), vlist(64), vlist_v((cache_line_storage<ValueList*>*)malloc(sizeof(cache_line_storage<ValueList*>)*MAX_SPEC_TXS)),
        read_logs((wlpdstm::Log<ValueListEntry>**)malloc(sizeof(wlpdstm::Log<ValueListEntry>*)*MAX_SPEC_TXS)), writes(64),
		writesets((cache_line_storage<WriteSet*>*)malloc(sizeof(cache_line_storage<WriteSet*>)*MAX_SPEC_TXS)), local_writesets((cache_line_storage<WriteSet*>*)malloc(sizeof(cache_line_storage<WriteSet*>)*MAX_SPEC_TXS)),
		r_orecs(64), r_orecs_v((wlpdstm::Log<orec_t*>**)malloc(sizeof(wlpdstm::Log<orec_t*>*)*MAX_SPEC_TXS)), locks(64),
        my_lock_v((id_version_t*)malloc(sizeof(id_version_t) * MAX_SPEC_TXS)),
		wf((filter_t*)FILTER_ALLOC(sizeof(filter_t))),
        rf((filter_t*)FILTER_ALLOC(sizeof(filter_t))),
        prio(0), consec_aborts(0), seed((unsigned long)&id), myRRecs(64),
        order(-1), alive(1),
        r_bytelocks(64), w_bytelocks(64), r_bitlocks(64), w_bitlocks(64),
        my_mcslock(new mcs_qnode_t()),
        cm_ts(INT_MAX),
        cf((filter_t*)FILTER_ALLOC(sizeof(filter_t))),
        nanorecs(64), nanorecs_v((NanorecList**)malloc(sizeof(NanorecList*)*MAX_SPEC_TXS)), begin_wait(0), strong_HG(),
		irrevocable(false),
        requires_validation(false),// validated(false), commit_ready(false), commited(false),
		dirty_commit(0), abort_transaction(false), running(true),
		average_time(0), insert_time(0), validation_time(0), average_val(0), reads(0), wait_commit(0), time(0), start(0)
		//start_times((uintptr_t*)calloc(SPECULATIVE_TXS, sizeof(uintptr_t))), last_read_times((uintptr_t*)calloc(SPECULATIVE_TXS, sizeof(uintptr_t)))

  {

      // update the allocator
      allocator.setID(id-1);

      // set up my lock word
      my_lock.fields.lock = 1;
      my_lock.fields.id = id;
//modificar id: id*i
      // clear filters
      wf->clear();
      rf->clear();

      //initialize arrays
      for(uintptr_t i = 0; i < MAX_SPEC_TXS; i++){
    	  scopes[i] = NULL;
    	  start_times[i].val = 0;
    	  vlist_v[i].data = new ValueList(64);
    	  read_logs[i] = new wlpdstm::Log<ValueListEntry>();
    	  writesets[i].data = new WriteSet(64);
    	  local_writesets[i].data = new WriteSet(64);
    	  r_orecs_v[i] = new wlpdstm::Log<orec_t*>();
    	  nanorecs_v[i] = new NanorecList(64);
    	  my_lock_v[i].fields.lock = 1;
    	  my_lock_v[i].fields.id = id*MAX_SPEC_TXS + i;
      }
  }

  /*** print a message and die */
  void UNRECOVERABLE(const char* msg)
  {
      std::cerr << msg << std::endl;
      exit(-1);
  }

  /***  GLOBAL FUNCTION POINTERS FOR OUR INDIRECTION-BASED MODE SWITCHING */

  /**
   *  The begin function pointer.  Note that we need tmbegin to equal
   *  begin_cgl initially, since "0" is the default algorithm
   */
  bool (TM_FASTCALL *volatile TxThread::tmbegin)(TxThread*) = begin_CGL;

  /**
   *  The tmrollback, tmabort, and tmirrevoc pointers
   */
  scope_t* (*TxThread::tmrollback)(STM_ROLLBACK_SIG(,,,));
  NORETURN void (*TxThread::tmabort)(TxThread*) = default_abort_handler;
  bool (*TxThread::tmirrevoc)(STM_IRREVOC_SIG(,)) = NULL;
  //void* (*TxThread::helper)(void*) = NULL;

  /*** the init factory */
  void TxThread::thread_init()
  {
      // multiple inits from one thread do not cause trouble
      if (Self) return;

      	// prevent new txns from starting.
		while (true) {
			int i = curr_policy.ALG_ID;
			if (bcasptr(&tmbegin, stms[i].begin, &begin_blocker))
				break;
			spin64();
		}

		// We need to be very careful here.  Some algorithms (at least TLI and
		// NOrecPrio) like to let a thread look at another thread's TxThread
		// object, even when that other thread is not in a transaction.  We
		// don't want the TxThread object we are making to be visible to
		// anyone, until it is 'ready'.
		//
		// Since those algorithms can only find this TxThread object by looking
		// in threads[], and they scan threads[] by using threadcount.val, we
		// use the following technique:
		//
		// First, only this function can ever change threadcount.val.  It does
		// not need to do so atomically, but it must do so from inside of the
		// critical section created by the begin_blocker CAS
		//
		// Second, we can predict threadcount.val early, but set it late.  Thus
		// we can completely configure this TxThread, and even put it in the
		// threads[] array, without writing threadcount.val.
		//
		// Lastly, when we finally do write threadcount.val, we make sure to
		// preserve ordering so that write comes after initialization, but
		// before lock release.

	      //set worker thread cpu affinity
	      cpu_set_t cpuset;
	      CPU_ZERO(&cpuset);
	      uint32_t cpu = threadcount.val;

	      if(stm::stms[curr_policy.ALG_ID].helperThreads > 0){
	      	  cpu = threadcount.val/WORKERS_PER_HELPER;
	    	  CPU_SET(cpu, &cpuset);
	      } else {
	    	  CPU_SET(cpu, &cpuset);
	      }
	      pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset);

	  nodemask_t mem_bind;
	  nodemask_zero(&mem_bind);
	  nodemask_set_compat(&mem_bind, numa_node_of_cpu(cpu));
	  numa_set_membind_compat(&mem_bind);

      // create a TxThread and save it in the respective NUMA node
	  Self = (TxThread*)numa_alloc_onnode(sizeof(TxThread),numa_node_of_cpu(cpu));

      new(Self) TxThread(threadcount.val + 1);

	  //Self = new TxThread(threadcount.val + 1);

      // configure my TM instrumentation
      install_algorithm_local(curr_policy.ALG_ID, Self);

      // set the pointer to this TxThread
      threads[threadcount.val].data = Self;

      // set the epoch to default
      epochs[threadcount.val].val = EPOCH_MAX;

      // NB: at this point, we could change the mode based on the thread
      //     count.  The best way to do so would be to install ProfileTM.  We
      //     would need to be very careful, though, in case another thread is
      //     already running ProfileTM.  We'd also need a way to skip doing
      //     so if a non-adaptive policy was in place.  An even better
      //     strategy might be to put a request for switching outside the
      //     critical section, as the last line of this method.
      //
      // NB: For the release, we are omitting said code, as it does not
      //     matter in the workloads we provide.  We should revisit at some
      //     later time.

      // now publish threadcount.val
      CFENCE;
      threadcount.val++;

      // now we can let threads progress again
      CFENCE;
      tmbegin = stms[curr_policy.ALG_ID].begin;
  }

  /**
   *  Simplified support for self-abort
   */
  void restart()
  {
      // get the thread's tx context
      TxThread* tx = Self;
      // register this restart
      ++tx->num_restarts;
      // call the abort code
      tx->tmabort(tx);
  }

  void thread_shutdown() {
	  if(Self->tmend)
		  Self->tmend(Self);
  }

  /**
   *  When the transactional system gets shut down, we call this to dump stats
   */
  void sys_shutdown()
    {
        static volatile unsigned int mtx = 0;
        while (!bcas32(&mtx, 0u, 1u)) { }

        uint64_t nontxn_count = 0;                // time outside of txns
        uint32_t pct_ro       = 0;                // read only txn ratio
        uint32_t txn_count    = 0;                // total txns
        uint32_t rw_txns      = 0;                // rw commits
        uint32_t ro_txns      = 0;                // ro commits
        uintptr_t wait_commits = 0;
        uintptr_t total_aborts = 0;
        uintptr_t average_time = 0;
        uintptr_t total_insert_time = 0;
        uintptr_t validation_time = 0;
        uintptr_t total_vals = 0;

        for (uint32_t i = 0; i < threadcount.val; i++) {
        	threads[i].data->running = false;

        	std::cout << "Thread: "       << threads[i].data->id
                      << "; RW Commits: " << threads[i].data->num_commits
                      << "; RO Commits: " << threads[i].data->num_ro
                      << "; Aborts: "     << threads[i].data->num_aborts
                      << "; Unique Aborts: " << threads[i].data->unique_aborts
                      << "; Restarts: "   << threads[i].data->num_restarts
                      << std::endl;
            threads[i].data->abort_hist.dump();
            rw_txns += threads[i].data->num_commits;
            ro_txns += threads[i].data->num_ro;
            nontxn_count += threads[i].data->total_nontxn_time;
            total_aborts+=threads[i].data->num_aborts;
            wait_commits+=threads[i].data->wait_commit;
            average_time+=threads[i].data->average_time;
            total_insert_time+=threads[i].data->insert_time;
            validation_time+=threads[i].data->validation_time;
            total_vals+=threads[i].data->average_val;
            std::cout << "average time: " << threads[i].data->average_time << std::endl;
            //std::cout << "number of validations: " << threads[i].data->average_val << std::endl;
            std::cout << "number of reads: " << threads[i].data->reads << std::endl;
            std::cout << "commits waited: " << threads[i].data->wait_commit << std::endl;
        }

        txn_count = rw_txns + ro_txns;
		pct_ro = (!txn_count) ? 0 : (100 * ro_txns) / txn_count;

		std::cout << "Total num txs:\t" << txn_count << std::endl;
		std::cout << "Total num aborts:\t" << total_aborts << std::endl;

		std::cout << "Total nontxn work:\t" << nontxn_count << std::endl;
		std::cout << "wait time:\t" << average_time - total_insert_time << std::endl;
		std::cout << "wait commits:\t" << wait_commits << std::endl;
		std::cout << "tx time:\t" << average_time << std::endl;
		std::cout << "tx without commit time:\t" << total_insert_time << std::endl;
		std::cout << "validation time:\t" << validation_time << std::endl;
		std::cout << "total validations:\t" << total_vals << std::endl;

      // if we ever switched to ProfileApp, then we should print out the
      // ProfileApp custom output.
      if (app_profiles) {
          uint32_t divisor =
              (curr_policy.ALG_ID == ProfileAppAvg) ? txn_count : 1;
          if (divisor == 0)
              divisor = 0u - 1u; // unsigned infinity :)

          std::cout << "# " << stms[curr_policy.ALG_ID].name << " #" << std::endl;
          std::cout << "# read_ro, read_rw_nonraw, read_rw_raw, write_nonwaw, write_waw, txn_time, "
                    << "pct_txtime, roratio #" << std::endl;
          std::cout << app_profiles->read_ro  / divisor << ", "
                    << app_profiles->read_rw_nonraw / divisor << ", "
                    << app_profiles->read_rw_raw / divisor << ", "
                    << app_profiles->write_nonwaw / divisor << ", "
                    << app_profiles->write_waw / divisor << ", "
                    << app_profiles->txn_time / divisor << ", "
                    << ((100*app_profiles->timecounter)/nontxn_count) << ", "
                    << pct_ro << " #" << std::endl;
      }
      CFENCE;
      mtx = 0;
  }

  /**
   *  for parsing input to determine the valid algorithms for a phase of
   *  execution.
   *
   *  Setting a policy is a lot like changing algorithms, but requires a little
   *  bit of custom synchronization
   */
  void set_policy(const char* phasename)
  {
      // prevent new txns from starting.  Note that we can't be in ProfileTM
      // while doing this
      while (true) {
          int i = curr_policy.ALG_ID;
          if (i == ProfileTM)
              continue;
          if (bcasptr(&TxThread::tmbegin, stms[i].begin, &begin_blocker))
              break;
          spin64();
      }

      // wait for everyone to be out of a transaction (scope == NULL)
      for (unsigned i = 0; i < threadcount.val; ++i)
          while (threads[i].data->scope)
              spin64();

      // figure out the algorithm for the STM, and set the adapt policy

      // we assume that the phase is a single-algorithm phase
      int new_algorithm = stm_name_map(phasename);
      int new_policy = Single;
      if (new_algorithm == -1) {
          int tmp = pol_name_map(phasename);
          if (tmp == -1)
              UNRECOVERABLE("Invalid configuration string");
          new_policy = tmp;
          new_algorithm = pols[tmp].startmode;
      }

      curr_policy.POL_ID = new_policy;
      curr_policy.waitThresh = pols[new_policy].waitThresh;
      curr_policy.abortThresh = pols[new_policy].abortThresh;

      // install the new algorithm
      install_algorithm(new_algorithm, Self);
  }

  /**
   *  Template Metaprogramming trick for initializing all STM algorithms.
   *
   *  This is either a very gross trick, or a very cool one.  We have ALG_MAX
   *  algorithms, and they all need to be initialized.  Each has a unique
   *  identifying integer, and each is initialized by calling an instantiation
   *  of initTM<> with that integer.
   *
   *  Rather than call each function through a line of code, we use a
   *  tail-recursive template: When we call MetaInitializer<0>.init(), it will
   *  recursively call itself for every X, where 0 <= X < ALG_MAX.  Since
   *  MetaInitializer<X>::init() calls initTM<X> before recursing, this
   *  instantiates and calls the appropriate initTM function.  Thus we
   *  correctly call all initialization functions.
   *
   *  Furthermore, since the code is tail-recursive, at -O3 g++ will inline all
   *  the initTM calls right into the sys_init function.  While the code is not
   *  performance critical, it's still nice to avoid the overhead.
   */
  template <int I = 0>
  struct MetaInitializer
  {
      /*** default case: init the Ith tm, then recurse to I+1 */
      static void init()
      {
          initTM<(stm::ALGS)I>();
          MetaInitializer<(stm::ALGS)I+1>::init();
      }
  };
  template <>
  struct MetaInitializer<ALG_MAX>
  {
      /*** termination case: do nothing for ALG_MAX */
      static void init() { }
  };

  /**
   *  Initialize the TM system.
   */
  void sys_init(int numThreads, stm::AbortHandler conflict_abort_handler)
  {
      static volatile uint32_t mtx = 0;

      if (bcas32(&mtx, 0u, 1u)) {
    	  TxThread::numThreads = numThreads;

          //get the number of Workers per Helper
     	  const char* wph = getenv("WPH");
          TxThread::WORKERS_PER_HELPER = wph ? atoi(wph) : 1;
	  if(TxThread::numThreads % TxThread::WORKERS_PER_HELPER)
	      printf("For optimal resource usage the total number of threads should be a multiple of the number of Workers per Helper!\n");

          if(TxThread::WORKERS_PER_HELPER > TxThread::numThreads)
              TxThread::WORKERS_PER_HELPER = TxThread::numThreads;

    	  // manually register all behavior policies that we support.  We do
          // this via tail-recursive template metaprogramming
          MetaInitializer<0>::init();

          // guess a default configuration, then check env for a better option
          const char* cfg = "SwissHT";
          const char* configstring = getenv("STM_CONFIG");
          if (configstring)
              cfg = configstring;
          else
              printf("STM_CONFIG environment variable not found... using %s\n", cfg);
          init_lib_name = cfg;

          //get the number of speculative transactions, if any
          const char* spectxs = getenv("SPEC_TXS");
          TxThread::SPECULATIVE_TXS = spectxs ? atoi(spectxs) : 2;
          if(TxThread::MAX_SPEC_TXS < TxThread::SPECULATIVE_TXS){
        	  TxThread::MAX_SPEC_TXS = TxThread::SPECULATIVE_TXS;
        	  printf("MAX_SPEC_TXS has been updated! This may lead to performance issues.\n");
          }

          // now initialize the the adaptive policies
          pol_init(cfg);

          // this is (for now) how we make sure we have a buffer to hold
          // profiles.  This also specifies how many profiles we do at a time.
          char* spc = getenv("STM_NUMPROFILES");
          if (spc != NULL)
              profile_txns = strtol(spc, 0, 10);
          profiles = (dynprof_t*)malloc(profile_txns * sizeof(dynprof_t));
          for (unsigned i = 0; i < profile_txns; i++)
              profiles[i].clear();

          // Initialize the global abort handler.
          if (conflict_abort_handler)
              TxThread::tmabort = conflict_abort_handler;

          // now set the phase
          set_policy(cfg);

          if(stm::stms[stm_name_map(cfg)].helperThreads > 0){
              pthread_t threadid[stm::stms[stm_name_map(cfg)].helperThreads];

              for(int k=0; k < stm::stms[stm_name_map(cfg)].helperThreads; k++){
            	  pthread_attr_t attr;
					cpu_set_t cpuset;

					pthread_attr_init(&attr);
					CPU_ZERO(&cpuset);
					CPU_SET(k*TxThread::WORKERS_PER_HELPER+4, &cpuset);
					pthread_attr_setaffinity_np(&attr, sizeof(cpuset), &cpuset);

                  pthread_create(&threadid[k], &attr, stm::stms[stm_name_map(cfg)].helper, (void *) (intptr_t) k);
              }
          }

          printf("STM library configured using config == %s and SPEC_TXS=%ld\n", cfg, TxThread::SPECULATIVE_TXS);

          mtx = 2;
      }
      while (mtx != 2) { }
  }

  /**
   *  Return the name of the algorithm with which the library was configured
   */
  const char* get_algname()
  {
      return init_lib_name;
  }

} // namespace stm
