/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2008-2009
 *
 * Event log format
 *
 * The log format is designed to be extensible: old tools should be
 * able to parse (but not necessarily understand all of) new versions
 * of the format, and new tools will be able to understand old log
 * files.
 *
 * The canonical documentation for the event log format and record layouts is
 * the "Eventlog encodings" section of the GHC User's Guide.
 *
 * To add a new event
 * ------------------
 *
 *  - In this file:
 *    - give it a new number, add a new #define EVENT_XXX
 *      below. Do not reuse event ids from deprecated event types.
 *
 *  - In EventLog.c
 *    - add it to the EventDesc array
 *    - emit the event type in initEventLogging()
 *    - emit the new event in postEvent_()
 *    - generate the event itself by calling postEvent() somewhere
 *
 *  - Describe the meaning and encoding of the event in the users guide
 *    (docs/user_guide/eventlog-formats.rst)
 *
 *  - In the Haskell code to parse the event log file:
 *    - add types and code to read the new event
 *
 * -------------------------------------------------------------------------- */

#pragma once

/*
 * Markers for begin/end of the Header.
 */
#define EVENT_HEADER_BEGIN    0x68647262 /* 'h' 'd' 'r' 'b' */
#define EVENT_HEADER_END      0x68647265 /* 'h' 'd' 'r' 'e' */

#define EVENT_DATA_BEGIN      0x64617462 /* 'd' 'a' 't' 'b' */
#define EVENT_DATA_END        0xffff

/*
 * Markers for begin/end of the list of Event Types in the Header.
 * Header, Event Type, Begin = hetb
 * Header, Event Type, End = hete
 */
#define EVENT_HET_BEGIN       0x68657462 /* 'h' 'e' 't' 'b' */
#define EVENT_HET_END         0x68657465 /* 'h' 'e' 't' 'e' */

#define EVENT_ET_BEGIN        0x65746200 /* 'e' 't' 'b' 0 */
#define EVENT_ET_END          0x65746500 /* 'e' 't' 'e' 0 */

/*
 * Types of event
 */
#define EVENT_CREATE_THREAD        0 /* (thread)               */
#define EVENT_RUN_THREAD           1 /* (thread)               */
#define EVENT_STOP_THREAD          2 /* (thread, status, blockinfo) */
#define EVENT_THREAD_RUNNABLE      3 /* (thread)               */
#define EVENT_MIGRATE_THREAD       4 /* (thread, new_cap)      */
/* 5, 6, 7 deprecated */
#define EVENT_THREAD_WAKEUP        8 /* (thread, other_cap)    */
#define EVENT_GC_START             9 /* ()                     */
#define EVENT_GC_END              10 /* ()                     */
#define EVENT_REQUEST_SEQ_GC      11 /* ()                     */
#define EVENT_REQUEST_PAR_GC      12 /* ()                     */
/* 13, 14 deprecated */
#define EVENT_CREATE_SPARK_THREAD 15 /* (spark_thread)         */
#define EVENT_LOG_MSG             16 /* (message ...)          */
/* 17 deprecated */
#define EVENT_BLOCK_MARKER        18 /* (size, end_time, capability) */
#define EVENT_USER_MSG            19 /* (message ...)          */
#define EVENT_GC_IDLE             20 /* () */
#define EVENT_GC_WORK             21 /* () */
#define EVENT_GC_DONE             22 /* () */
/* 23, 24 used by eden */
#define EVENT_CAPSET_CREATE       25 /* (capset, capset_type)  */
#define EVENT_CAPSET_DELETE       26 /* (capset)               */
#define EVENT_CAPSET_ASSIGN_CAP   27 /* (capset, cap)          */
#define EVENT_CAPSET_REMOVE_CAP   28 /* (capset, cap)          */
/* the RTS identifier is in the form of "GHC-version rts_way"  */
#define EVENT_RTS_IDENTIFIER      29 /* (capset, name_version_string) */
/* the vectors in these events are null separated strings             */
#define EVENT_PROGRAM_ARGS        30 /* (capset, commandline_vector)  */
#define EVENT_PROGRAM_ENV         31 /* (capset, environment_vector)  */
#define EVENT_OSPROCESS_PID       32 /* (capset, pid)          */
#define EVENT_OSPROCESS_PPID      33 /* (capset, parent_pid)   */
#define EVENT_SPARK_COUNTERS      34 /* (crt,dud,ovf,cnv,gcd,fiz,rem) */
#define EVENT_SPARK_CREATE        35 /* ()                     */
#define EVENT_SPARK_DUD           36 /* ()                     */
#define EVENT_SPARK_OVERFLOW      37 /* ()                     */
#define EVENT_SPARK_RUN           38 /* ()                     */
#define EVENT_SPARK_STEAL         39 /* (victim_cap)           */
#define EVENT_SPARK_FIZZLE        40 /* ()                     */
#define EVENT_SPARK_GC            41 /* ()                     */
#define EVENT_INTERN_STRING       42 /* (string, id) {not used by ghc} */
#define EVENT_WALL_CLOCK_TIME     43 /* (capset, unix_epoch_seconds, nanoseconds) */
#define EVENT_THREAD_LABEL        44 /* (thread, name_string)  */
#define EVENT_CAP_CREATE          45 /* (cap)                  */
#define EVENT_CAP_DELETE          46 /* (cap)                  */
#define EVENT_CAP_DISABLE         47 /* (cap)                  */
#define EVENT_CAP_ENABLE          48 /* (cap)                  */
#define EVENT_HEAP_ALLOCATED      49 /* (heap_capset, alloc_bytes) */
#define EVENT_HEAP_SIZE           50 /* (heap_capset, size_bytes) */
#define EVENT_HEAP_LIVE           51 /* (heap_capset, live_bytes) */
#define EVENT_HEAP_INFO_GHC       52 /* (heap_capset, n_generations,
                                         max_heap_size, alloc_area_size,
                                         mblock_size, block_size) */
#define EVENT_GC_STATS_GHC        53 /* (heap_capset, generation,
                                         copied_bytes, slop_bytes, frag_bytes,
                                         par_n_threads,
                                         par_max_copied,
                                         par_tot_copied, par_balanced_copied) */
#define EVENT_GC_GLOBAL_SYNC      54 /* ()                     */
#define EVENT_TASK_CREATE         55 /* (taskID, cap, tid)       */
#define EVENT_TASK_MIGRATE        56 /* (taskID, cap, new_cap)   */
#define EVENT_TASK_DELETE         57 /* (taskID)                 */
#define EVENT_USER_MARKER         58 /* (marker_name) */
#define EVENT_HACK_BUG_T9003      59 /* Hack: see trac #9003 */

/* Range 60 - 80 is used by eden for parallel tracing
 * see http://www.mathematik.uni-marburg.de/~eden/
 */

/* Range 100 - 139 is reserved for Mercury. */

/* Range 140 - 159 is reserved for Perf events. */

/* Range 160 - 180 is reserved for cost-centre heap profiling events. */

#define EVENT_HEAP_PROF_BEGIN              160
#define EVENT_HEAP_PROF_COST_CENTRE        161
#define EVENT_HEAP_PROF_SAMPLE_BEGIN       162
#define EVENT_HEAP_PROF_SAMPLE_COST_CENTRE 163
#define EVENT_HEAP_PROF_SAMPLE_STRING      164
#define EVENT_HEAP_PROF_SAMPLE_END         165
#define EVENT_HEAP_BIO_PROF_SAMPLE_BEGIN   166
#define EVENT_PROF_SAMPLE_COST_CENTRE      167
#define EVENT_PROF_BEGIN                   168

#define EVENT_USER_BINARY_MSG              181

#define EVENT_CONC_MARK_BEGIN              200
#define EVENT_CONC_MARK_END                201
#define EVENT_CONC_SYNC_BEGIN              202
#define EVENT_CONC_SYNC_END                203
#define EVENT_CONC_SWEEP_BEGIN             204
#define EVENT_CONC_SWEEP_END               205
#define EVENT_CONC_UPD_REM_SET_FLUSH       206
#define EVENT_NONMOVING_HEAP_CENSUS        207

/* Temporary, custom events
 * We can perhaps add it to perf events range ultimately.
 * POST event must be PRE event+1
 * */
#define EVENT_PRE_THREAD_CLOCK           300
#define EVENT_POST_THREAD_CLOCK          301
#define EVENT_PRE_THREAD_PAGE_FAULTS     302
#define EVENT_POST_THREAD_PAGE_FAULTS    303
#define EVENT_PRE_THREAD_CTX_SWITCHES    304
#define EVENT_POST_THREAD_CTX_SWITCHES   305
#define EVENT_PRE_THREAD_ALLOCATED       306
#define EVENT_POST_THREAD_ALLOCATED      307
#define EVENT_PRE_HW_CACHE_L1I           308
#define EVENT_POST_HW_CACHE_L1I          309
#define EVENT_PRE_HW_CACHE_L1I_MISS      310
#define EVENT_POST_HW_CACHE_L1I_MISS     311
#define EVENT_PRE_HW_CACHE_L1D           312
#define EVENT_POST_HW_CACHE_L1D          313
#define EVENT_PRE_HW_CACHE_L1D_MISS      314
#define EVENT_POST_HW_CACHE_L1D_MISS     315
#define EVENT_PRE_HW_CACHE_MISSES        316
#define EVENT_POST_HW_CACHE_MISSES       317
#define EVENT_PRE_HW_INSTRUCTIONS        318
#define EVENT_POST_HW_INSTRUCTIONS       319
#define EVENT_PRE_HW_BRANCH_MISSES       320
#define EVENT_POST_HW_BRANCH_MISSES      321
#define EVENT_PRE_THREAD_CPU_MIGRATIONS  322
#define EVENT_POST_THREAD_CPU_MIGRATIONS 323
#define EVENT_PRE_PROCESS_CPU_TIME       324
#define EVENT_PRE_FOREIGN_CPU_TIME       325
#define EVENT_PRE_GC_CPU_TIME            326
#define EVENT_PRE_USER_CPU_TIME          327
#define EVENT_PRE_SYSTEM_CPU_TIME        328

/*
 * The highest event code +1 that ghc itself emits. Note that some event
 * ranges higher than this are reserved but not currently emitted by ghc.
 * This must match the size of the EventDesc[] array in EventLog.c
 */
#define NUM_GHC_EVENT_TAGS        329

#if 0  /* DEPRECATED EVENTS: */
/* we don't actually need to record the thread, it's implicit */
#define EVENT_RUN_SPARK            5 /* (thread)               */
#define EVENT_STEAL_SPARK          6 /* (thread, victim_cap)   */
/* shutdown replaced by EVENT_CAP_DELETE */
#define EVENT_SHUTDOWN             7 /* ()                     */
/* ghc changed how it handles sparks so these are no longer applicable */
#define EVENT_CREATE_SPARK        13 /* (cap, thread) */
#define EVENT_SPARK_TO_THREAD     14 /* (cap, thread, spark_thread) */
#define EVENT_STARTUP             17 /* (num_capabilities)     */
/* these are used by eden but are replaced by new alternatives for ghc */
#define EVENT_VERSION             23 /* (version_string) */
#define EVENT_PROGRAM_INVOCATION  24 /* (commandline_string) */
#endif

/*
 * Status values for EVENT_STOP_THREAD
 *
 * 1-5 are the StgRun return values (from includes/Constants.h):
 *
 * #define HeapOverflow   1
 * #define StackOverflow  2
 * #define ThreadYielding 3
 * #define ThreadBlocked  4
 * #define ThreadFinished 5
 * #define ForeignCall                  6
 * #define BlockedOnMVar                7
 * #define BlockedOnBlackHole           8
 * #define BlockedOnRead                9
 * #define BlockedOnWrite               10
 * #define BlockedOnDelay               11
 * #define BlockedOnSTM                 12
 * #define BlockedOnDoProc              13
 * #define BlockedOnCCall               -- not used (see ForeignCall)
 * #define BlockedOnCCall_NoUnblockExc  -- not used (see ForeignCall)
 * #define BlockedOnMsgThrowTo          16
 */
#define THREAD_SUSPENDED_FOREIGN_CALL 6

/*
 * Capset type values for EVENT_CAPSET_CREATE
 */
#define CAPSET_TYPE_CUSTOM      1  /* reserved for end-user applications */
#define CAPSET_TYPE_OSPROCESS   2  /* caps belong to the same OS process */
#define CAPSET_TYPE_CLOCKDOMAIN 3  /* caps share a local clock/time      */

/*
 * Heap profile breakdown types. See EVENT_HEAP_PROF_BEGIN.
 */
typedef enum {
    HEAP_PROF_BREAKDOWN_COST_CENTRE = 0x1,
    HEAP_PROF_BREAKDOWN_MODULE,
    HEAP_PROF_BREAKDOWN_CLOSURE_DESCR,
    HEAP_PROF_BREAKDOWN_TYPE_DESCR,
    HEAP_PROF_BREAKDOWN_RETAINER,
    HEAP_PROF_BREAKDOWN_BIOGRAPHY,
    HEAP_PROF_BREAKDOWN_CLOSURE_TYPE
} HeapProfBreakdown;

#if !defined(EVENTLOG_CONSTANTS_ONLY)

typedef StgWord16 EventTypeNum;
typedef StgWord64 EventTimestamp; /* in nanoseconds */
typedef StgWord32 EventThreadID;
typedef StgWord16 EventCapNo;
typedef StgWord16 EventPayloadSize; /* variable-size events */
typedef StgWord16 EventThreadStatus; /* status for EVENT_STOP_THREAD */
typedef StgWord32 EventCapsetID;
typedef StgWord16 EventCapsetType;   /* types for EVENT_CAPSET_CREATE */
typedef StgWord64 EventTaskId;         /* for EVENT_TASK_* */
typedef StgWord64 EventKernelThreadId; /* for EVENT_TASK_CREATE */

#define EVENT_PAYLOAD_SIZE_MAX STG_WORD16_MAX
#endif
