/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2001,2019
 * Author: Sungwoo Park, Daniel Gröber
 *
 * Generalised profiling heap traversal.
 *
 * ---------------------------------------------------------------------------*/

#if defined(GC_PROFILING)

#include "PosixSource.h"
#include "Rts.h"
#include "sm/Storage.h"
#include "Printer.h"
#include "Stats.h"

#include "TraverseHeap.h"

/** Note [Profiling heap traversal visited bit]
 *
 * If the RTS is compiled with profiling enabled StgProfHeader can be used by
 * profiling code to store per-heap object information.
 *
 * The generic heap traversal code reserves the least significant bit of the
 * largest members of the 'trav' union to decide whether we've already visited a
 * given closure in the current pass or not. The rest of the field is free to be
 * used by the calling profiler.
 *
 * By doing things this way we implicitly assume that the LSB of the largest
 * field in the 'trav' union is insignificant. This is true at least for the
 * word aligned pointers which the retainer profiler currently stores there and
 * should be maintained by new users of the 'trav' union for example by shifting
 * the real data up by one bit.
 *
 * Since we don't want to have to scan the entire heap a second time just to
 * reset the per-object visitied bit before/after the real traversal we make the
 * interpretation of this bit dependent on the value of a global variable,
 * 'flip'.
 *
 * When the 'trav' bit is equal to the value of 'flip' the closure data is
 * valid otherwise not (see isTravDataValid). We then invert the value of 'flip'
 * on each heap traversal (see traverseWorkStack), in effect marking all
 * closure's data as invalid at once.
 *
 * There are some complications with this approach, namely: static objects and
 * mutable data. There we do just go over all existing objects to reset the bit
 * manually. See 'resetStaticObjectForProfiling' and 'resetMutableObjects'.
 */
StgWord flip = 0;

#define setTravDataToZero(c) \
  (c)->header.prof.hp.trav.lsb = flip

typedef enum {
    // Object with fixed layout. Keeps an information about that
    // element was processed. (stackPos.next.step)
    posTypeStep,
    // Description of the pointers-first heap object. Keeps information
    // about layout. (stackPos.next.ptrs)
    posTypePtrs,
    // Keeps SRT bitmap (stackPos.next.srt)
    posTypeSRT,
    // Keeps a new object that was not inspected yet. Keeps a parent
    // element (stackPos.next.parent)
    posTypeFresh
} nextPosType;

typedef union {
    // fixed layout or layout specified by a field in the closure
    StgWord step;

    // layout.payload
    struct {
        // See StgClosureInfo in InfoTables.h
        StgHalfWord pos;
        StgHalfWord ptrs;
        StgPtr payload;
    } ptrs;

    // SRT
    struct {
        StgClosure *srt;
    } srt;

    // parent of the current closure, used only when posTypeFresh is set
    StgClosure *cp;
} nextPos;

/**
 * Position pointer into a closure. Determines what the next element to return
 * for a stackElement is.
 */
typedef struct {
    nextPosType type;
    nextPos next;
} stackPos;

// XXX Optimize the stack usage
typedef struct {
  size_t total_size;
  size_t filtered_size;
  size_t large_size;
  size_t small_pinned_size;
} traversalStats;

/**
 * An element of the traversal work-stack. Besides the closure itself this also
 * stores it's parent and associated data.
 *
 * When 'info.type == posTypeFresh' a 'stackElement' represents just one
 * closure, namely 'c' and 'cp' being it's parent. Otherwise 'info' specifies an
 * offset into the children of 'c'. This is to support returning a closure's
 * children one-by-one without pushing one element per child onto the stack. See
 * traversePushChildren() and traversePop().
 *
 */
typedef struct stackElement_ {
    stackPos info;
    StgClosure *c;
    stackData data;
    // We traverse all the children of a node before we print the node. We do
    // this so that we can decide to print or not print the node based on
    // whether we are printing any of the children. We may not print any
    // children if they do not pass the filtering criteria, in that case we
    // want to skip printing the node as well.
    //
    // When traversing we keep the aggregate size of all the children of
    // the node in se_subtree_stats. When we start traversing a child we save
    // the parent's se_subtree_stats in se_parent_stats so that we can use
    // se_subtree_stats for the children of the current node.
    traversalStats se_parent_stats;
    traversalStats se_subtree_stats;
    int se_dup_count;
    int se_level;
    bool se_done;
} stackElement;


#if defined(DEBUG)
unsigned int g_traversalDebugLevel = 0;
static inline void debug(const char *s, ...)
{
    va_list ap;

    if(g_traversalDebugLevel == 0)
        return;

    va_start(ap,s);
    vdebugBelch(s, ap);
    va_end(ap);
}
#else
#define debug(...)
#endif

// number of blocks allocated for one stack
#define BLOCKS_IN_STACK 1

/* -----------------------------------------------------------------------------
 * Add a new block group to the stack.
 * Invariants:
 *  currentStack->link == s.
 * -------------------------------------------------------------------------- */
STATIC_INLINE void
newStackBlock( traverseState *ts, bdescr *bd )
{
    ts->currentStack = bd;
    ts->stackTop     = (stackElement *)(bd->start + BLOCK_SIZE_W * bd->blocks);
    ts->stackBottom  = (stackElement *)bd->start;
    ts->stackLimit   = (stackElement *)ts->stackTop;
    bd->free     = (StgPtr)ts->stackLimit;
}

/* -----------------------------------------------------------------------------
 * Return to the previous block group.
 * Invariants:
 *   s->link == currentStack.
 * -------------------------------------------------------------------------- */
STATIC_INLINE void
returnToOldStack( traverseState *ts, bdescr *bd )
{
    ts->currentStack = bd;
    ts->stackTop = (stackElement *)bd->free;
    ts->stackBottom = (stackElement *)bd->start;
    ts->stackLimit = (stackElement *)(bd->start + BLOCK_SIZE_W * bd->blocks);
    bd->free = (StgPtr)ts->stackLimit;
}

/**
 *  Initializes the traversal work-stack.
 */
void
initializeTraverseStack( traverseState *ts )
{
    if (ts->firstStack != NULL) {
        freeChain(ts->firstStack);
    }

    ts->firstStack = allocGroup(BLOCKS_IN_STACK);
    ts->firstStack->link = NULL;
    ts->firstStack->u.back = NULL;

    ts->stackSize = 0;
    ts->maxStackSize = 0;

    newStackBlock(ts, ts->firstStack);
}

/**
 * Frees all the block groups in the traversal works-stack.
 *
 * Invariants:
 *   firstStack != NULL
 */
void
closeTraverseStack( traverseState *ts )
{
    freeChain(ts->firstStack);
    ts->firstStack = NULL;
}

/**
 * Returns the largest stack size encountered during the traversal.
 */
int
getTraverseStackMaxSize(traverseState *ts)
{
    return ts->maxStackSize;
}

/**
 * Returns true if the whole stack is empty.
 **/
STATIC_INLINE bool
isEmptyWorkStack( traverseState *ts )
{
    return (ts->firstStack == ts->currentStack) && ts->stackTop == ts->stackLimit;
}

/**
 * Returns size of stack
 */
W_
traverseWorkStackBlocks(traverseState *ts)
{
    bdescr* bd;
    W_ res = 0;

    for (bd = ts->firstStack; bd != NULL; bd = bd->link)
      res += bd->blocks;

    return res;
}

/**
 * Initializes *info from ptrs and payload.
 *
 * Invariants:
 *
 *   payload[] begins with ptrs pointers followed by non-pointers.
 */
STATIC_INLINE void
init_ptrs( stackPos *info, uint32_t ptrs, StgPtr payload )
{
    info->type              = posTypePtrs;
    info->next.ptrs.pos     = 0;
    info->next.ptrs.ptrs    = ptrs;
    info->next.ptrs.payload = payload;
}

/**
 * Find the next object from *info.
 */
STATIC_INLINE StgClosure *
find_ptrs( stackPos *info )
{
    if (info->next.ptrs.pos < info->next.ptrs.ptrs) {
        return (StgClosure *)info->next.ptrs.payload[info->next.ptrs.pos++];
    } else {
        return NULL;
    }
}

/**
 *  Initializes *info from SRT information stored in *infoTable.
 */
STATIC_INLINE void
init_srt_fun( stackPos *info, const StgFunInfoTable *infoTable )
{
    info->type = posTypeSRT;
    if (infoTable->i.srt) {
        info->next.srt.srt = (StgClosure*)GET_FUN_SRT(infoTable);
    } else {
        info->next.srt.srt = NULL;
    }
}

STATIC_INLINE void
init_srt_thunk( stackPos *info, const StgThunkInfoTable *infoTable )
{
    info->type = posTypeSRT;
    if (infoTable->i.srt) {
        info->next.srt.srt = (StgClosure*)GET_SRT(infoTable);
    } else {
        info->next.srt.srt = NULL;
    }
}

/**
 * Find the next object from *info.
 */
STATIC_INLINE StgClosure *
find_srt( stackPos *info )
{
    StgClosure *c;
    if (info->type == posTypeSRT) {
        c = info->next.srt.srt;
        info->next.srt.srt = NULL;
        return c;
    }

    return NULL;
}

/**
 * Push a set of closures, represented by a single 'stackElement', onto the
 * traversal work-stack.
 */
static void
pushStackElement(traverseState *ts, const stackElement se)
{
    bdescr *nbd;      // Next Block Descriptor
    if (ts->stackTop - 1 < ts->stackBottom) {
        debug("pushStackElement() to the next stack.\n");

        // currentStack->free is updated when the active stack is switched
        // to the next stack.
        ts->currentStack->free = (StgPtr)ts->stackTop;

        if (ts->currentStack->link == NULL) {
            nbd = allocGroup(BLOCKS_IN_STACK);
            nbd->link = NULL;
            nbd->u.back = ts->currentStack;
            ts->currentStack->link = nbd;
        } else
            nbd = ts->currentStack->link;

        newStackBlock(ts, nbd);
    }

    // adjust stackTop (acutal push)
    ts->stackTop--;
    // If the size of stackElement was huge, we would better replace the
    // following statement by either a memcpy() call or a switch statement
    // on the type of the element. Currently, the size of stackElement is
    // small enough (5 words) that this direct assignment seems to be enough.
    *ts->stackTop = se;

    ts->stackSize++;
    if (ts->stackSize > ts->maxStackSize) ts->maxStackSize = ts->stackSize;
    ASSERT(ts->stackSize >= 0);
    debug("stackSize = %d\n", ts->stackSize);
}

static void initTraversalStats (traversalStats *stats) {
    stats->total_size = 0;
    stats->filtered_size = 0;
    stats->large_size = 0;
    stats->small_pinned_size = 0;
}

static bool isClosurePinned (StgClosure *c) {
    StgPtr p = (StgPtr)c;
    bdescr *bd;

    bd = Bdescr(p);
    return ((bd->flags & (BF_PINNED | BF_LARGE | BF_COMPACT)) != 0);
}

static void updateTraversalStats (traversalStats *dst, StgClosure *c, size_t size) {
    dst->total_size += size;
    if (size * sizeof(W_) >= LARGE_OBJECT_THRESHOLD) {
      dst->large_size += size;
    } else {
      if (isClosurePinned (c)) {
        dst->small_pinned_size += size;
      }
    }
}

static traversalStats addTraversalStats (traversalStats *dst, traversalStats *src) {
    traversalStats stats;

    stats.total_size = dst->total_size + src->total_size;
    stats.filtered_size = dst->filtered_size + src->filtered_size;
    stats.large_size = dst->large_size + src->large_size;
    stats.small_pinned_size = dst->small_pinned_size + src->small_pinned_size;

    return stats;
}

static void accTraversalStats (traversalStats *dst, traversalStats *src) {
    dst->total_size += src->total_size;
    dst->filtered_size += src->filtered_size;
    dst->large_size += src->large_size;
    dst->small_pinned_size += src->small_pinned_size;
}

static bool checkTraversalStats (traversalStats *stats) {
    return (stats->total_size == 0 &&
      stats->filtered_size == 0 &&
      stats->large_size == 0 &&
      stats->small_pinned_size == 0);
}

/**
 * Push a single closure onto the traversal work-stack.
 *
 *  cp   - object's parent
 *  c    - closure
 *  data - data associated with closure.
 */
inline void
traversePushClosure(int level, traverseState *ts, StgClosure *c, StgClosure *cp, stackData data) {
    stackElement se;

    se.c = c;
    se.info.next.cp = cp;
    se.data = data;
    se.info.type = posTypeFresh;
    se.se_level = level;
    se.se_done = false;
    initTraversalStats (&se.se_parent_stats);
    initTraversalStats (&se.se_subtree_stats);
    se.se_dup_count = 0;

    pushStackElement(ts, se);
};

/* A dummy frame to indicate that a tree level is done */
static inline void
traversePushDone(StgClosure *c, StgClosure *cp, stackData data, int level,
      traversalStats cur_stats, traverseState *ts) {
    stackElement se;

    se.c = c;
    se.info.next.cp = cp;
    se.data = data;
    se.info.type = 0; // XXX ?
    se.se_level = level;
    se.se_done = true;
    se.se_parent_stats = cur_stats;
    initTraversalStats (&se.se_subtree_stats);
    se.se_dup_count = 0;

    pushStackElement(ts, se);
};

/**
 * traversePushChildren() extracts the first child of 'c' in 'first_child' and
 * conceptually pushes all remaining children of 'c' onto the traversal stack
 * while associating 'data' with the pushed elements to be returned upon poping.
 *
 * If 'c' has no children, 'first_child' is set to NULL and nothing is pushed
 * onto the stack.
 *
 * If 'c' has only one child, 'first_child' is set to that child and nothing is
 * pushed onto the stack.
 *
 * Invariants:
 *
 *  - 'c' is not any of TSO, AP, PAP, AP_STACK, which means that there cannot
 *       be any stack objects.
 *
 * Note: SRTs are considered to be children as well.
 *
 * Note: When pushing onto the stack we only really push one 'stackElement'
 * representing all children onto the stack. See traversePop()
 */
STATIC_INLINE void
traversePushChildren(traverseState *ts, StgClosure *c, StgClosure **first_child)
{
    stackElement *se = ts->stackTop;

    debug("traversePushChildren(): stackTop = 0x%x\n", ts->stackTop);

    ASSERT(get_itbl(c)->type != TSO);
    ASSERT(get_itbl(c)->type != AP_STACK);

    // fill in se.info
    switch (get_itbl(c)->type) {
        // no child, no SRT
    case CONSTR_0_1:
    case CONSTR_0_2:
    case ARR_WORDS:
    case COMPACT_NFDATA:
        *first_child = NULL;
        return;

        // one child (fixed), no SRT
    case MUT_VAR_CLEAN:
    case MUT_VAR_DIRTY:
        *first_child = ((StgMutVar *)c)->var;
        se->se_done = true;
        goto out;

    case THUNK_SELECTOR:
        *first_child = ((StgSelector *)c)->selectee;
        se->se_done = true;
        goto out;
    case BLACKHOLE:
        *first_child = ((StgInd *)c)->indirectee;
        se->se_done = true;
        goto out;
    case CONSTR_1_0:
    case CONSTR_1_1:
        *first_child = c->payload[0];
        se->se_done = true;
        goto out;

        // For CONSTR_2_0 and MVAR, we use se.info.step to record the position
        // of the next child. We do not write a separate initialization code.
        // Also we do not have to initialize info.type;

        // two children (fixed), no SRT
        // need to push a stackElement, but nothing to store in se.info
    case CONSTR_2_0:
        *first_child = c->payload[0];         // return the first pointer
        se->info.type = posTypeStep;
        se->info.next.step = 2;            // 2 = second
        break;

        // three children (fixed), no SRT
        // need to push a stackElement
    case MVAR_CLEAN:
    case MVAR_DIRTY:
        // head must be TSO and the head of a linked list of TSOs.
        // Shoule it be a child? Seems to be yes.
        *first_child = (StgClosure *)((StgMVar *)c)->head;
        se->info.type = posTypeStep;
        se->info.next.step = 2;            // 2 = second
        break;

        // three children (fixed), no SRT
    case WEAK:
        *first_child = ((StgWeak *)c)->key;
        se->info.type = posTypeStep;
        se->info.next.step = 2;
        break;

        // layout.payload.ptrs, no SRT
    case TVAR:
    case CONSTR:
    case CONSTR_NOCAF:
    case PRIM:
    case MUT_PRIM:
    case BCO:
        init_ptrs(&se->info, get_itbl(c)->layout.payload.ptrs,
                  (StgPtr)c->payload);
        *first_child = find_ptrs(&se->info);
        if (*first_child == NULL)
            return;   // no child
        break;

        // StgMutArrPtr.ptrs, no SRT
    case MUT_ARR_PTRS_CLEAN:
    case MUT_ARR_PTRS_DIRTY:
    case MUT_ARR_PTRS_FROZEN_CLEAN:
    case MUT_ARR_PTRS_FROZEN_DIRTY:
        init_ptrs(&se->info, ((StgMutArrPtrs *)c)->ptrs,
                  (StgPtr)(((StgMutArrPtrs *)c)->payload));
        *first_child = find_ptrs(&se->info);
        if (*first_child == NULL)
            return;
        break;

        // StgMutArrPtr.ptrs, no SRT
    case SMALL_MUT_ARR_PTRS_CLEAN:
    case SMALL_MUT_ARR_PTRS_DIRTY:
    case SMALL_MUT_ARR_PTRS_FROZEN_CLEAN:
    case SMALL_MUT_ARR_PTRS_FROZEN_DIRTY:
        init_ptrs(&se->info, ((StgSmallMutArrPtrs *)c)->ptrs,
                  (StgPtr)(((StgSmallMutArrPtrs *)c)->payload));
        *first_child = find_ptrs(&se->info);
        if (*first_child == NULL)
            return;
        break;

    // layout.payload.ptrs, SRT
    case FUN_STATIC:
    case FUN:           // *c is a heap object.
    case FUN_2_0:
        init_ptrs(&se->info, get_itbl(c)->layout.payload.ptrs, (StgPtr)c->payload);
        *first_child = find_ptrs(&se->info);
        if (*first_child == NULL)
            // no child from ptrs, so check SRT
            goto fun_srt_only;
        break;

    case THUNK:
    case THUNK_2_0:
        init_ptrs(&se->info, get_itbl(c)->layout.payload.ptrs,
                  (StgPtr)((StgThunk *)c)->payload);
        *first_child = find_ptrs(&se->info);
        if (*first_child == NULL)
            // no child from ptrs, so check SRT
            goto thunk_srt_only;
        break;

        // 1 fixed child, SRT
    case FUN_1_0:
    case FUN_1_1:
        *first_child = c->payload[0];
        ASSERT(*first_child != NULL);
        init_srt_fun(&se->info, get_fun_itbl(c));
        break;

    case THUNK_1_0:
    case THUNK_1_1:
        *first_child = ((StgThunk *)c)->payload[0];
        ASSERT(*first_child != NULL);
        init_srt_thunk(&se->info, get_thunk_itbl(c));
        break;

    case FUN_0_1:      // *c is a heap object.
    case FUN_0_2:
    fun_srt_only:
        init_srt_fun(&se->info, get_fun_itbl(c));
        *first_child = find_srt(&se->info);
        if (*first_child == NULL)
            return;     // no child
        break;

    // SRT only
    case THUNK_STATIC:
        ASSERT(get_itbl(c)->srt != 0);
        /* fall-thru */
    case THUNK_0_1:
    case THUNK_0_2:
    thunk_srt_only:
        init_srt_thunk(&se->info, get_thunk_itbl(c));
        *first_child = find_srt(&se->info);
        if (*first_child == NULL)
            return;     // no child
        break;

    case TREC_CHUNK:
        *first_child = (StgClosure *)((StgTRecChunk *)c)->prev_chunk;
        se->info.type = posTypeStep;
        se->info.next.step = 0;  // entry no.
        break;

        // cannot appear
    case PAP:
    case AP:
    case AP_STACK:
    case TSO:
    case STACK:
    case IND_STATIC:
        // stack objects
    case UPDATE_FRAME:
    case CATCH_FRAME:
    case UNDERFLOW_FRAME:
    case STOP_FRAME:
    case RET_BCO:
    case RET_SMALL:
    case RET_BIG:
        // invalid objects
    case IND:
    case INVALID_OBJECT:
    default:
        barf("Invalid object *c in push(): %d", get_itbl(c)->type);
        return;
    }

out:
    // se.info.next.cp has to be initialized when type==posTypeFresh. We don't
    // do that here though. So type must be !=posTypeFresh.
    ASSERT(se->info.type != posTypeFresh);
}

/**
 *  popStackElement(): Remove a depleted stackElement from the top of the
 *  traversal work-stack.
 *
 *  Invariants:
 *    stackTop cannot be equal to stackLimit unless the whole stack is
 *    empty, in which case popStackElement() is not allowed.
 */
static void
popStackElement(traverseState *ts) {
    debug("popStackElement(): stackTop = 0x%x\n", ts->stackTop);

    ASSERT(ts->stackTop != ts->stackLimit);
    ASSERT(!isEmptyWorkStack(ts));

    // <= (instead of <) is wrong!
    if (ts->stackTop + 1 < ts->stackLimit) {
        ts->stackTop++;

        ts->stackSize--;
        if (ts->stackSize > ts->maxStackSize) ts->maxStackSize = ts->stackSize;
        ASSERT(ts->stackSize >= 0);
        debug("stackSize = (--) %d\n", ts->stackSize);

        return;
    }

    bdescr *pbd;    // Previous Block Descriptor

    debug("popStackElement() to the previous stack.\n");

    ASSERT(ts->stackTop + 1 == ts->stackLimit);
    ASSERT(ts->stackBottom == (stackElement *)ts->currentStack->start);

    if (ts->firstStack == ts->currentStack) {
        // The stack is completely empty.
        ts->stackTop++;
        ASSERT(ts->stackTop == ts->stackLimit);

        ts->stackSize--;
        if (ts->stackSize > ts->maxStackSize) ts->maxStackSize = ts->stackSize;
        ASSERT(ts->stackSize >= 0);
        debug("stackSize = %d\n", ts->stackSize);

        return;
    }

    // currentStack->free is updated when the active stack is switched back
    // to the previous stack.
    ts->currentStack->free = (StgPtr)ts->stackLimit;

    // find the previous block descriptor
    pbd = ts->currentStack->u.back;
    ASSERT(pbd != NULL);

    returnToOldStack(ts, pbd);

    ts->stackSize--;
    if (ts->stackSize > ts->maxStackSize) ts->maxStackSize = ts->stackSize;
    ASSERT(ts->stackSize >= 0);
    debug("stackSize = %d\n", ts->stackSize);
}

extern FILE *hp_file;
extern size_t getClosureSize(const StgClosure *p);

#define MAX_SPACES 100

static void fillSpaces(char *spaces, int cur_level) {
    int i;

    for (i=0; i < cur_level && i < MAX_SPACES - 1; i++) {
      spaces[i] = ' ';
    }
    spaces[i] = '\0';
}

static bool collapseDuplicates = 1;

// XXX Report maximum, average object size, and histogram
//
// CAUTION: modifies the ts->stackTop->se_dup_count.
static void printNode (bool first_visit, traverseState *ts, stackElement *se,
    int cur_level, traversalStats cur_stats) {

    bool shouldReportRevisit = false;
    if (!first_visit && !shouldReportRevisit) {
        return;
    }

    StgClosure *c_untagged;
    c_untagged = UNTAG_CLOSURE(se->c);
    size_t cl_size;
    char spaces[MAX_SPACES];
    const StgInfoTable *info = get_itbl(c_untagged);
    bool cl_static = false;

    if ((char *)c_untagged < (char *)mblock_address_space.begin) {
      cl_static = true;
    }

    if (!first_visit && cl_static == true) {
      return;
    }

    cl_size = getClosureSize(c_untagged);
    if (collapseDuplicates && !isEmptyWorkStack(ts) && first_visit) {
      stackElement *se1 = ts->stackTop;
      const StgInfoTable *info = get_itbl(c_untagged);
      const StgInfoTable *pinfo = get_itbl(UNTAG_CLOSURE(se1->c));

      if (strcmp(GET_PROF_TYPE(info), GET_PROF_TYPE(pinfo)) == 0
        && strcmp(GET_PROF_DESC(info), GET_PROF_DESC(pinfo)) == 0
        && getClosureSize(UNTAG_CLOSURE(se1->c)) == cl_size) {
        se1->se_dup_count = se1->se_dup_count + se->se_dup_count + 1;
        return;
      }
    }

    // We print the static closure size as 0 because we do not account it.
    if (cl_static == true) {
      cl_size = 0;
    }
    fillSpaces(spaces, cur_level);
    fprintf (hp_file
          , "%s%d %p %s {%s} {%s} {%lu}:"
          , spaces
          , cur_level
          , c_untagged
          , closure_type_names[info->type]
          , GET_PROF_TYPE(info)
          , GET_PROF_DESC(info)
          , (StgWord64) c_untagged->header.prof.ccs);
    if (se->se_dup_count > 0) {
      fprintf (hp_file, " %lu (x%d) [%lu]"
              , cl_size
              , (se->se_dup_count+1)
              , cur_stats.total_size);
    } else {
      fprintf (hp_file, " %lu [%lu]", cl_size, cur_stats.total_size);
    }

    // XXX we can mark COMPACT as well if required.
    if (cur_stats.total_size == cur_stats.large_size) {
      fprintf (hp_file, " LARGE");
    } else if (cur_stats.total_size == cur_stats.small_pinned_size) {
      fprintf (hp_file, " PINNED");
    }

    if (first_visit) {
      fprintf (hp_file, "\n");
    } else {
      fprintf (hp_file, " (revisit)\n");
    }
    return;
}

bool traverseIsFirstVisit(StgClosure *c);

// XXX Frequency of doing the profile should be related to the window size.
// Such that we are checking a window of particular size and in the next check
// we slide past that.
// XXX We can also implement traversing only those objects which were
// created/mutated since the last check, using gcid to identify the
// creation generation. If an object is old it's entire subtree check
// can be avoided.
// XXX We can also implement generational gc at a finer granularity using gcid
// as the generation.
uint64_t gcDiffNewest = 10;
uint64_t gcDiffOldest = 20;
uint64_t gcAbsOldest = 10;
enum ReportType report = GC_WINDOW;
bool isReportVerbose = false;
bool enable_fine_grained_pinned = true;

// In words. Display only objects larger than this.
// uint64_t sizeThreshold = (LARGE_OBJECT_THRESHOLD/sizeof(W_));
uint64_t sizeThreshold = 0;
// When set to false, do not display unpinned blocks, only pinned are
// displayed.
bool enableUnpinned = true;

static const char* stringifyReportType(enum ReportType rep)
{
   switch (rep)
   {
      case GC_SINCE: return "GC_SINCE";
      case GC_WINDOW: return "GC_WINDOW";
      case GC_STATS: return "GC_STATS";
      default: barf ("stringifyReportType: invalid report type\n");
   }
}

static bool filterClosure (StgClosure *c, size_t size) {
    // We increment the stats before heap traversal.
    uint64_t curGC = (uint64_t) getNumGcs() - 1;
    uint64_t gcid = (StgWord64) c->header.prof.ccs;

    if (size < sizeThreshold) {
      return false;
    }

    switch (report) {
      case GC_WINDOW:
        if (gcid < curGC - gcDiffOldest || gcid > curGC - gcDiffNewest) {
          return false;
        }
        break;
      case GC_SINCE:
        if (gcid < gcAbsOldest || gcid > curGC - gcDiffNewest) {
          return false;
        }
        break;
      case GC_STATS: return false;
      default: barf("filterClosure: unhandled report type\n");
    }

    // XXX Reuse the isClosurePinned result from previous test?
    if (enableUnpinned == false && !isClosurePinned(c)) {
      return false;
    }

    return true;
}

/**
 *  Finds the next object to be considered for retainer profiling and store
 *  its pointer to *c.
 *
 *  If the unprocessed object was stored in the stack (posTypeFresh), the
 *  this object is returned as-is. Otherwise Test if the topmost stack
 *  element indicates that more objects are left,
 *  and if so, retrieve the first object and store its pointer to *c. Also,
 *  set *cp and *data appropriately, both of which are stored in the stack
 *  element.  The topmost stack element then is overwritten so as for it to now
 *  denote the next object.
 *
 *  If the topmost stack element indicates no more objects are left, pop
 *  off the stack element until either an object can be retrieved or
 *  the work-stack becomes empty, indicated by true returned by
 *  isEmptyWorkStack(), in which case *c is set to NULL.
 *
 *  Note:
 *
 *    It is okay to call this function even when the work-stack is empty.
 *
 *  cur_stats is always the current subtree size. The size of the tree before
 *  this subtree is stored in se_size. As we come up from a subtree we add the
 *  size to the parent's se_size.
 */
STATIC_INLINE void
traversePop(traverseState *ts, StgClosure **c, StgClosure **cp, stackData *data,
    int *cur_level, traversalStats *cur_stats, stackElement **pse)
{
    stackElement *se;

    debug("traversePop(): stackTop = 0x%x\n", ts->stackTop);

    // Is this the last internal element? If so instead of modifying the current
    // stackElement in place we actually remove it from the stack.
    bool last;

begin:
    last = false;
    do {
        if (isEmptyWorkStack(ts)) {
            *c = NULL;
            return;
        }

        // Invariants: when we come back to the parent node from a child node
        // we need to add the size of the child to the parent.
        //
        // When we start traversing a new child node, the size should be
        // reset to 0.

        // Note: Below every `break`, where the loop condition is true, must be
        // accompanied by a popStackElement() otherwise this is an infinite
        // loop.
        se = ts->stackTop;
        *pse = se;

        if (*cur_level != se->se_level) {
          fprintf (stderr, "cur_level = %d, se_level = %d\n", *cur_level, se->se_level);
          barf ("cur_level != se->se_level\n");
        }

        // This should be before anything else. If a stack frame is marked with
        // se_done, we should not check any of the fields other than level and
        // size.
        if (se->se_done) {
            popStackElement(ts);
            *cur_level = *cur_level - 1 ;
            if (*cur_level < 0) {
              barf ("cur_level < 0\n");
            }

            StgClosure *c_untagged;
            c_untagged = UNTAG_CLOSURE(se->c);
            if ((char *)c_untagged >= (char *)mblock_address_space.begin) {
                size_t cl_size = getClosureSize(c_untagged);
                updateTraversalStats (cur_stats, c_untagged, cl_size);
                if (filterClosure (c_untagged, cl_size)) {
                  cur_stats->filtered_size += cl_size;
                }
            }

            if (cur_stats->filtered_size > 0 || se->se_subtree_stats.filtered_size > 0) {
              printNode (true, ts, se, *cur_level,
                    addTraversalStats(cur_stats, &se->se_subtree_stats));
            }

            // cur_stats is carried forward and aggregated in the parent
            // This is the running total.
            accTraversalStats (cur_stats, &se->se_parent_stats);

            *c = NULL;
            continue;
        }

        // If this is a top-level element, you should pop that out.
        if (se->info.type == posTypeFresh) {
            *cp = se->info.next.cp;
            *c = se->c;
            *data = se->data;
            popStackElement(ts);
            if (!checkTraversalStats(&se->se_parent_stats)) {
              barf ("se_parent_stats != 0 for a fresh node");
            }

            StgClosure *c_untagged;
            c_untagged = UNTAG_CLOSURE(*c);
            bool first_visit = traverseIsFirstVisit(c_untagged);
            if (first_visit) {
              return;
            } else {
              // some top level weak closures get added by stable ptrs
              // list as well as by weak ptr list.
              /*
              const StgInfoTable *info = get_itbl(c_untagged);
              fprintf (stderr, "Skipping already visited: closure %p, flip %lu, level %d, type %s, desc %s\n"
                , c_untagged
                , flip
                , *cur_level
                , GET_PROF_TYPE(info)
                , GET_PROF_DESC(info));
              */
              printNode (false, ts, se, *cur_level,
                    addTraversalStats(cur_stats, &se->se_subtree_stats));
              *c = NULL;
              continue;
            }
        }

        // Note: The first ptr of all of these was already returned as
        // *fist_child in push(), so we always start with the second field.
        switch (get_itbl(se->c)->type) {
            // two children (fixed), no SRT
            // nothing in se.info
        case CONSTR_2_0:
            *c = se->c->payload[1];
            last = true;
            goto out;

            // three children (fixed), no SRT
            // need to push a stackElement
        case MVAR_CLEAN:
        case MVAR_DIRTY:
            if (se->info.next.step == 2) {
                *c = (StgClosure *)((StgMVar *)se->c)->tail;
                se->info.next.step++;             // move to the next step
                // no popStackElement
            } else {
                *c = ((StgMVar *)se->c)->value;
                last = true;
            }
            goto out;

            // three children (fixed), no SRT
        case WEAK:
            if (se->info.next.step == 2) {
                *c = ((StgWeak *)se->c)->value;
                se->info.next.step++;
                // no popStackElement
            } else {
                *c = ((StgWeak *)se->c)->finalizer;
                last = true;
            }
            goto out;

        case TREC_CHUNK: {
            // These are pretty complicated: we have N entries, each
            // of which contains 3 fields that we want to follow.  So
            // we divide the step counter: the 2 low bits indicate
            // which field, and the rest of the bits indicate the
            // entry number (starting from zero).
            TRecEntry *entry;
            uint32_t entry_no = se->info.next.step >> 2;
            uint32_t field_no = se->info.next.step & 3;
            if (entry_no == ((StgTRecChunk *)se->c)->next_entry_idx) {
                *c = NULL;
                // popStackElement(ts);
                se->se_done = true;
                break; // this breaks out of the switch not the loop
            }
            entry = &((StgTRecChunk *)se->c)->entries[entry_no];
            if (field_no == 0) {
                *c = (StgClosure *)entry->tvar;
            } else if (field_no == 1) {
                *c = entry->expected_value;
            } else {
                *c = entry->new_value;
            }
            se->info.next.step++;
            goto out;
        }

        case TVAR:
        case CONSTR:
        case PRIM:
        case MUT_PRIM:
        case BCO:
            // StgMutArrPtr.ptrs, no SRT
        case MUT_ARR_PTRS_CLEAN:
        case MUT_ARR_PTRS_DIRTY:
        case MUT_ARR_PTRS_FROZEN_CLEAN:
        case MUT_ARR_PTRS_FROZEN_DIRTY:
        case SMALL_MUT_ARR_PTRS_CLEAN:
        case SMALL_MUT_ARR_PTRS_DIRTY:
        case SMALL_MUT_ARR_PTRS_FROZEN_CLEAN:
        case SMALL_MUT_ARR_PTRS_FROZEN_DIRTY:
            *c = find_ptrs(&se->info);
            if (*c == NULL) {
                // popStackElement(ts);
                se->se_done = true;
                break; // this breaks out of the switch not the loop
            }
            goto out;

            // layout.payload.ptrs, SRT
        case FUN:         // always a heap object
        case FUN_STATIC:
        case FUN_2_0:
            if (se->info.type == posTypePtrs) {
                *c = find_ptrs(&se->info);
                if (*c != NULL) {
                    goto out;
                }
                init_srt_fun(&se->info, get_fun_itbl(se->c));
            }
            goto do_srt;

        case THUNK:
        case THUNK_2_0:
            if (se->info.type == posTypePtrs) {
                *c = find_ptrs(&se->info);
                if (*c != NULL) {
                    goto out;
                }
                init_srt_thunk(&se->info, get_thunk_itbl(se->c));
            }
            goto do_srt;

            // SRT
        do_srt:
        case THUNK_STATIC:
        case FUN_0_1:
        case FUN_0_2:
        case THUNK_0_1:
        case THUNK_0_2:
        case FUN_1_0:
        case FUN_1_1:
        case THUNK_1_0:
        case THUNK_1_1:
            *c = find_srt(&se->info);
            if(*c == NULL) {
                // popStackElement(ts);
                se->se_done = true;
                break; // this breaks out of the switch not the loop
            }
            goto out;

            // no child (fixed), no SRT
        case CONSTR_0_1:
        case CONSTR_0_2:
        case ARR_WORDS:
            // one child (fixed), no SRT
        case MUT_VAR_CLEAN:
        case MUT_VAR_DIRTY:
        case THUNK_SELECTOR:
        case CONSTR_1_1:
            // cannot appear
        case PAP:
        case AP:
        case AP_STACK:
        case TSO:
        case STACK:
        case IND_STATIC:
        case CONSTR_NOCAF:
            // stack objects
        case UPDATE_FRAME:
        case CATCH_FRAME:
        case UNDERFLOW_FRAME:
        case STOP_FRAME:
        case RET_BCO:
        case RET_SMALL:
        case RET_BIG:
            // invalid objects
        case IND:
        case INVALID_OBJECT:
        default:
            barf("Invalid object *c in traversePop(): %d", get_itbl(se->c)->type);
            return;
        }
    } while (*c == NULL);

out:

    ASSERT(*c != NULL);
    if(last) {
        //popStackElement(ts);
        se->se_done = true;
    }

    StgClosure *c_untagged;
    c_untagged = UNTAG_CLOSURE(*c);
    bool first_visit = traverseIsFirstVisit(c_untagged);
    if (first_visit) {
      *cp = se->c;
      *data = se->data;

      accTraversalStats (&se->se_parent_stats, cur_stats);
      accTraversalStats (&se->se_subtree_stats, cur_stats);
      initTraversalStats (cur_stats);
    } else {
        /*
        const StgInfoTable *info = get_itbl(c_untagged);
        fprintf (stderr, "already visited: closure %p, flip %lu, level %d, type %s, desc %s\n"
          , c_untagged
          , flip
          , *cur_level
          , GET_PROF_TYPE(info)
          , GET_PROF_DESC(info));
        */
        printNode (false, ts, se, *cur_level, addTraversalStats(cur_stats, &se->se_subtree_stats));
        goto begin;
    }

    return;

}

/**
 * Make sure a closure's profiling data is initialized to zero if it does not
 * conform to the current value of the flip bit, returns true in this case.
 *
 * See Note [Profiling heap traversal visited bit].
 */
bool
traverseMaybeInitClosureData(StgClosure *c)
{
    if (!isTravDataValid(c)) {
        setTravDataToZero(c);
        return true;
    }
    return false;
}

bool
traverseIsFirstVisit(StgClosure *c)
{
  // isTravDataValid means trav bit is same as flip bit.
    if (!isTravDataValid(c)) {
        return true;
    }
    return false;
}

/**
 * Call traversePushClosure for each of the closures covered by a large bitmap.
 */
static void
traverseLargeBitmap (int level, traverseState *ts, StgPtr p, StgLargeBitmap *large_bitmap,
                     uint32_t size, StgClosure *c, stackData data)
{
    uint32_t i, b;
    StgWord bitmap;

    b = 0;
    bitmap = large_bitmap->bitmap[b];
    for (i = 0; i < size; ) {
        if ((bitmap & 1) == 0) {
            traversePushClosure(level, ts, (StgClosure *)*p, c, data);
        }
        i++;
        p++;
        if (i % BITS_IN(W_) == 0) {
            b++;
            bitmap = large_bitmap->bitmap[b];
        } else {
            bitmap = bitmap >> 1;
        }
    }
}

STATIC_INLINE StgPtr
traverseSmallBitmap (int level, traverseState *ts, StgPtr p, uint32_t size, StgWord bitmap,
                     StgClosure *c, stackData data)
{
    while (size > 0) {
        if ((bitmap & 1) == 0) {
            traversePushClosure(level, ts, (StgClosure *)*p, c, data);
        }
        p++;
        bitmap = bitmap >> 1;
        size--;
    }
    return p;
}

/**
 *  traversePushStack(ts, cp, data, stackStart, stackEnd) pushes all the objects
 *  in the STG stack-chunk from stackStart to stackEnd onto the traversal
 *  work-stack with 'c' and 'data' being their parent and associated data,
 *  respectively.
 *
 *  Invariants:
 *
 *    *cp is one of the following: TSO, AP_STACK.
 *
 *    stackStart < stackEnd.
 *
 *    If *c is TSO, its state is not ThreadComplete,or ThreadKilled,
 *    which means that its stack is ready to process.
 *
 *  Note:
 *
 *    This code was almost plagiarzied from GC.c! For each pointer,
 *    traversePushClosure() is invoked instead of evacuate().
 */
static void
traversePushStack(int level, traverseState *ts, StgClosure *cp, stackData data,
                  StgPtr stackStart, StgPtr stackEnd)
{
    StgPtr p;
    const StgRetInfoTable *info;
    StgWord bitmap;
    uint32_t size;

    ASSERT(get_itbl(cp)->type == STACK);

    p = stackStart;
    while (p < stackEnd) {
        info = get_ret_itbl((StgClosure *)p);

        switch(info->i.type) {

        case UPDATE_FRAME:
            traversePushClosure(level, ts, ((StgUpdateFrame *)p)->updatee, cp, data);
            p += sizeofW(StgUpdateFrame);
            continue;

        case UNDERFLOW_FRAME:
        case STOP_FRAME:
        case CATCH_FRAME:
        case CATCH_STM_FRAME:
        case CATCH_RETRY_FRAME:
        case ATOMICALLY_FRAME:
        case RET_SMALL:
            bitmap = BITMAP_BITS(info->i.layout.bitmap);
            size   = BITMAP_SIZE(info->i.layout.bitmap);
            p++;
            p = traverseSmallBitmap(level, ts, p, size, bitmap, cp, data);

        follow_srt:
            if (info->i.srt) {
                traversePushClosure(level, ts, GET_SRT(info), cp, data);
            }
            continue;

        case RET_BCO: {
            StgBCO *bco;

            p++;
            traversePushClosure(level, ts, (StgClosure*)*p, cp, data);
            bco = (StgBCO *)*p;
            p++;
            size = BCO_BITMAP_SIZE(bco);
            traverseLargeBitmap(level, ts, p, BCO_BITMAP(bco), size, cp, data);
            p += size;
            continue;
        }

            // large bitmap (> 32 entries, or > 64 on a 64-bit machine)
        case RET_BIG:
            size = GET_LARGE_BITMAP(&info->i)->size;
            p++;
            traverseLargeBitmap(level, ts, p, GET_LARGE_BITMAP(&info->i),
                                size, cp, data);
            p += size;
            // and don't forget to follow the SRT
            goto follow_srt;

        case RET_FUN: {
            StgRetFun *ret_fun = (StgRetFun *)p;
            const StgFunInfoTable *fun_info;

            traversePushClosure(level, ts, ret_fun->fun, cp, data);
            fun_info = get_fun_itbl(UNTAG_CONST_CLOSURE(ret_fun->fun));

            p = (P_)&ret_fun->payload;
            switch (fun_info->f.fun_type) {
            case ARG_GEN:
                bitmap = BITMAP_BITS(fun_info->f.b.bitmap);
                size = BITMAP_SIZE(fun_info->f.b.bitmap);
                p = traverseSmallBitmap(level, ts, p, size, bitmap, cp, data);
                break;
            case ARG_GEN_BIG:
                size = GET_FUN_LARGE_BITMAP(fun_info)->size;
                traverseLargeBitmap(level, ts, p, GET_FUN_LARGE_BITMAP(fun_info),
                                    size, cp, data);
                p += size;
                break;
            default:
                bitmap = BITMAP_BITS(stg_arg_bitmaps[fun_info->f.fun_type]);
                size = BITMAP_SIZE(stg_arg_bitmaps[fun_info->f.fun_type]);
                p = traverseSmallBitmap(level, ts, p, size, bitmap, cp, data);
                break;
            }
            goto follow_srt;
        }

        default:
            barf("Invalid object found in traversePushStack(): %d",
                 (int)(info->i.type));
        }
    }
}

/**
 * Call traversePushClosure for each of the children of a PAP/AP
 */
STATIC_INLINE StgPtr
traversePAP (int level, traverseState *ts,
                    StgClosure *pap,    /* NOT tagged */
                    stackData data,
                    StgClosure *fun,    /* tagged */
                    StgClosure** payload, StgWord n_args)
{
    StgPtr p;
    StgWord bitmap;
    const StgFunInfoTable *fun_info;

    traversePushClosure(level, ts, fun, pap, data);
    fun = UNTAG_CLOSURE(fun);
    fun_info = get_fun_itbl(fun);
    ASSERT(fun_info->i.type != PAP);

    p = (StgPtr)payload;

    switch (fun_info->f.fun_type) {
    case ARG_GEN:
        bitmap = BITMAP_BITS(fun_info->f.b.bitmap);
        p = traverseSmallBitmap(level, ts, p, n_args, bitmap,
                                pap, data);
        break;
    case ARG_GEN_BIG:
        traverseLargeBitmap(level, ts, p, GET_FUN_LARGE_BITMAP(fun_info),
                            n_args, pap, data);
        p += n_args;
        break;
    case ARG_BCO:
        traverseLargeBitmap(level, ts, (StgPtr)payload, BCO_BITMAP(fun),
                            n_args, pap, data);
        p += n_args;
        break;
    default:
        bitmap = BITMAP_BITS(stg_arg_bitmaps[fun_info->f.fun_type]);
        p = traverseSmallBitmap(level, ts, p, n_args, bitmap, pap, data);
        break;
    }
    return p;
}

extern uint32_t numObjectVisited;
extern uint32_t timesAnyObjectVisited;

static void
resetMutableObjects(int cur_level, traversalStats *cur_stats, W_ *mut_words)
{
    uint32_t g, n;
    bdescr *bd;
    StgPtr ml;
    char spaces[MAX_SPACES];

    fillSpaces(spaces, cur_level);

    // The following code resets the 'trav' field of each unvisited mutable
    // object.
    for (g = 0; g < RtsFlags.GcFlags.generations; g++) {
        // NOT true: even G0 has a block on its mutable list
        // ASSERT(g != 0 || (generations[g].mut_list == NULL));

        // Traversing through mut_list is necessary
        // because we can find MUT_VAR objects which have not been
        // visited during heap traversal.
        for (n = 0; n < n_capabilities; n++) {
          for (bd = capabilities[n]->mut_lists[g]; bd != NULL; bd = bd->link) {
            for (ml = bd->start; ml < bd->free; ml++) {
                bool first_visit = traverseMaybeInitClosureData((StgClosure *)*ml);
                timesAnyObjectVisited++;
                // Account the pointer word
                (*mut_words)++;
                if (first_visit) {
                  StgClosure *c_untagged = UNTAG_CLOSURE((StgClosure *)*ml);
                  const StgInfoTable *info = get_itbl(c_untagged);
                  // fprintf (stderr, "----------> mut object missed\n");
                  numObjectVisited++;
                  if ((char *)c_untagged >= (char *)mblock_address_space.begin) {
                      size_t cl_size = getClosureSize(c_untagged);
                      updateTraversalStats (cur_stats, c_untagged, cl_size);
                      if (filterClosure (c_untagged, cl_size)) {
                        cur_stats->filtered_size += cl_size;
                        fprintf (hp_file
                              , "%s%d %p %s {%s} {%s} {%lu}:"
                              , spaces
                              , cur_level
                              , c_untagged
                              , closure_type_names[info->type]
                              , GET_PROF_TYPE(info)
                              , GET_PROF_DESC(info)
                              , (StgWord64) c_untagged->header.prof.ccs);
                        // XXX total_size is accumulated.
                        fprintf (hp_file, " %lu [%lu]", cl_size, cur_stats->total_size);
                      }
                  }
                }
            }
          }
        }
    }
}

static void getMemUsage(void) {
    FILE *file;
    char buffer[100];
    char *filename = "/proc/self/statm";

    file = fopen(filename, "r");
    if (file == NULL) {
        perror("Error opening /proc/self/statm");
        return;
    }

    // XXX VmData and VmStk can be reported separately using /proc/self/stat.
    // Also using the stack start address and current stack pointer we can find
    // the current resident stack size.
    // Foreign memory allocations will show up in C heap in VmRss.
    // Any mmaps by the program will also show up in VmRss.
    // XXX How is VmStk reported in case of multiple threads?
    if (fgets(buffer, sizeof(buffer), file) != NULL) {
        fprintf(hp_file, "VmSize,VmRss,RssFile,VmExe,_,VmData+VmStk,_ (pages):\n\t%s", buffer);
    } else {
        perror("Error reading /proc/self/statm");
    }

    fclose(file);
}

enum parseState {
    findRss,
    findAnon,
    findVmFlags,
    findHeader
};

static void getMemMaps(bool verbose, size_t threshold_rss_kb) {
    FILE *file;
    char buffer[4096];
    char header[4096];
    char *filename = "/proc/self/smaps";
    char *rss = "Rss:";
    size_t rssLen = strlen(rss);
    char *anon = "Anonymous:";
    size_t anonLen = strlen(anon);
    char *vmflags = "VmFlags:";
    size_t vmfLen = strlen(vmflags);
    enum parseState state = findHeader;
    size_t rssKb;
    size_t total_rss = 0;
    size_t total_anon = 0;
    bool print_anon = true;

    file = fopen(filename, "r");
    if (file == NULL) {
        perror("Error opening /proc/self/smaps");
        return;
    }

    // XXX handle error
    // XXX Print in sorted order
    // XXX We are reading line by line, the maps might change while we are
    // reading. For better results we should read the entire file in one go and
    // then process.
    while (fgets(buffer, sizeof(buffer), file)) {
        switch (state) {
            case findHeader:
                strncpy (header, buffer, sizeof(header));
                state = findRss;
                continue;
            case findRss:
                if (strncmp(buffer, rss, rssLen) == 0) {
                    strtok(buffer, " ");
                    rssKb = atoll(strtok(NULL, " "));
                    if (rssKb > 0) {
                        total_rss += rssKb;
                        if (verbose && rssKb >= threshold_rss_kb) {
                            fprintf(hp_file, "%s", header);
                            fprintf(hp_file, "Rss: %lu kB\n", rssKb);
                            print_anon = true;
                        } else {
                            print_anon = false;
                        }
                        state = findAnon;
                    } else {
                        state = findVmFlags;
                    }
                }
                continue;
            case findAnon:
                if (strncmp(buffer, anon, anonLen) == 0) {
                    strtok(buffer, " ");
                    rssKb = atoll(strtok(NULL, " "));
                    total_anon += rssKb;
                    if (print_anon) {
                        fprintf(hp_file, "Anonymous: %lu kB\n", rssKb);
                    }
                    state = findVmFlags;
                }
                continue;
            case findVmFlags:
                if (strncmp(buffer, vmflags, vmfLen) == 0) {
                    state = findHeader;
                }
                continue;
            default: barf ("getMemMpas: illegal state\n");
        }
    }

    fprintf(hp_file, "Total Rss: %lu kB\n", total_rss);
    fprintf(hp_file, " File maps: %lu kB\n", total_rss - total_anon);
    fprintf(hp_file, " Anonymous: %lu kB\n", total_anon);
    fclose(file);
}

/**
 * Traverse all closures on the traversal work-stack, calling 'visit_cb' on each
 * closure. See 'visitClosure_cb' for details. This function flips the 'flip'
 * bit and hence every closure's profiling data will be reset to zero upon
 * visiting. See Note [Profiling heap traversal visited bit].
 */
void
traverseWorkStack(traverseState *ts, visitClosure_cb visit_cb)
{
    // first_child = first child of c
    StgClosure *c, *cp, *first_child;
    stackData data, child_data;
    StgWord typeOfc;
    int cur_level = 0;
    traversalStats cur_stats;
    // XXX these can overflow, we should reset them every time.
    uint32_t any = timesAnyObjectVisited;
    uint32_t total = numObjectVisited;
    // We increment the stats before heap traversal.
    uint64_t curGc = (uint64_t) getNumGcs() - 1;
    stackElement *se;
    bool verbose = isReportVerbose;

    initTraversalStats (&cur_stats);
    // Now we flip the flip bit.
    flip = flip ^ 1;

    // XXX This should be checked by the CLI
    if (gcDiffNewest > gcDiffOldest) {
      gcDiffNewest = gcDiffOldest;
    }
    // XXX Using the profiling header moves the perfectly aligned page size
    // allocations by a few bytes, thus increasing the slop significantly. To
    // avoid that we can use a per megablock bitmap to keep track of the
    // traversed closures in a non-profiling build. Or we can reserve 32-bytes
    // per 4K block in the block descriptor for that purpose, though this could
    // be more expensive to set on allocations, but we can clear it cheaply at
    // the end of traversal, by just walking all the used blocks.
    //
    // XXX record the thread-id of allocator along with gc-id
    // XXX Filter based on thread-id
    //
    // if we are reporting heap profile the GC is forced to be a major
    // GC.
    if(curGc >= gcDiffOldest) {
      fprintf ( hp_file
              , "state: "
                "report %s, dNewest %lu, dOldest %lu, aOldest %lu, "
                "verbose %s, fineGrainedPinnedReporting %s\n"
              , stringifyReportType(report), gcDiffNewest
              , gcDiffOldest, gcAbsOldest
              , verbose ? "true" : "false"
              , enable_fine_grained_pinned ? "true" : "false");

      uint64_t window_lower;
      uint64_t window_upper = curGc - gcDiffNewest;
      if (report == GC_SINCE) {
          window_lower = gcAbsOldest;
      } else {
          window_lower = curGc - gcDiffOldest;
      }
      fprintf (hp_file, "gcids: current {%lu}, window [%lu, %lu]\n"
            , curGc, window_lower, window_upper);

    } else {
      fprintf (hp_file, "gcids: current {%lu}\n" , curGc);
    }
    fprintf(hp_file, "---------Process memory-----------\n");
    getMemMaps(verbose, 256);
    if (verbose) {
        getMemUsage();
    }
    gcStats gcstats = getGCStats(verbose, enable_fine_grained_pinned);
    fprintf(hp_file, "---------Haskell Closure Level Usage-----------\n");
    fprintf (hp_file, "flip: {%lu}\n" , flip);
    /*
    fprintf (hp_file, "Haskell heap base address: {%lx}\n"
          , mblock_address_space.begin);
    */

    // c = Current closure                           (possibly tagged)
    // cp = Current closure's Parent                 (NOT tagged)
    // data = current closures' associated data      (NOT tagged)
    // data_out = data to associate with current closure's children

loop:
    traversePop(ts, &c, &cp, &data, &cur_level, &cur_stats, &se);

    if (c == NULL) {
        W_ mut_words = 0;

        debug("maxStackSize= %d\n", ts->maxStackSize);
        resetMutableObjects(cur_level, &cur_stats, &mut_words);

        fprintf (hp_file, "total visits: {%u}\n", timesAnyObjectVisited - any);
        fprintf (hp_file, "total objects: {%u}\n", numObjectVisited - total);
        fprintf (hp_file, "filtered bytes: %lu (%lu words)\n"
              , cur_stats.filtered_size * sizeof(W_), cur_stats.filtered_size);

        fprintf(hp_file, "---------Real Usage/Used block space-----------\n");
        reportWithUtilWords ("live bytes"
              , gcstats.live_words, cur_stats.total_size + mut_words);
        W_ pinned_size = cur_stats.large_size + cur_stats.small_pinned_size;
        W_ unpinned_size = cur_stats.total_size - pinned_size;
        reportWithUtilWords (" movable"
              , gcstats.regular_words, unpinned_size);
        // XXX There will be some loss due to alignment of pinned
        // data in both large and small allocations (aligned
        // arrays). However, the significant loss is because of dead
        // pinned objects.
        reportWithUtilWords (" pinned"
              , gcstats.large_words
              , pinned_size);
        if (enable_fine_grained_pinned) {
          reportWithUtilWords ("  large"
                , gcstats.large_pinned_words
                , cur_stats.large_size);
          reportWithUtilWords ("  small"
                , gcstats.small_pinned_words
                , cur_stats.small_pinned_size);
        }
        reportWithUtilWords (" mut_lists"
        // XXX get it from gcstats?
              , mut_words
              , mut_words);

        if (verbose) {
          liveDiff(cur_stats.total_size * sizeof(W_));
        }
        if (cur_level != 0) {
          barf("Traversal loop ended at cur_level: %d\n", cur_level);
        }
        return;
    }
inner_loop:
    c = UNTAG_CLOSURE(c);

    // Some closures are added twice on the stack by the initialization code
    // itself.  So we need to take care of that here.
    if ((char *)c >= (char *)mblock_address_space.begin) {
      if (traverseIsFirstVisit(c) == 0) {
        printNode (false, ts, se, cur_level, addTraversalStats(&cur_stats, &se->se_subtree_stats));
        goto loop;
      }
    }

    typeOfc = get_itbl(c)->type;

    // special cases
    switch (typeOfc) {
    case TSO:
        if (((StgTSO *)c)->what_next == ThreadComplete ||
            ((StgTSO *)c)->what_next == ThreadKilled) {
            debug("ThreadComplete or ThreadKilled encountered in traverseWorkStack()\n");
            goto loop;
        }
        break;

    case IND_STATIC:
        cur_level = cur_level + 1;
        traversePushDone(c, NULL, child_data, cur_level, cur_stats, ts);
        initTraversalStats (&cur_stats);

        // We just skip IND_STATIC, so it's never visited.
        c = ((StgIndStatic *)c)->indirectee;
        bool first_visit1 = traverseIsFirstVisit(UNTAG_CLOSURE(c));
        if (first_visit1) {
          goto inner_loop;
        } else {
          printNode (false, ts, se, cur_level, addTraversalStats(&cur_stats, &se->se_subtree_stats));
          goto loop;
        }

    case CONSTR_NOCAF:
        // static objects with no pointers out, so goto loop.

        // It is not just enough not to visit *c; it is
        // mandatory because CONSTR_NOCAF are not reachable from
        // scavenged_static_objects, the list from which is assumed to traverse
        // all static objects after major garbage collections.
        goto loop;

    case THUNK_STATIC:
        if (get_itbl(c)->srt == 0) {
            // No need to visit *c; no dynamic objects are reachable from it.
            //
            // Static objects: if we traverse all the live closures,
            // including static closures, during each heap census then
            // we will observe that some static closures appear and
            // disappear.  eg. a closure may contain a pointer to a
            // static function 'f' which is not otherwise reachable
            // (it doesn't indirectly point to any CAFs, so it doesn't
            // appear in any SRTs), so we would find 'f' during
            // traversal.  However on the next sweep there may be no
            // closures pointing to 'f'.
            //
            // We must therefore ignore static closures whose SRT is
            // empty, because these are exactly the closures that may
            // "appear".  A closure with a non-empty SRT, and which is
            // still required, will always be reachable.
            //
            // But what about CONSTR?  Surely these may be able
            // to appear, and they don't have SRTs, so we can't
            // check.  So for now, we're calling
            // resetStaticObjectForProfiling() from the
            // garbage collector to reset the retainer sets in all the
            // reachable static objects.
            goto loop;
        }
        /* fall-thru */

    case FUN_STATIC: {
        const StgInfoTable *info = get_itbl(c);
        if (info->srt == 0 && info->layout.payload.ptrs == 0) {
            goto loop;
        } else {
            break;
        }
    }

    default:
        break;
    }

    // If this is the first visit to c, initialize its data.
    bool first_visit = traverseMaybeInitClosureData(c);
    bool traverse_children
        = visit_cb(c, cp, data, first_visit, (stackData*)&child_data);
    cur_level = cur_level + 1;
    traversePushDone (c, cp, child_data, cur_level, cur_stats, ts);
    initTraversalStats (&cur_stats);
    if(!traverse_children) {
        goto loop;
    }

    // process child

    // Special case closures: we process these all in one go rather
    // than attempting to save the current position, because doing so
    // would be hard.
    switch (typeOfc) {
    case STACK:
        // XXX ensure there is at least one actual frame between stackStart and
        // stackEnd.
        traversePushStack(cur_level, ts, c, child_data,
                    ((StgStack *)c)->sp,
                    ((StgStack *)c)->stack + ((StgStack *)c)->stack_size);
        goto loop;

    case TSO:
    {
        StgTSO *tso = (StgTSO *)c;

        traversePushClosure(cur_level, ts, (StgClosure *) tso->stackobj, c, child_data);
        traversePushClosure(cur_level, ts, (StgClosure *) tso->blocked_exceptions, c, child_data);
        traversePushClosure(cur_level, ts, (StgClosure *) tso->bq, c, child_data);
        traversePushClosure(cur_level, ts, (StgClosure *) tso->trec, c, child_data);
        if (   tso->why_blocked == BlockedOnMVar
               || tso->why_blocked == BlockedOnMVarRead
               || tso->why_blocked == BlockedOnBlackHole
               || tso->why_blocked == BlockedOnMsgThrowTo
            ) {
            traversePushClosure(cur_level, ts, tso->block_info.closure, c, child_data);
        }
        goto loop;
    }

    case BLOCKING_QUEUE:
    {
        StgBlockingQueue *bq = (StgBlockingQueue *)c;
        traversePushClosure(cur_level, ts, (StgClosure *) bq->link,  c, child_data);
        traversePushClosure(cur_level, ts, (StgClosure *) bq->bh,    c, child_data);
        traversePushClosure(cur_level, ts, (StgClosure *) bq->owner, c, child_data);
        goto loop;
    }

    case PAP:
    {
        StgPAP *pap = (StgPAP *)c;
        traversePAP(cur_level, ts, c, child_data, pap->fun, pap->payload, pap->n_args);
        goto loop;
    }

    case AP:
    {
        StgAP *ap = (StgAP *)c;
        traversePAP(cur_level, ts, c, child_data, ap->fun, ap->payload, ap->n_args);
        goto loop;
    }

    case AP_STACK:
        traversePushClosure(cur_level, ts, ((StgAP_STACK *)c)->fun, c, child_data);
        traversePushStack(cur_level, ts, c, child_data,
                    (StgPtr)((StgAP_STACK *)c)->payload,
                    (StgPtr)((StgAP_STACK *)c)->payload +
                             ((StgAP_STACK *)c)->size);
        goto loop;
    }

    ts->stackTop->se_done = false;
    traversePushChildren(ts, c, &first_child);

    // If first_child is null, c has no child.
    // If first_child is not null, the top stack element points to the next
    // object. traversePushChildren() may or may not push a stackElement on the
    // stack.
    if (first_child == NULL) {
        ts->stackTop->se_done = true;
        goto loop;
    }

    // We have already pushed the stack entry in traversePushChildren
    // (c, cp, data) = (first_child, c, child_data)
    data = child_data;
    cp = c;
    c = first_child;

    goto inner_loop;
}

/**
 *  Traverse all static objects for which we compute retainer sets,
 *  and reset their rs fields to NULL, which is accomplished by
 *  invoking traverseMaybeInitClosureData(). This function must be called
 *  before zeroing all objects reachable from scavenged_static_objects
 *  in the case of major garbage collections. See GarbageCollect() in
 *  GC.c.
 *  Note:
 *    The mut_once_list of the oldest generation must also be traversed?
 *    Why? Because if the evacuation of an object pointed to by a static
 *    indirection object fails, it is put back to the mut_once_list of
 *    the oldest generation.
 *    However, this is not necessary because any static indirection objects
 *    are just traversed through to reach dynamic objects. In other words,
 *    they are not taken into consideration in computing retainer sets.
 *
 * SDM (20/7/2011): I don't think this is doing anything sensible,
 * because it happens before retainerProfile() and at the beginning of
 * retainerProfil() we change the sense of 'flip'.  So all of the
 * calls to traverseMaybeInitClosureData() here are initialising retainer sets
 * with the wrong flip.  Also, I don't see why this is necessary.  I
 * added a traverseMaybeInitClosureData() call to retainRoot(), and that seems
 * to have fixed the assertion failure in retainerSetOf() I was
 * encountering.
 */
void
resetStaticObjectForProfiling( StgClosure *static_objects )
{
    uint32_t count = 0;
    StgClosure *p;

    p = static_objects;
    while (p != END_OF_STATIC_OBJECT_LIST) {
        p = UNTAG_STATIC_LIST_PTR(p);
        count++;

        switch (get_itbl(p)->type) {
        case IND_STATIC:
            // Since we do not compute the retainer set of any
            // IND_STATIC object, we don't have to reset its retainer
            // field.
            p = (StgClosure*)*IND_STATIC_LINK(p);
            break;
        case THUNK_STATIC:
            traverseMaybeInitClosureData(p);
            p = (StgClosure*)*THUNK_STATIC_LINK(p);
            break;
        case FUN_STATIC:
        case CONSTR:
        case CONSTR_1_0:
        case CONSTR_2_0:
        case CONSTR_1_1:
        case CONSTR_NOCAF:
            traverseMaybeInitClosureData(p);
            p = (StgClosure*)*STATIC_LINK(get_itbl(p), p);
            break;
        default:
            barf("resetStaticObjectForProfiling: %p (%lu)",
                 p, (unsigned long)get_itbl(p)->type);
            break;
        }
    }

    debug("count in scavenged_static_objects = %d\n", count);
}

#endif /* PROFILING */
