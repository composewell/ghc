/* -----------------------------------------------------------------------------
 *
 * (c) The University of Glasgow, 2009
 *
 * Lag/Drag/Void profiling.
 *
 * Do not #include this file directly: #include "Rts.h" instead.
 *
 * To understand the structure of the RTS headers, see the wiki:
 *   https://gitlab.haskell.org/ghc/ghc/wikis/commentary/source-tree/includes
 *
 * ---------------------------------------------------------------------------*/

#pragma once

#if defined(GC_PROFILING)

/* retrieves the LDV word from closure c */
#define LDVW(c)                 (((StgClosure *)(c))->header.prof.hp.ldvw)

/*
 * Stores the creation time for closure c.
 * This macro is called at the very moment of closure creation.
 *
 * NOTE: this initializes LDVW(c) to zero, which ensures that there
 * is no conflict between retainer profiling and LDV profiling,
 * because retainer profiling also expects LDVW(c) to be initialised
 * to zero.
 */

#if defined(CMINUSMINUS)

// XXX need for this case as well.

#else

// XXX Fix the type/header inclusions
//#include "TraverseHeap.h"
//extern StgWord flip;
extern uint64_t flip;

#define LDV_RECORD_CREATE(c)   \
  LDVW((c)) = flip

#endif

#else  /* !PROFILING */

#define LDV_RECORD_CREATE(c)   /* nothing */

#endif /* PROFILING */
