#ifndef _internal_h_INCLUDED
#define _internal_h_INCLUDED

#include "arena.h"
#include "array.h"
#include "assign.h"
#include "averages.h"
#include "check.h"
#include "classify.h"
#include "clause.h"
#include "cover.h"
#include "extend.h"
#include "flags.h"
#include "format.h"
#include "frames.h"
#include "heap.h"
#include "kimits.h"
#include "kissat.h"
#include "literal.h"
#include "mode.h"
#include "options.h"
#include "phases.h"
#include "profile.h"
#include "proof.h"
#include "queue.h"
#include "random.h"
#include "reluctant.h"
#include "rephase.h"
#include "smooth.h"
#include "stack.h"
#include "statistics.h"
#include "value.h"
#include "vector.h"
#include "watch.h"

typedef struct datarank datarank;

struct datarank {
  unsigned data;
  unsigned rank;
};

typedef struct import import;

struct import {
  unsigned lit;
  bool extension;
  bool imported;
  bool eliminated;
};

typedef struct termination termination;

struct termination {
#ifdef COVERAGE
  volatile uint64_t flagged;
#else
  volatile bool flagged;
#endif
  volatile void *state;
  int (*volatile terminate) (void *);
};

// clang-format off

typedef STACK (value) eliminated;
typedef STACK (import) imports;
typedef STACK (datarank) dataranks;
typedef STACK (watch) statches;
typedef STACK (watch *) patches;

// clang-format on

struct kitten;

//For MallobSweep the Kissat solver needs to know about its sweeper
typedef struct sweeper sweeper;


struct kissat {
#if !defined(NDEBUG) || defined(METRICS)
  bool backbone_computing;
#endif
#ifdef LOGGING
  bool compacting;
#endif
  bool extended;
  bool inconsistent;
  bool iterating;
  bool preprocessing;
  bool probing;
#ifndef QUIET
  bool sectioned;
#endif
  bool stable;
#if !defined(NDEBUG) || defined(METRICS)
  bool transitive_reducing;
  bool vivifying;
#endif
  bool warming;
  bool watching;

  bool large_clauses_watched_after_binary_clauses;

  termination termination;

  unsigned vars;
  unsigned size;
  unsigned active;
  unsigned randec;

  ints export;
  ints units;
  imports import;
  extensions extend;
  unsigneds witness;

  assigned *assigned;
  flags *flags;

  mark *marks;

  value *values;
  phases phases;

  eliminated eliminated;
  unsigneds etrail;

  links *links;
  queue queue;

  heap scores;
  double scinc;

  heap schedule;
  double scoreshift;

  unsigned level;
  frames frames;

  unsigned_array trail;
  unsigned *propagate;

  unsigned best_assigned;
  unsigned target_assigned;
  unsigned unflushed;
  unsigned unassigned;

  unsigneds delayed;

#if defined(LOGGING) || !defined(NDEBUG)
  unsigneds resolvent;
#endif
  unsigned resolvent_size;
  unsigned antecedent_size;

  dataranks ranks;

  unsigneds analyzed;
  unsigneds levels;
  unsigneds minimize;
  unsigneds poisoned;
  unsigneds promote;
  unsigneds removable;
  unsigneds shrinkable;

  clause conflict;

  bool clause_satisfied;
  bool clause_shrink;
  bool clause_trivial;

  unsigneds clause;
  unsigneds shadow;

  arena arena;
  vectors vectors;
  reference first_reducible;
  reference last_irredundant;
  watches *watches;

  reference last_learned[4];

  sizes sorter;

  generator random;
  averages averages[2];
  unsigned tier1[2], tier2[2];
  reluctant reluctant;

  bounds bounds;
  classification classification;
  delays delays;
  enabled enabled;
  limited limited;
  limits limits;
  remember last;
  unsigned walked;

  mode mode;

  uint64_t ticks;

  format format;
  char *prefix;

  statches antecedents[2];
  statches gates[2];
  patches xorted[2];
  unsigneds resolvents;
  bool resolve_gate;

  struct kitten *kitten;
#ifdef METRICS
  uint64_t *gate_eliminated;
#else
  bool gate_eliminated;
#endif
  bool sweep_incomplete;
  unsigneds sweep_schedule;

#if !defined(NDEBUG) || !defined(NPROOFS)
  unsigneds added;
  unsigneds removed;
#endif

#if !defined(NDEBUG) || !defined(NPROOFS) || defined(LOGGING)
  ints original;
  size_t offset_of_last_original_clause;
#endif

#ifndef QUIET
  profiles profiles;
#endif

#ifndef NOPTIONS
  options options;
#endif

#ifndef NDEBUG
  checker *checker;
#endif

#ifndef NPROOFS
  proof *proof;

  // Proof logging
  void *proof_log_state;
  void (*on_drup_derivation) (void* state, const int* lits, int nbLits, int glue);
  void (*on_lrup_import)     (void* state, unsigned long id, const int* lits, int nbLits, const unsigned char* sigData);
  void (*on_drup_deletion)   (void* state, const int* lits, int nbLits);
#endif

  // Clause export
  void *consume_clause_state;
  int *consume_clause_buffer;
  unsigned consume_clause_max_size;
  void (*consume_clause) (void *state, int size, int glue);
  unsigned last_glue;

  // Clause import
  void *produce_clause_state;
  void (*produce_clause) (void *state, int **clause, int *size, int *glue, unsigned long *id, unsigned char *sig);
  unsigned long num_conflicts_at_last_import;

  //--------------------------------------------------------------------------------
  // For MallobSweep
  sweeper *sweeper;
  //These flags here are stored on the solver-level, because
  //individual sweeper-structs are discarded after each sweep iteration
  //i.e. there are times when this information is required but not sweeper exists
  volatile int shweep_local_iteration;
  volatile bool shweep_end_iteration_signal;
  volatile bool shweep_end_job_signal;
  double shweep_t0;

  //there exist time-windows inbetween the sweep iterations
  //where no (accessible) sweeper object exists.
  //we track on the solver-level (permanently available)
  //whether such a sweeper exists and is accessible for stealing right now
  volatile bool shweeper_allows_stealing;

  //Export to own Mallob::Kissat object
  int *shweep_export_eq_buffer;
  void (*shweep_export_eq_callback) (void *state);
  void (*shweep_export_unit_callback) (void *state, int lit);

  //Import directly from SweepJob:: and bypass Kissat::
  void (*shweep_import_SweepJob_eq_callback) (void *SweepJobState, int *lit1, int *lit2, int localId);
  void (*shweep_import_SweepJob_unit_callback) (void *SweepJobState, int *lit, int localId);

  void *shweep_mallob_KissatState;
  void *shweep_mallob_SweepJobState;
  void (*shweep_search_work_callback) (void *state, unsigned **work, int *work_size, int local_id);

  void (*shweep_report_finished_iteration_callback) (void *SweepJobState, int localId);

  struct shweep_statistics shweep;     

  //--------------------------------------------------------------------------------

  // Initial variable phases
  signed char *initial_variable_phases;
  int initial_variable_phases_len;

  // Additional statistics
  unsigned long num_imported_external_clauses;
  unsigned long num_discarded_external_clauses;
  unsigned long r_ee,r_ed,r_pb,r_ss,r_sw,r_tr,r_fx,r_ia,r_tl;
  
  struct exportmore_statistics exportmore_statistics; 

  // Preprocessing reporting
  void *report_preprocess_state;
  bool (*begin_report) (void *state, int vars, int cls);
  void (*report_preprocessed_lit) (void *state, int lit);

  statistics statistics;
};

#define VARS (solver->vars)
#define LITS (2 * solver->vars)

#if 0
#define TIEDX (GET_OPTION (focusedtiers) ? 0 : solver->stable)
#define TIER1 (solver->tier1[TIEDX])
#define TIER2 (solver->tier2[TIEDX])
#else
#define TIER1 (solver->tier1[0])
#define TIER2 (solver->tier2[1])
#endif

#define SCORES (&solver->scores)

static inline unsigned kissat_assigned (kissat *solver) {
  assert (VARS >= solver->unassigned);
  return VARS - solver->unassigned;
}

#define all_variables(IDX) \
  unsigned IDX = 0, IDX##_END = solver->vars; \
  IDX != IDX##_END; \
  ++IDX

#define all_literals(LIT) \
  unsigned LIT = 0, LIT##_END = LITS; \
  LIT != LIT##_END; \
  ++LIT

#define all_clauses(C) \
  clause *C = (clause *) BEGIN_STACK (solver->arena), \
         *const C##_END = (clause *) END_STACK (solver->arena), *C##_NEXT; \
  C != C##_END && (C##_NEXT = kissat_next_clause (C), true); \
  C = C##_NEXT

#define capacity_last_learned \
  (sizeof solver->last_learned / sizeof *solver->last_learned)

#define real_end_last_learned (solver->last_learned + capacity_last_learned)

#define really_all_last_learned(REF_PTR) \
  reference *REF_PTR = solver->last_learned, \
            *REF_PTR##_END = real_end_last_learned; \
  REF_PTR != REF_PTR##_END; \
  REF_PTR++

void kissat_reset_last_learned (kissat *solver);

#endif
