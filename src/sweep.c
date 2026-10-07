#include "sweep.h"
#include "dense.h"
#include "inline.h"
#include "kitten.h"
#include "logging.h"
#include "print.h"
#include "promote.h"
#include "propdense.h"
#include "proprobe.h"
#include "random.h"
#include "rank.h"
#include "report.h"
#include "terminate.h"

#include "import.h"
#include <inttypes.h>
#include <string.h>

//New includes for MallobSweep
#include "clauseexport.h"  //export things
#include "resources.h"     //to get wallclock time
#include "substitute.h"    //scheduled after every MallobSweep iteration
#include "congruence.h"    //scheduled at the start of MallobSweep
#include "propinitially.h" //scheduled at the start of MallobSweep

#include <sys/stat.h>
#include <unistd.h>

const int V0_CRIT_SWEEP = 0;
const int V1_INFO_SWEEP = 1;
const int V2_VERB_SWEEP = 2;
const int V3_VVERB_SWEEP = 3;
const int V4_UVERB_SWEEP = 4;
const int V5_XVERB_SWEEP = 5;

const int INVALID_ELIT=INT32_MAX;

struct sweeper {
  kissat *solver;
  unsigned *depths;
  unsigned *reprs;
  unsigned *next, *prev;
  unsigned first, last;
  unsigned encoded;
  unsigned save;
  unsigneds vars;
  references refs;
  unsigneds clause;
  unsigneds backbone;
  unsigneds partition;
  unsigneds core[2];
  struct {
    uint64_t ticks;
    unsigned clauses, depth, vars;
  } limit;

  //For MallobSweep
  unsigned *work;     //The Worklist of this sweeper
  unsigneds RESWEEP;  //Recent equivalences for re-sweeping (deactivated by default, though)
  int work_end;
  int work_head;
  int max_work_after_steal;
  int rank;
  int localId;
  volatile bool somebody_is_stealing_from_me;
};

typedef struct sweeper sweeper;

static int sweep_solve (sweeper *sweeper) {
  kissat *solver = sweeper->solver;
  kitten *kitten = solver->kitten;
  kitten_randomize_phases (kitten);
  INC (sweep_solved);
  int res = kitten_solve (kitten);
  if (res == 10)
    INC (sweep_sat);
  if (res == 20)
    INC (sweep_unsat);
  return res;
}

static void set_kitten_ticks_limit (sweeper *sweeper) {
  uint64_t remaining = 0;
  kissat *solver = sweeper->solver;
  if (solver->statistics.kitten_ticks < sweeper->limit.ticks)
    remaining = sweeper->limit.ticks - solver->statistics.kitten_ticks;
  LOG ("'kitten_ticks' remaining %" PRIu64, remaining);
  kitten_set_ticks_limit (solver->kitten, remaining);
}

static bool kitten_ticks_limit_hit (sweeper *sweeper, const char *when) {
  kissat *solver = sweeper->solver;
  if (solver->statistics.kitten_ticks >= sweeper->limit.ticks) {
    LOG ("'kitten_ticks' limit of %" PRIu64 " ticks hit after %" PRIu64
         " ticks during %s",
         sweeper->limit.ticks, solver->statistics.kitten_ticks, when);
    return true;
  }
#ifndef LOGGING
  (void) when;
#endif
  return false;
}

static void init_sweeper (kissat *solver, sweeper *sweeper) {
  //For MallobSweep, the solver must also know its sweeper
  solver->sweeper = sweeper;
  sweeper->solver = solver;
  sweeper->encoded = 0;
  CALLOC (sweeper->depths, VARS);
  NALLOC (sweeper->reprs, LITS);
  for (all_literals (lit))
    sweeper->reprs[lit] = lit;
  NALLOC (sweeper->prev, VARS);
  memset (sweeper->prev, 0xff, VARS * sizeof *sweeper->prev);
  NALLOC (sweeper->next, VARS);
  memset (sweeper->next, 0xff, VARS * sizeof *sweeper->next);
#ifndef NDEBUG
  for (all_variables (idx))
    assert (sweeper->prev[idx] == INVALID_IDX);
  for (all_variables (idx))
    assert (sweeper->next[idx] == INVALID_IDX);
#endif
  sweeper->first = sweeper->last = INVALID_IDX;
  INIT_STACK (sweeper->vars);
  INIT_STACK (sweeper->refs);
  INIT_STACK (sweeper->clause);
  INIT_STACK (sweeper->backbone);
  INIT_STACK (sweeper->partition);
  INIT_STACK (sweeper->core[0]);
  INIT_STACK (sweeper->core[1]);
  assert (!solver->kitten);
  solver->kitten = kitten_embedded (solver);
  kitten_track_antecedents (solver->kitten);
  kissat_enter_dense_mode (solver, 0);
  kissat_connect_irredundant_large_clauses (solver);

  unsigned completed = solver->statistics.sweep_completed;
  const unsigned max_completed = 32;
  if (completed > max_completed)
    completed = max_completed;

  uint64_t vars_limit = GET_OPTION (sweepvars);
  vars_limit <<= completed;
  const unsigned max_vars_limit = GET_OPTION (sweepmaxvars);
  if (vars_limit > max_vars_limit)
    vars_limit = max_vars_limit;
  sweeper->limit.vars = vars_limit;
  kissat_extremely_verbose (solver, "sweeper variable limit %u",
                            sweeper->limit.vars);

  uint64_t depth_limit = solver->statistics.sweep_completed;
  depth_limit += GET_OPTION (sweepdepth);
  const unsigned max_depth = GET_OPTION (sweepmaxdepth);
  if (depth_limit > max_depth)
    depth_limit = max_depth;
  sweeper->limit.depth = depth_limit;
  kissat_extremely_verbose (solver, "sweeper depth limit %u",
                            sweeper->limit.depth);

  uint64_t clause_limit = GET_OPTION (sweepclauses);
  clause_limit <<= completed;
  const unsigned max_clause_limit = GET_OPTION (sweepmaxclauses);
  if (clause_limit > max_clause_limit)
    clause_limit = max_clause_limit;
  sweeper->limit.clauses = clause_limit;
  kissat_extremely_verbose (solver, "sweeper clause limit %u",
                            sweeper->limit.clauses);

  if (GET_OPTION (sweepcomplete)) {
    sweeper->limit.ticks = UINT64_MAX;
    kissat_extremely_verbose (solver, "unlimited sweeper ticks limit");
  } else {
    SET_EFFORT_LIMIT (ticks_limit, sweep, kitten_ticks);
    sweeper->limit.ticks = ticks_limit;
  }
  set_kitten_ticks_limit (sweeper);

  if (GET_OPTION (mallob_sweeping) || GET_OPTION (puresweep)) {
    solver->shweep.env_limit_vars    = sweeper->limit.vars;
    solver->shweep.env_limit_depth   = sweeper->limit.depth;
    solver->shweep.env_limit_clauses = sweeper->limit.clauses;
    kissat_custom_message(solver, V3_VVERB_SWEEP, "sweeper (compl %i) variables %u", completed, sweeper->limit.vars);
    kissat_custom_message(solver, V3_VVERB_SWEEP, "sweeper (compl %i) depth     %u", completed, sweeper->limit.depth);
    kissat_custom_message(solver, V3_VVERB_SWEEP, "sweeper (compl %i) clauses   %u", completed, sweeper->limit.clauses);
  }

  if (GET_OPTION (mallob_sweeping)) {
    INIT_STACK (sweeper->RESWEEP);
    //These two counters track the progress on the worklist.
    //The worklist itself (sweeper->work) is NOT created here,
    //instead it is allocated and managed externally by Mallob in C++,
    //and we only operate on it and trust that it remains allocated for us
    sweeper->work_head=0;
    sweeper->work_end=0;
    sweeper->rank = GET_OPTION (mallob_rank);
    sweeper->localId = GET_OPTION (mallob_local_id);
    sweeper->max_work_after_steal=0;
    sweeper->somebody_is_stealing_from_me=false;
    //After all other safeguards have been declared, now we can allow stealing
    //(especially relevant that we have work_head = 0 and work_end = 0)
    solver->shweeper_allows_stealing = true;
  }
}

static unsigned release_sweeper (sweeper *sweeper) {
  kissat *solver = sweeper->solver;

  unsigned merged = 0;
  for (all_variables (idx)) {
    if (!ACTIVE (idx))
      continue;
    const unsigned lit = LIT (idx);
    if (sweeper->reprs[lit] != lit)
      merged++;
  }
  DEALLOC (sweeper->depths, VARS);
  DEALLOC (sweeper->reprs, LITS);
  DEALLOC (sweeper->prev, VARS);
  DEALLOC (sweeper->next, VARS);
  RELEASE_STACK (sweeper->vars);
  RELEASE_STACK (sweeper->refs);
  RELEASE_STACK (sweeper->clause);
  RELEASE_STACK (sweeper->backbone);
  RELEASE_STACK (sweeper->partition);
  RELEASE_STACK (sweeper->core[0]);
  RELEASE_STACK (sweeper->core[1]);
  kitten_release (solver->kitten);
  solver->kitten = 0;
  kissat_resume_sparse_mode (solver, false, 0);
  if (GET_OPTION (mallob_sweeping)) {
    RELEASE_STACK (sweeper->RESWEEP);
    solver->sweeper = 0;
    kissat_custom_message(solver,V1_INFO_SWEEP, "release sweeper");
  }
  return merged;
}

static void clear_sweeper (sweeper *sweeper) {
  kissat *solver = sweeper->solver;
  LOG ("clearing sweeping environment");
  kitten_clear (solver->kitten);
  kitten_track_antecedents (solver->kitten);
  for (all_stack (unsigned, idx, sweeper->vars)) {
    assert (sweeper->depths[idx]);
    sweeper->depths[idx] = 0;
  }
  CLEAR_STACK (sweeper->vars);
  for (all_stack (reference, ref, sweeper->refs)) {
    clause *c = kissat_dereference_clause (solver, ref);
    assert (c->swept);
    c->swept = false;
  }
  CLEAR_STACK (sweeper->refs);
  CLEAR_STACK (sweeper->backbone);
  CLEAR_STACK (sweeper->partition);
  sweeper->encoded = 0;
  set_kitten_ticks_limit (sweeper);
}

static unsigned sweep_repr (sweeper *sweeper, unsigned lit) {
  unsigned res;
  {
    unsigned prev = lit;
    while ((res = sweeper->reprs[prev]) != prev)
      prev = res;
  }
  if (res == lit)
    return res;
#if defined(LOGGING) || !defined(NDEBUG)
  kissat *solver = sweeper->solver;
#endif
  LOG ("sweeping repr[%s] = %s", LOGLIT (lit), LOGLIT (res));
  {
    const unsigned not_res = NOT (res);
    unsigned next, prev = lit;
    ;
    while ((next = sweeper->reprs[prev]) != res) {
      const unsigned not_prev = NOT (prev);
      sweeper->reprs[not_prev] = not_res;
      sweeper->reprs[prev] = res;
      prev = next;
    }
    assert (sweeper->reprs[NOT (prev)] == not_res);
  }
  return res;
}

static void add_literal_to_environment (sweeper *sweeper, unsigned depth,
                                        unsigned lit) {
  const unsigned repr = sweep_repr (sweeper, lit);
  if (repr != lit)
    return;
  kissat *solver = sweeper->solver;
  const unsigned idx = IDX (lit);
  if (sweeper->depths[idx])
    return;
  assert (depth < UINT_MAX);
  sweeper->depths[idx] = depth + 1;
  PUSH_STACK (sweeper->vars, idx);
  LOG ("sweeping[%u] adding literal %s", depth, LOGLIT (lit));
}

static void sweep_clause (sweeper *sweeper, unsigned depth) {
  kissat *solver = sweeper->solver;
  assert (SIZE_STACK (sweeper->clause) > 1);
  for (all_stack (unsigned, lit, sweeper->clause))
    add_literal_to_environment (sweeper, depth, lit);
  kitten_clause (solver->kitten, SIZE_STACK (sweeper->clause),
                 BEGIN_STACK (sweeper->clause));
  CLEAR_STACK (sweeper->clause);
  sweeper->encoded++;
}

static void sweep_binary (sweeper *sweeper, unsigned depth, unsigned lit,
                          unsigned other) {
  if (sweep_repr (sweeper, lit) != lit)
    return;
  if (sweep_repr (sweeper, other) != other)
    return;
  kissat *solver = sweeper->solver;
  LOGBINARY (lit, other, "sweeping[%u]", depth);
  value *values = solver->values;

  //(@1): When running in MallobSweep, it can happen that the binary (lit, other)
  //that we want to add to the environment turns out to be a unit that has not been detected yet.
  //This can be caused by unit/equivalence imports which somehow sidestep
  //some earlier detections. We cannot continue at this point with
  //the normal flow of this method because an assertion would trigger.
  //Our solution is to conservatively skip this binary entirely, i.e.
  //not adding it to the sweeping environment. This is sound, since we
  //make the environment weaker than it could be, the only
  //downside is that we now might miss some equivalence detections in that environment.
  if (GET_OPTION (mallob_sweeping) && values[lit]!=0) {
    solver->shweep.stumbled_units++;
    return;
  }

  assert (!values[lit]);
  const value other_value = values[other];
  if (other_value > 0) {
    LOGBINARY (lit, other, "skipping satisfied");
    return;
  }
  const unsigned *depths = sweeper->depths;
  const unsigned other_idx = IDX (other);
  const unsigned other_depth = depths[other_idx];
  const unsigned lit_idx = IDX (lit);
  const unsigned lit_depth = depths[lit_idx];
  if (other_depth && other_depth < lit_depth) {
    LOGBINARY (lit, other, "skipping depth %u copied", other_depth);
    return;
  }
  //Analog MallobSweep edgecase as above (@1), now for the other literal in the binary clause
  if (GET_OPTION (mallob_sweeping) && other_value!=0) {
    solver->shweep.stumbled_units++;
    return;
  }
  assert (!other_value);
  assert (EMPTY_STACK (sweeper->clause));
  PUSH_STACK (sweeper->clause, lit);
  PUSH_STACK (sweeper->clause, other);
  sweep_clause (sweeper, depth);
}

static void sweep_reference (sweeper *sweeper, unsigned depth,
                             reference ref) {
  assert (EMPTY_STACK (sweeper->clause));
  kissat *solver = sweeper->solver;
  clause *c = kissat_dereference_clause (solver, ref);
  if (c->swept)
    return;
  if (c->garbage)
    return;
  LOGCLS (c, "sweeping[%u]", depth);
  value *values = solver->values;
  for (all_literals_in_clause (lit, c)) {
    const value value = values[lit];
    if (value > 0) {
      kissat_mark_clause_as_garbage (solver, c);
      CLEAR_STACK (sweeper->clause);
      return;
    }
    if (value < 0)
      continue;
    PUSH_STACK (sweeper->clause, lit);
  }
  PUSH_STACK (sweeper->refs, ref);
  c->swept = true;

  //Analog MallobSweep edgecase as above (@1), a clause we wanted to add to
  //the environment turns out to already be unit.
  if (SIZE_STACK(sweeper->clause)==1) {
    assert(GET_OPTION(mallob_sweeping));
    CLEAR_STACK (sweeper->clause);
    solver->shweep.stumbled_units++;
    return;
  }
  sweep_clause (sweeper, depth);
}

static void save_core_clause (void *state, bool learned, size_t size,
                              const unsigned *lits) {
  sweeper *sweeper = state;
  kissat *solver = sweeper->solver;
  if (solver->inconsistent)
    return;
  const value *const values = solver->values;
  unsigneds *core = sweeper->core + sweeper->save;
  size_t saved = SIZE_STACK (*core);
  const unsigned *end = lits + size;
  unsigned non_false = 0;
  for (const unsigned *p = lits; p != end; p++) {
    const unsigned lit = *p;
    const value value = values[lit];
    if (value > 0) {
      LOGLITS (size, lits, "extracted %s satisfied lemma", LOGLIT (lit));
      RESIZE_STACK (*core, saved);
      return;
    }
    PUSH_STACK (*core, lit);
    if (value < 0)
      continue;
    if (!learned && ++non_false > 1) {
      LOGLITS (size, lits, "ignoring extracted original clause");
      RESIZE_STACK (*core, saved);
      return;
    }
  }
#ifdef LOGGING
  unsigned *saved_lits = BEGIN_STACK (*core) + saved;
  size_t saved_size = SIZE_STACK (*core) - saved;
  LOGLITS (saved_size, saved_lits, "saved core[%u]", sweeper->save);
#endif
  PUSH_STACK (*core, INVALID_LIT);
}

static void add_core (sweeper *sweeper, unsigned core_idx) {
  kissat *solver = sweeper->solver;
  if (solver->inconsistent)
    return;
  LOG ("check and add extracted core[%u] lemmas to proof", core_idx);
  assert (core_idx == 0 || core_idx == 1);
  unsigneds *core = sweeper->core + core_idx;
  const value *const values = solver->values;

  unsigned *q = BEGIN_STACK (*core);
  const unsigned *const end_core = END_STACK (*core), *p = q;

  while (p != end_core) {
    const unsigned *c = p;
    while (*p != INVALID_LIT)
      p++;
#ifdef LOGGING
    size_t old_size = p - c;
    LOGLITS (old_size, c, "simplifying extracted core[%u] lemma", core_idx);
#endif
    bool satisfied = false;
    unsigned unit = INVALID_LIT;

    unsigned *d = q;

    for (const unsigned *l = c; !satisfied && l != p; l++) {
      const unsigned lit = *l;
      const value value = values[lit];
      if (value > 0) {
        satisfied = true;
        break;
      }
      if (!value)
        unit = *q++ = lit;
    }

    size_t new_size = q - d;
    p++;

    if (satisfied) {
      q = d;
      LOG ("not adding satisfied clause");
      continue;
    }

    if (!new_size) {
      LOG ("sweeping produced empty clause");
      kissat_custom_message (solver,V1_INFO_SWEEP, "SWEEPER found result UNSATISFIABLE ! found empty clause in kitten core");
      CHECK_AND_ADD_EMPTY ();
      ADD_EMPTY_TO_PROOF ();
      solver->inconsistent = true;
      CLEAR_STACK (*core);
      return;
    }

    if (new_size == 1) {
      q = d;
      assert (unit != INVALID_LIT);
      LOG ("sweeping produced unit %s", LOGLIT (unit));
      CHECK_AND_ADD_UNIT (unit);
      ADD_UNIT_TO_PROOF (unit);
      kissat_assign_unit (solver, unit, "sweeping backbone reason");
      if (GET_OPTION (exportmore)) {
        //(@1) Armin went here directly with kissat_assign_unit instead of 
        //kissat_learned_unit, probably to be able to pass the reason strings.
        //This means we need to do the export explicitly here. 
        kissat_export_redundant_clause (solver, 1, 1, &unit);
        solver->exportmore_statistics.unit_sweep++;
      }
      //Catch unit for sharing in MallobSweep
      if (GET_OPTION (mallob_sweeping)) {
        shweep_export_unit(solver, unit);
      }
      INC (sweep_units);
      continue;
    }

    *q++ = INVALID_LIT;

    assert (new_size > 1);
    LOGLITS (new_size, d, "adding extracted core[%u] lemma", core_idx);
    CHECK_AND_ADD_LITS (new_size, d);
    ADD_LITS_TO_PROOF (new_size, d);
  }
  SET_END_OF_STACK (*core, q);
#ifndef LOGGING
  (void) core_idx;
#endif
}

static void save_core (sweeper *sweeper, unsigned core) {
  kissat *solver = sweeper->solver;
  LOG ("saving extracted core[%u] lemmas", core);
  assert (core == 0 || core == 1);
  assert (EMPTY_STACK (sweeper->core[core]));
  sweeper->save = core;
  kitten_compute_clausal_core (solver->kitten, 0);
  kitten_traverse_core_clauses (solver->kitten, sweeper, save_core_clause);
}

static void clear_core (sweeper *sweeper, unsigned core_idx) {
  kissat *solver = sweeper->solver;
  if (solver->inconsistent)
    return;
#if defined(LOGGING) || !defined(NDEBUG) || !defined(NPROOFS)
  assert (core_idx == 0 || core_idx == 1);
  LOG ("clearing core[%u] lemmas", core_idx);
#endif
  unsigneds *core = sweeper->core + core_idx;
#ifdef CHECKING_OR_PROVING
  LOG ("deleting sub-solver core clauses");
  const unsigned *const end = END_STACK (*core);
  const unsigned *c = BEGIN_STACK (*core);
  for (const unsigned *p = c; c != end; c = ++p) {
    while (*p != INVALID_LIT)
      p++;
    const size_t size = p - c;
    assert (size > 1);
    REMOVE_CHECKER_LITS (size, c);
    DELETE_LITS_FROM_PROOF (size, c);
  }
#endif
  CLEAR_STACK (*core);
}

static void save_add_clear_core (sweeper *sweeper) {
  save_core (sweeper, 0);
  add_core (sweeper, 0);
  clear_core (sweeper, 0);
}

#define LOGBACKBONE(MESSAGE) \
  LOGLITSET (SIZE_STACK (sweeper->backbone), \
             BEGIN_STACK (sweeper->backbone), MESSAGE)

#define LOGPARTITION(MESSAGE) \
  LOGLITPART (SIZE_STACK (sweeper->partition), \
              BEGIN_STACK (sweeper->partition), MESSAGE)

static void init_backbone_and_partition (sweeper *sweeper) {
  kissat *solver = sweeper->solver;
  LOG ("initializing backbone and equivalent literals candidates");
  for (all_stack (unsigned, idx, sweeper->vars)) {
    if (!ACTIVE (idx))
      continue;
    const unsigned lit = LIT (idx);
    const unsigned not_lit = NOT (lit);
    const signed char tmp = kitten_value (solver->kitten, lit);
    const unsigned candidate = (tmp < 0) ? not_lit : lit;
    LOG ("sweeping candidate %s", LOGLIT (candidate));
    PUSH_STACK (sweeper->backbone, candidate);
    PUSH_STACK (sweeper->partition, candidate);
  }
  PUSH_STACK (sweeper->partition, INVALID_LIT);

  LOGBACKBONE ("initialized backbone candidates");
  LOGPARTITION ("initialized equivalence candidates");
}

static void sweep_empty_clause (sweeper *sweeper) {
  assert (!sweeper->solver->inconsistent);
  save_add_clear_core (sweeper);
  assert (sweeper->solver->inconsistent);
}

static void sweep_refine_partition (sweeper *sweeper) {
  kissat *solver = sweeper->solver;
  LOG ("refining partition");
  kitten *kitten = solver->kitten;
  unsigneds old_partition = sweeper->partition;
  unsigneds new_partition;
  INIT_STACK (new_partition);
  const value *const values = solver->values;
  const unsigned *const old_begin = BEGIN_STACK (old_partition);
  const unsigned *const old_end = END_STACK (old_partition);
#ifdef LOGGING
  unsigned old_classes = 0;
  unsigned new_classes = 0;
#endif
  for (const unsigned *p = old_begin, *q; p != old_end; p = q + 1) {
    unsigned assigned_true = 0, other;
    for (q = p; (other = *q) != INVALID_LIT; q++) {
      if (sweep_repr (sweeper, other) != other)
        continue;
      if (values[other])
        continue;
      signed char value = kitten_value (kitten, other);
      if (!value)
        LOG ("dropping sub-solver unassigned %s", LOGLIT (other));
      else if (value > 0) {
        PUSH_STACK (new_partition, other);
        assigned_true++;
      }
    }
#ifdef LOGGING
    LOG ("refining class %u of size %zu", old_classes, (size_t) (q - p));
    old_classes++;
#endif
    if (assigned_true == 0)
      LOG ("no positive literal in class");
    else if (assigned_true == 1) {
#ifdef LOGGING
      other =
#else
      (void)
#endif
          POP_STACK (new_partition);
      LOG ("dropping singleton class %s", LOGLIT (other));
    } else {
      LOG ("%u positive literal in class", assigned_true);
      PUSH_STACK (new_partition, INVALID_LIT);
#ifdef LOGGING
      new_classes++;
#endif
    }

    unsigned assigned_false = 0;
    for (q = p; (other = *q) != INVALID_LIT; q++) {
      if (sweep_repr (sweeper, other) != other)
        continue;
      if (values[other])
        continue;
      signed char value = kitten_value (kitten, other);
      if (value < 0) {
        PUSH_STACK (new_partition, other);
        assigned_false++;
      }
    }

    if (assigned_false == 0)
      LOG ("no negative literal in class");
    else if (assigned_false == 1) {
#ifdef LOGGING
      other =
#else
      (void)
#endif
          POP_STACK (new_partition);
      LOG ("dropping singleton class %s", LOGLIT (other));
    } else {
      LOG ("%u negative literal in class", assigned_false);
      PUSH_STACK (new_partition, INVALID_LIT);
#ifdef LOGGING
      new_classes++;
#endif
    }
  }
  RELEASE_STACK (old_partition);
  sweeper->partition = new_partition;
  LOG ("refined %u classes into %u", old_classes, new_classes);
  LOGPARTITION ("refined equivalence candidates");
}

static void sweep_refine_backbone (sweeper *sweeper) {
  kissat *solver = sweeper->solver;
  LOG ("refining backbone candidates");
  const unsigned *const end = END_STACK (sweeper->backbone);
  unsigned *q = BEGIN_STACK (sweeper->backbone);
  const value *const values = solver->values;
  kitten *kitten = solver->kitten;
  for (const unsigned *p = q; p != end; p++) {
    const unsigned lit = *p;
    if (values[lit])
      continue;
    signed char value = kitten_value (kitten, lit);
    if (!value)
      LOG ("dropping sub-solver unassigned %s", LOGLIT (lit));
    else if (value >= 0)
      *q++ = lit;
  }
  SET_END_OF_STACK (sweeper->backbone, q);
  LOGBACKBONE ("refined backbone candidates");
}

static void sweep_refine (sweeper *sweeper) {
#ifdef LOGGING
  kissat *solver = sweeper->solver;
#endif
  if (EMPTY_STACK (sweeper->backbone))
    LOG ("no need to refine empty backbone candidates");
  else
    sweep_refine_backbone (sweeper);
  if (EMPTY_STACK (sweeper->partition))
    LOG ("no need to refine empty partition candidates");
  else
    sweep_refine_partition (sweeper);
}

static void flip_backbone_literals (struct sweeper *sweeper) {
  struct kissat *solver = sweeper->solver;
  const unsigned max_rounds = GET_OPTION (sweepfliprounds);
  if (!max_rounds)
    return;
  assert (!EMPTY_STACK (sweeper->backbone));
  struct kitten *kitten = solver->kitten;
  if (kitten_status (kitten) != 10)
    return;
#ifdef LOGGING
  unsigned total_flipped = 0;
#endif
  unsigned flipped, round = 0;
  do {
    round++;
    flipped = 0;
    unsigned *begin = BEGIN_STACK (sweeper->backbone), *q = begin;
    const unsigned *const end = END_STACK (sweeper->backbone), *p = q;
    while (p != end) {
      const unsigned lit = *p++;
      INC (sweep_flip_backbone);
      if (kitten_flip_literal (kitten, lit)) {
        LOG ("flipping backbone candidate %s succeeded", LOGLIT (lit));
#ifdef LOGGING
        total_flipped++;
#endif
        INC (sweep_flipped_backbone);
        flipped++;
      } else {
        LOG ("flipping backbone candidate %s failed", LOGLIT (lit));
        *q++ = lit;
      }
    }
    SET_END_OF_STACK (sweeper->backbone, q);
    LOG ("flipped %u backbone candidates in round %u", flipped, round);

    if (TERMINATED (sweep_terminated_1))
      break;
    if (solver->statistics.kitten_ticks > sweeper->limit.ticks)
      break;
  } while (flipped && round < max_rounds);
  LOG ("flipped %u backbone candidates in total in %u rounds",
       total_flipped, round);
}

static bool sweep_backbone_candidate (sweeper *sweeper, unsigned lit) {
  kissat *solver = sweeper->solver;
  LOG ("trying backbone candidate %s", LOGLIT (lit));
  kitten *kitten = solver->kitten;
  signed char value = kitten_fixed (kitten, lit);
  if (value) {
    INC (sweep_fixed_backbone);
    LOG ("literal %s already fixed", LOGLIT (lit));
    assert (value > 0);
    return false;
  }

  INC (sweep_flip_backbone);
  if (kitten_status (kitten) == 10 && kitten_flip_literal (kitten, lit)) {
    INC (sweep_flipped_backbone);
    LOG ("flipping %s succeeded", LOGLIT (lit));
    LOGBACKBONE ("refined backbone candidates");
    return false;
  }

  LOG ("flipping %s failed", LOGLIT (lit));
  const unsigned not_lit = NOT (lit);
  INC (sweep_solved_backbone);
  kitten_assume (kitten, not_lit);
  int res = sweep_solve (sweeper);
  if (res == 10) {
    LOG ("sweeping backbone candidate %s failed", LOGLIT (lit));
    sweep_refine (sweeper);
    INC (sweep_sat_backbone);
    return false;
  }

  if (res == 20) {
    LOG ("sweep unit %s", LOGLIT (lit));
    save_add_clear_core (sweeper);
    INC (sweep_unsat_backbone);
    return true;
  }

  INC (sweep_unknown_backbone);

  LOG ("sweeping backbone candidate %s failed", LOGLIT (lit));
  return false;
}

static void add_binary (kissat *solver, unsigned lit, unsigned other) {
  kissat_new_binary_clause (solver, lit, other);
}

static bool scheduled_variable (sweeper *sweeper, unsigned idx) {
#ifndef NDEBUG
  kissat *const solver = sweeper->solver;
  assert (VALID_INTERNAL_INDEX (idx));
#endif
  return sweeper->prev[idx] != INVALID_IDX || sweeper->first == idx;
}

static void schedule_inner (sweeper *sweeper, unsigned idx) {
  kissat *const solver = sweeper->solver;
  assert (VALID_INTERNAL_INDEX (idx));
  if (!ACTIVE (idx))
    return;
  const unsigned next = sweeper->next[idx];
  if (next != INVALID_IDX) {
    LOG ("rescheduling inner %s as last", LOGVAR (idx));
    const unsigned prev = sweeper->prev[idx];
    assert (sweeper->prev[next] == idx);
    sweeper->prev[next] = prev;
    if (prev == INVALID_IDX) {
      assert (sweeper->first == idx);
      sweeper->first = next;
    } else {
      assert (sweeper->next[prev] == idx);
      sweeper->next[prev] = next;
    }
    const unsigned last = sweeper->last;
    if (last == INVALID_IDX) {
      assert (sweeper->first == INVALID_IDX);
      sweeper->first = idx;
    } else {
      assert (sweeper->next[last] == INVALID_IDX);
      sweeper->next[last] = idx;
    }
    sweeper->prev[idx] = last;
    sweeper->next[idx] = INVALID_IDX;
    sweeper->last = idx;
  } else if (sweeper->last != idx) {
    LOG ("scheduling inner %s as last", LOGVAR (idx));
    const unsigned last = sweeper->last;
    if (last == INVALID_IDX) {
      assert (sweeper->first == INVALID_IDX);
      sweeper->first = idx;
    } else {
      assert (sweeper->next[last] == INVALID_IDX);
      sweeper->next[last] = idx;
    }
    assert (sweeper->next[idx] == INVALID_IDX);
    sweeper->prev[idx] = last;
    sweeper->last = idx;
  } else
    LOG ("keeping inner %s scheduled as last", LOGVAR (idx));
}

static void schedule_outer (sweeper *sweeper, unsigned idx) {
#if !defined(NDEBUG) || defined(LOGGING)
  kissat *const solver = sweeper->solver;
#endif
  assert (VALID_INTERNAL_INDEX (idx));
  assert (!scheduled_variable (sweeper, idx));
  assert (ACTIVE (idx));
  const unsigned first = sweeper->first;
  if (first == INVALID_IDX) {
    assert (sweeper->last == INVALID_IDX);
    sweeper->last = idx;
  } else {
    assert (sweeper->prev[first] == INVALID_IDX);
    sweeper->prev[first] = idx;
  }
  assert (sweeper->prev[idx] == INVALID_IDX);
  sweeper->next[idx] = first;
  sweeper->first = idx;
  LOG ("scheduling outer %s as first", LOGVAR (idx));
}

static unsigned next_scheduled (sweeper *sweeper) {
#if !defined(NDEBUG) || defined(LOGGING)
  kissat *const solver = sweeper->solver;
#endif
  unsigned res = sweeper->last;
  if (res == INVALID_IDX) {
    LOG ("no more scheduled variables left");
    return INVALID_IDX;
  }
  assert (VALID_INTERNAL_INDEX (res));
  LOG ("dequeuing next scheduled %s", LOGVAR (res));
  const unsigned prev = sweeper->prev[res];
  assert (sweeper->next[res] == INVALID_IDX);
  sweeper->prev[res] = INVALID_IDX;
  if (prev == INVALID_IDX) {
    assert (sweeper->first == res);
    sweeper->first = INVALID_IDX;
  } else {
    assert (sweeper->next[prev] == res);
    sweeper->next[prev] = INVALID_IDX;
  }
  sweeper->last = prev;
  return res;
}

#define all_scheduled(IDX) \
  unsigned IDX = sweeper->first, NEXT_##IDX; \
  IDX != INVALID_IDX && (NEXT_##IDX = sweeper->next[IDX], true); \
  IDX = NEXT_##IDX

static void substitute_connected_clauses (sweeper *sweeper, unsigned lit,
                                          unsigned repr) {
  kissat *solver = sweeper->solver;
  if (solver->inconsistent)
    return;
  value *const values = solver->values;
  if (values[lit])
    return;
  if (values[repr])
    return;
  LOG ("substituting %s with %s in all irredundant clauses", LOGLIT (lit),
       LOGLIT (repr));

  assert (lit != repr);
  assert (lit != NOT (repr));

#ifdef CHECKING_OR_PROVING
  const bool checking_or_proving = kissat_checking_or_proving (solver);
  assert (EMPTY_STACK (solver->added));
  assert (EMPTY_STACK (solver->removed));
#endif

  unsigneds *const delayed = &solver->delayed;
  assert (EMPTY_STACK (*delayed));

  {
    watches *lit_watches = &WATCHES (lit);
    watch *const begin_watches = BEGIN_WATCHES (*lit_watches);
    const watch *const end_watches = END_WATCHES (*lit_watches);

    watch *q = begin_watches;
    const watch *p = q;

    while (p != end_watches) {
      const watch head = *q++ = *p++;
      if (head.type.binary) {
        const unsigned other = head.binary.lit;
        const value other_value = values[other];
        if (other == NOT (repr))
          continue;
        if (other_value < 0)
          break;
        if (other_value > 0)
          continue;
        if (other == repr) {
          CHECK_AND_ADD_UNIT (lit);
          ADD_UNIT_TO_PROOF (lit);
          kissat_assign_unit (solver, lit, "substituted binary clause");
          if (GET_OPTION (exportmore)) {
            //See (@1) on why we need to export manually
            kissat_export_redundant_clause (solver, 1, 1, &lit);
            solver->exportmore_statistics.unit_sweep++;
          }
          //Catch unit for sharing in MallobSweep
          if (GET_OPTION (mallob_sweeping)) {
            shweep_export_unit(solver, lit);
          }
          INC (sweep_units);
          break;
        }
        CHECK_AND_ADD_BINARY (repr, other);
        ADD_BINARY_TO_PROOF (repr, other);
        REMOVE_CHECKER_BINARY (lit, other);
        DELETE_BINARY_FROM_PROOF (lit, other);
        PUSH_STACK (*delayed, head.raw);
        watch src = {.raw = head.raw};
        watch dst = {.raw = head.raw};
        src.binary.lit = lit;
        dst.binary.lit = repr;
        watches *other_watches = &WATCHES (other);
        kissat_substitute_large_watch (solver, other_watches, src, dst);
        q--;
      } else {
        const reference ref = head.large.ref;
        assert (EMPTY_STACK (sweeper->clause));
        clause *c = kissat_dereference_clause (solver, ref);
        if (c->garbage)
          continue;

        bool satisfied = false;
        bool repr_already_watched = false;
        const unsigned not_repr = NOT (repr);
#ifndef NDEBUG
        bool found = false;
#endif
        for (all_literals_in_clause (other, c)) {
          if (other == lit) {
#ifndef NDEBUG
            assert (!found);
            found = true;
#endif
            PUSH_STACK (solver->clause, repr);
            continue;
          }
          assert (other != NOT (lit));
          if (other == repr) {
            assert (!repr_already_watched);
            repr_already_watched = true;
            continue;
          }
          if (other == not_repr) {
            satisfied = true;
            break;
          }
          const value tmp = values[other];
          if (tmp < 0)
            continue;
          if (tmp > 0) {
            satisfied = true;
            break;
          }
          PUSH_STACK (solver->clause, other);
        }

        if (satisfied) {
          CLEAR_STACK (solver->clause);
          kissat_mark_clause_as_garbage (solver, c);
          continue;
        }
        assert (found);

        const unsigned new_size = SIZE_STACK (solver->clause);

        if (new_size == 0) {
          LOGCLS (c, "substituted empty clause");
          kissat_custom_message (solver,V1_INFO_SWEEP,
            "SWEEPER found UNSAT! during clause substitution\n");
          assert (!solver->inconsistent);
          solver->inconsistent = true;
          CHECK_AND_ADD_EMPTY ();
          ADD_EMPTY_TO_PROOF ();
          break;
        }

        if (new_size == 1) {
          LOGCLS (c, "reduces to unit");
          const unsigned unit = POP_STACK (solver->clause);
          CHECK_AND_ADD_UNIT (unit);
          ADD_UNIT_TO_PROOF (unit);
          kissat_assign_unit (solver, unit, "substituted large clause");
          //See (@1) on why we need to export manually
          if (GET_OPTION (exportmore)) {
            kissat_export_redundant_clause (solver, 1, 1, &unit);
            solver->exportmore_statistics.unit_sweep++;
          }
          //Catch for sharing in MallobSweep
          if (GET_OPTION (mallob_sweeping)) {
            shweep_export_unit(solver, unit);
          }
          INC (sweep_units);
          break;
        }

        CHECK_AND_ADD_STACK (solver->clause);
        ADD_STACK_TO_PROOF (solver->clause);
        REMOVE_CHECKER_CLAUSE (c);
        DELETE_CLAUSE_FROM_PROOF (c);

        if (!c->redundant)
          kissat_mark_added_literals (solver, new_size,
                                      BEGIN_STACK (solver->clause));

        if (new_size == 2) {
          const unsigned second = POP_STACK (solver->clause);
          const unsigned first = POP_STACK (solver->clause);
          LOGCLS (c, "reduces to binary clause %s %s", LOGLIT (first),
                  LOGLIT (second));
          assert (first == repr || second == repr);
          const unsigned other = first ^ second ^ repr;
          const watch src = {.raw = head.raw};
          watch dst = kissat_binary_watch (repr);
          watches *other_watches = &WATCHES (other);
          kissat_substitute_large_watch (solver, other_watches, src, dst);
          assert (solver->statistics.clauses_irredundant);
          solver->statistics.clauses_irredundant--;
          assert (solver->statistics.clauses_binary < UINT64_MAX);
          solver->statistics.clauses_binary++;
          dst.binary.lit = other;
          PUSH_STACK (*delayed, dst.raw);
          const size_t bytes = kissat_actual_bytes_of_clause (c);
          ADD (arena_garbage, bytes);
          c->garbage = true;
          q--;
          continue;
        }

        assert (2 < new_size);
        const unsigned old_size = c->size;
        assert (new_size <= old_size);

        const unsigned *const begin = BEGIN_STACK (solver->clause);
        const unsigned *const end = END_STACK (solver->clause);

        unsigned *lits = c->lits;
        unsigned *q = lits;

        for (const unsigned *p = begin; p != end; p++) {
          const unsigned other = *p;
          *q++ = other;
        }

        if (new_size < old_size) {
          c->size = new_size;
          c->searched = 2;
          if (c->redundant && c->glue >= new_size)
            kissat_promote_clause (solver, c, new_size - 1);
          if (!c->shrunken) {
            c->shrunken = true;
            lits[old_size - 1] = INVALID_LIT;
          }
        }

        LOGCLS (c, "substituted");

        if (!repr_already_watched)
          PUSH_STACK (*delayed, head.raw);
        CLEAR_STACK (solver->clause);
        q--;
      }
    }
    while (p != end_watches)
      *q++ = *p++;
    SET_END_OF_WATCHES (*lit_watches, q);
  }
  {
    const unsigned *const begin_delayed = BEGIN_STACK (*delayed);
    const unsigned *const end_delayed = END_STACK (*delayed);
    for (const unsigned *p = begin_delayed; p != end_delayed; p++) {
      const watch head = {.raw = *p};
      watches *repr_watches = &WATCHES (repr);
      PUSH_WATCHES (*repr_watches, head);
    }

    CLEAR_STACK (*delayed);
  }

#ifdef CHECKING_OR_PROVING
  if (checking_or_proving) {
    CLEAR_STACK (solver->added);
    CLEAR_STACK (solver->removed);
  }
#endif
}

static void sweep_remove (sweeper *sweeper, unsigned lit) {
  kissat *solver = sweeper->solver;
  assert (sweeper->reprs[lit] != lit);
  unsigneds *partition = &sweeper->partition;
  unsigned *const begin_partition = BEGIN_STACK (*partition), *p;
  const unsigned *const end_partition = END_STACK (*partition);
  for (p = begin_partition; *p != lit; p++)
    assert (p + 1 != end_partition);
  unsigned *begin_class = p;
  while (begin_class != begin_partition && begin_class[-1] != INVALID_LIT)
    begin_class--;
  const unsigned *end_class = p;
  while (*end_class != INVALID_LIT)
    end_class++;
  const unsigned size = end_class - begin_class;
  LOG ("removing non-representative %s from equivalence class of size %u",
       LOGLIT (lit), size);
  assert (size > 1);
  unsigned *q = begin_class;
  if (size == 2) {
    LOG ("completely squashing equivalence class of %s", LOGLIT (lit));
    for (const unsigned *r = end_class + 1; r != end_partition; r++)
      *q++ = *r;
  } else {
    for (const unsigned *r = begin_class; r != end_partition; r++)
      if (r != p)
        *q++ = *r;
  }
  SET_END_OF_STACK (*partition, q);
#ifndef LOGGING
  (void) solver;
#endif
}

static void flip_partition_literals (struct sweeper *sweeper) {
  struct kissat *solver = sweeper->solver;
  const unsigned max_rounds = GET_OPTION (sweepfliprounds);
  if (!max_rounds)
    return;
  assert (!EMPTY_STACK (sweeper->partition));
  struct kitten *kitten = solver->kitten;
  if (kitten_status (kitten) != 10)
    return;
#ifdef LOGGING
  unsigned total_flipped = 0;
#endif
  unsigned flipped, round = 0;
  do {
    round++;
    flipped = 0;
    unsigned *begin = BEGIN_STACK (sweeper->partition), *dst = begin;
    const unsigned *const end = END_STACK (sweeper->partition), *src = dst;
    while (src != end) {
      const unsigned *end_src = src;
      while (assert (end_src != end), *end_src != INVALID_LIT)
        end_src++;
      unsigned size = end_src - src;
      assert (size > 1);
      unsigned *q = dst;
      for (const unsigned *p = src; p != end_src; p++) {
        const unsigned lit = *p;
        if (kitten_flip_literal (kitten, lit)) {
          LOG ("flipping equivalence candidate %s succeeded", LOGLIT (lit));
#ifdef LOGGING
          total_flipped++;
#endif
          flipped++;
          if (--size < 2)
            break;
        } else {
          LOG ("flipping equivalence candidate %s failed", LOGLIT (lit));
          *q++ = lit;
        }
      }
      if (size > 1) {
        *q++ = INVALID_LIT;
        dst = q;
      }
      src = end_src + 1;
    }
    SET_END_OF_STACK (sweeper->partition, dst);
    LOG ("flipped %u equivalence candidates in round %u", flipped, round);

    if (TERMINATED (sweep_terminated_2))
      break;
    if (solver->statistics.kitten_ticks > sweeper->limit.ticks)
      break;
  } while (flipped && round < max_rounds);
  LOG ("flipped %u equivalence candidates in total in %u rounds",
       total_flipped, round);
}

static bool sweep_equivalence_candidates (sweeper *sweeper, unsigned lit,
                                          unsigned other) {
  kissat *solver = sweeper->solver;
  LOG ("trying equivalence candidates %s = %s", LOGLIT (lit),
       LOGLIT (other));
  const unsigned not_other = NOT (other);
  const unsigned not_lit = NOT (lit);
  kitten *kitten = solver->kitten;
  const unsigned *const begin = BEGIN_STACK (sweeper->partition);
  unsigned *const end = END_STACK (sweeper->partition);
  assert (begin + 3 <= end);
  assert (end[-3] == lit);
  assert (end[-2] == other);
  const unsigned third = (end - begin == 3) ? INVALID_LIT : end[-4];
  const int status = kitten_status (kitten);
  if (status == 10 && kitten_flip_literal (kitten, lit)) {
    INC (sweep_flip_equivalences);
    INC (sweep_flipped_equivalences);
    LOG ("flipping %s succeeded", LOGLIT (lit));
    if (third == INVALID_LIT) {
      LOG ("squashing equivalence class of %s", LOGLIT (lit));
      SET_END_OF_STACK (sweeper->partition, end - 3);
    } else {
      LOG ("removing %s from equivalence class of %s", LOGLIT (lit),
           LOGLIT (other));
      end[-3] = other;
      end[-2] = INVALID_LIT;
      SET_END_OF_STACK (sweeper->partition, end - 1);
    }
    LOGPARTITION ("refined equivalence candidates");
    return false;
  } else if (status == 10 && kitten_flip_literal (kitten, other)) {
    ADD (sweep_flip_equivalences, 2);
    INC (sweep_flipped_equivalences);
    LOG ("flipping %s succeeded", LOGLIT (other));
    if (third == INVALID_LIT) {
      LOG ("squashing equivalence class of %s", LOGLIT (lit));
      SET_END_OF_STACK (sweeper->partition, end - 3);
    } else {
      LOG ("removing %s from equivalence class of %s", LOGLIT (other),
           LOGLIT (lit));
      end[-2] = INVALID_LIT;
      SET_END_OF_STACK (sweeper->partition, end - 1);
    }
    LOGPARTITION ("refined equivalence candidates");
    return false;
  }
  if (status == 10)
    ADD (sweep_flip_equivalences, 2);
  LOG ("flipping %s and %s both failed", LOGLIT (lit), LOGLIT (other));
  kitten_assume (kitten, not_lit);
  kitten_assume (kitten, other);
  INC (sweep_solved_equivalences);
  int res = sweep_solve (sweeper);
  if (res == 10) {
    INC (sweep_sat_equivalences);
    LOG ("first sweeping implication %s -> %s failed", LOGLIT (other),
         LOGLIT (lit));
    sweep_refine (sweeper);
  } else if (!res) {
    INC (sweep_unknown_equivalences);
    LOG ("first sweeping implication %s -> %s hit ticks limit",
         LOGLIT (other), LOGLIT (lit));
  }

  if (res != 20)
    return false;

  INC (sweep_unsat_equivalences);
  LOG ("first sweeping implication %s -> %s succeeded", LOGLIT (other),
       LOGLIT (lit));

  save_core (sweeper, 0);

  kitten_assume (kitten, lit);
  kitten_assume (kitten, not_other);
  res = sweep_solve (sweeper);
  INC (sweep_solved_equivalences);
  if (res == 10) {
    INC (sweep_sat_equivalences);
    LOG ("second sweeping implication %s <- %s failed", LOGLIT (other),
         LOGLIT (lit));
    sweep_refine (sweeper);
  } else if (!res) {
    INC (sweep_unknown_equivalences);
    LOG ("second sweeping implication %s <- %s hit ticks limit",
         LOGLIT (other), LOGLIT (lit));
  }

  if (res != 20) {
    CLEAR_STACK (sweeper->core[0]);
    return false;
  }

  INC (sweep_unsat_equivalences);
  LOG ("second sweeping implication %s <- %s succeeded too", LOGLIT (other),
       LOGLIT (lit));

  save_core (sweeper, 1);

  LOG ("sweep equivalence %s = %s", LOGLIT (lit), LOGLIT (other));
  INC (sweep_equivalences);

  add_core (sweeper, 0);
  add_binary (solver, lit, not_other);
  clear_core (sweeper, 0);

  add_core (sweeper, 1);
  add_binary (solver, not_lit, other);
  clear_core (sweeper, 1);
  
  if (GET_OPTION (exportmore)) {
    kissat_export_redundant_binary (solver, lit, not_other);
    kissat_export_redundant_binary (solver, not_lit, other);
    solver->exportmore_statistics.bin_sweep+=2;
  }

  if (GET_OPTION (mallob_sweeping)) {
    shweep_export_equivalence(solver, lit, other);
  }
  unsigned repr;
  if (lit < other) {
    repr = sweeper->reprs[other] = lit;
    sweeper->reprs[not_other] = not_lit;
    substitute_connected_clauses (sweeper, other, lit);
    substitute_connected_clauses (sweeper, not_other, not_lit);
    sweep_remove (sweeper, other);
  } else {
    repr = sweeper->reprs[lit] = other;
    sweeper->reprs[not_lit] = not_other;
    substitute_connected_clauses (sweeper, lit, other);
    substitute_connected_clauses (sweeper, not_lit, not_other);
    sweep_remove (sweeper, lit);
  }

  //Added a custom resweeping logic for  MallobSweep, where a found equivalence
  //can be directly used as the starting point of the next sweep.
  //Resweeping is deactivated by default, though, because it can lead to more
  //redundant work, when different solvers resweep the same variable.
  const unsigned repr_idx = IDX (repr);
  if (!GET_OPTION (mallob_sweeping)) {
    //original behaviour before/without MallobSweep
    schedule_inner (sweeper, repr_idx);
  } else {
    int rnd_per_mille = kissat_pick_random(&solver->random, 0,1000); //in range [0..999]
    if (rnd_per_mille < GET_OPTION (mallob_resweep_chance)) {
      PUSH_STACK(sweeper->RESWEEP, repr_idx);
    }
  }
  return true;
}

static const char *sweep_variable (sweeper *sweeper, unsigned idx) {
  kissat *solver = sweeper->solver;
  assert (!solver->inconsistent);
  if (!ACTIVE (idx))
    return "inactive variable";
  const unsigned start = LIT (idx);
  if (sweeper->reprs[start] != start)
    return "non-representative variable";
  assert (EMPTY_STACK (sweeper->vars));
  assert (EMPTY_STACK (sweeper->refs));
  assert (EMPTY_STACK (sweeper->backbone));
  assert (EMPTY_STACK (sweeper->partition));
  assert (!sweeper->encoded);

  INC (sweep_variables);

  LOG ("sweeping %s", LOGVAR (idx));
  assert (!VALUE (start));
  LOG ("starting sweeping[0]");
  add_literal_to_environment (sweeper, 0, start);
  LOG ("finished sweeping[0]");
  LOG ("starting sweeping[1]");

  bool limit_reached = false;
  size_t expand = 0, next = 1;
  bool success = false;
  unsigned depth = 1;

  while (!limit_reached) {
    if (sweeper->encoded >= sweeper->limit.clauses) {
      LOG ("environment clause limit reached");
      limit_reached = true;
      break;
    }
    if (expand == next) {
      LOG ("finished sweeping[%u]", depth);
      if (depth >= sweeper->limit.depth) {
        LOG ("environment depth limit reached");
        break;
      }
      next = SIZE_STACK (sweeper->vars);
      if (expand == next) {
        LOG ("completely copied all clauses");
        break;
      }
      depth++;
      LOG ("starting sweeping[%u]", depth);
    }
    const unsigned choices = next - expand;
    if (GET_OPTION (sweeprand) && choices > 1) {
      const unsigned swap =
          kissat_pick_random (&solver->random, 0, choices);
      if (swap) {
        unsigned *vars = sweeper->vars.begin;
        SWAP (unsigned, vars[expand], vars[expand + swap]);
      }
    }
    const unsigned idx = PEEK_STACK (sweeper->vars, expand);
    LOG ("traversing and adding clauses of %s", LOGVAR (idx));
    for (unsigned sign = 0; sign < 2; sign++) {
      const unsigned lit = LIT (idx) + sign;
      watches *watches = &WATCHES (lit);
      for (all_binary_large_watches (watch, *watches)) {
        if (watch.type.binary) {
          const unsigned other = watch.binary.lit;
          sweep_binary (sweeper, depth, lit, other);
        } else {
          reference ref = watch.large.ref;
          sweep_reference (sweeper, depth, ref);
        }
        if (SIZE_STACK (sweeper->vars) >= sweeper->limit.vars) {
          LOG ("environment variable limit reached");
          limit_reached = true;
          break;
        }
      }
      if (limit_reached)
        break;
    }
    expand++;
  }
  ADD (sweep_depth, depth);
  ADD (sweep_clauses, sweeper->encoded);
  ADD (sweep_environment, SIZE_STACK (sweeper->vars));
  kissat_extremely_verbose (solver,
                            "sweeping variable %d environment of "
                            "%zu variables %u clauses depth %u",
                            kissat_export_literal (solver, LIT (idx)),
                            SIZE_STACK (sweeper->vars), sweeper->encoded,
                            depth);
  int res = sweep_solve (sweeper);
  LOG ("sub-solver returns '%d'", res);
  if (res == 10) {
    init_backbone_and_partition (sweeper);
#ifndef QUIET
    uint64_t units = solver->statistics.sweep_units;
    uint64_t solved = solver->statistics.sweep_solved;
#endif
    START (sweepbackbone);
    while (!EMPTY_STACK (sweeper->backbone)) {
      if (solver->inconsistent || TERMINATED (sweep_terminated_3) ||
          kitten_ticks_limit_hit (sweeper, "backbone refinement")) {
        limit_reached = true;
      STOP_SWEEP_BACKBONE:
        STOP (sweepbackbone);
        goto DONE;
      }
      flip_backbone_literals (sweeper);
      if (TERMINATED (sweep_terminated_4) ||
          kitten_ticks_limit_hit (sweeper, "backbone refinement")) {
        limit_reached = true;
        goto STOP_SWEEP_BACKBONE;
      }
      if (EMPTY_STACK (sweeper->backbone))
        break;
      const unsigned lit = POP_STACK (sweeper->backbone);
      if (!ACTIVE (IDX (lit)))
        continue;
      if (sweep_backbone_candidate (sweeper, lit))
        success = true;
    }
    STOP (sweepbackbone);
#ifndef QUIET
    units = solver->statistics.sweep_units - units;
    solved = solver->statistics.sweep_solved - solved;
    kissat_extremely_verbose (
        solver,
        "complete swept variable %d backbone with %" PRIu64
        " units in %" PRIu64 " solver calls",
        kissat_export_literal (solver, LIT (idx)), units, solved);
#endif
    assert (EMPTY_STACK (sweeper->backbone));
#ifndef QUIET
    uint64_t equivalences = solver->statistics.sweep_equivalences;
    solved = solver->statistics.sweep_solved;
#endif
    START (sweepequivalences);
    while (!EMPTY_STACK (sweeper->partition)) {
      if (solver->inconsistent || TERMINATED (sweep_terminated_5) ||
          kitten_ticks_limit_hit (sweeper, "partition refinement")) {
        limit_reached = true;
      STOP_SWEEP_EQUIVALENCES:
        STOP (sweepequivalences);
        goto DONE;
      }
      flip_partition_literals (sweeper);
      if (TERMINATED (sweep_terminated_6) ||
          kitten_ticks_limit_hit (sweeper, "backbone refinement")) {
        limit_reached = true;
        goto STOP_SWEEP_EQUIVALENCES;
      }
      if (EMPTY_STACK (sweeper->partition))
        break;
      if (SIZE_STACK (sweeper->partition) > 2) {
        const unsigned *end = END_STACK (sweeper->partition);
        assert (end[-1] == INVALID_LIT);
        unsigned lit = end[-3];
        unsigned other = end[-2];
        if (sweep_equivalence_candidates (sweeper, lit, other))
          success = true;
      } else
        CLEAR_STACK (sweeper->partition);
    }
    STOP (sweepequivalences);
#ifndef QUIET
    equivalences = solver->statistics.sweep_equivalences - equivalences;
    solved = solver->statistics.sweep_solved - solved;
    if (equivalences)
      kissat_extremely_verbose (
          solver,
          "complete swept variable %d partition with %" PRIu64
          " equivalences in %" PRIu64 " solver calls",
          kissat_export_literal (solver, LIT (idx)), equivalences, solved);
#endif
  } else if (res == 20)
    sweep_empty_clause (sweeper);

DONE:
  clear_sweeper (sweeper);

  if (!solver->inconsistent && !kissat_propagated (solver))
    (void) kissat_dense_propagate (solver);

  if (success && limit_reached)
    return "successfully despite reaching limit";
  if (!success && !limit_reached)
    return "unsuccessfully without reaching limit";
  else if (success && !limit_reached)
    return "successfully without reaching limit";
  assert (!success && limit_reached);
  return "unsuccessfully and reached limit";
}

typedef struct sweep_candidate sweep_candidate;

struct sweep_candidate {
  unsigned rank;
  unsigned idx;
};

// clang-format off

typedef STACK(sweep_candidate) sweep_candidates;

// clang-format on

#define RANK_SWEEP_CANDIDATE(CAND) (CAND).rank

static bool scheduable_variable (sweeper *sweeper, unsigned idx,
                                 size_t *occ_ptr) {
  kissat *solver = sweeper->solver;
  const unsigned lit = LIT (idx);
  const size_t pos = SIZE_WATCHES (WATCHES (lit));
  if (!pos)
    return false;
  const unsigned max_occurrences = sweeper->limit.clauses;
  if (pos > max_occurrences)
    return false;
  const unsigned not_lit = NOT (lit);
  const size_t neg = SIZE_WATCHES (WATCHES (not_lit));
  if (!neg)
    return false;
  if (neg > max_occurrences)
    return false;
  *occ_ptr = pos + neg;
  return true;
}

static unsigned schedule_all_other_not_scheduled_yet (sweeper *sweeper) {
  kissat *solver = sweeper->solver;
  sweep_candidates fresh;
  INIT_STACK (fresh);
  flags *const flags = solver->flags;
  const bool incomplete = solver->sweep_incomplete;
  for (all_variables (idx)) {
    struct flags *const f = flags + idx;
    if (!f->active)
      continue;
    if (incomplete && !f->sweep)
      continue;
    if (scheduled_variable (sweeper, idx))
      continue;
    size_t occ;
    if (!scheduable_variable (sweeper, idx, &occ)) {
      FLAGS (idx)->sweep = false;
      continue;
    }
    sweep_candidate cand;
    cand.rank = occ;
    cand.idx = idx;
    PUSH_STACK (fresh, cand);
  }
  const size_t size = SIZE_STACK (fresh);
  assert (size <= UINT_MAX);
  RADIX_STACK (sweep_candidate, unsigned, fresh, RANK_SWEEP_CANDIDATE);
  for (all_stack (sweep_candidate, cand, fresh))
    schedule_outer (sweeper, cand.idx);
  RELEASE_STACK (fresh);
  return size;
}

static unsigned reschedule_previously_remaining (sweeper *sweeper) {
  kissat *solver = sweeper->solver;
  flags *flags = solver->flags;
  unsigned rescheduled = 0;
  unsigneds *remaining = &solver->sweep_schedule;
  for (all_stack (unsigned, idx, *remaining)) {
    struct flags *f = flags + idx;
    if (!f->active)
      continue;
    if (scheduled_variable (sweeper, idx))
      continue;
    size_t occ;
    if (!scheduable_variable (sweeper, idx, &occ)) {
      f->sweep = false;
      continue;
    }
    schedule_inner (sweeper, idx);
    rescheduled++;
  }
  RELEASE_STACK (*remaining);
  return rescheduled;
}

static unsigned incomplete_variables (sweeper *sweeper) {
  kissat *solver = sweeper->solver;
  flags *flags = solver->flags;
  unsigned res = 0;
  for (all_variables (idx)) {
    struct flags *f = flags + idx;
    if (!f->active)
      continue;
    if (f->sweep)
      res++;
  }
  return res;
}

static void mark_incomplete (sweeper *sweeper) {
  kissat *solver = sweeper->solver;
  flags *flags = solver->flags;
  unsigned marked = 0;
  for (all_scheduled (idx))
    if (!flags[idx].sweep) {
      flags[idx].sweep = true;
      marked++;
    }
  solver->sweep_incomplete = true;
#ifndef QUIET
  kissat_extremely_verbose (
      solver, "marked %u scheduled sweeping variables as incomplete",
      marked);
#else
  (void) marked;
#endif
}

static unsigned schedule_sweeping (sweeper *sweeper) {
  const unsigned rescheduled = reschedule_previously_remaining (sweeper);
  const unsigned fresh = schedule_all_other_not_scheduled_yet (sweeper);
  const unsigned scheduled = fresh + rescheduled;
  const unsigned incomplete = incomplete_variables (sweeper);
  kissat *solver = sweeper->solver;
#ifndef QUIET
  kissat_phase (solver, "sweep", GET (sweep),
                "scheduled %u variables %.0f%% "
                "(%u rescheduled %.0f%%, %u incomplete %.0f%%)",
                scheduled,
                kissat_percent (scheduled, sweeper->solver->active),
                rescheduled, kissat_percent (rescheduled, scheduled),
                incomplete, kissat_percent (incomplete, scheduled));
#endif
  if (incomplete)
    assert (solver->sweep_incomplete);
  else {
    if (solver->sweep_incomplete)
      INC (sweep_completed);
    mark_incomplete (sweeper);
  }
  return scheduled;
}

static void unschedule_sweeping (sweeper *sweeper, unsigned swept,
                                 unsigned scheduled) {
  kissat *solver = sweeper->solver;
#ifdef QUIET
  (void) scheduled, (void) swept;
#endif
  assert (EMPTY_STACK (solver->sweep_schedule));
  assert (solver->sweep_incomplete);
  flags *flags = solver->flags;
  for (all_scheduled (idx))
    if (flags[idx].active) {
      PUSH_STACK (solver->sweep_schedule, idx);
      LOG ("untried scheduled %s", LOGVAR (idx));
    }
#ifndef QUIET
  const unsigned retained = SIZE_STACK (solver->sweep_schedule);
  kissat_extremely_verbose (
      solver, "retained %u variables %.0f%% to be swept next time",
      retained, kissat_percent (retained, solver->active));
#endif
  const unsigned incomplete = incomplete_variables (sweeper);
  if (incomplete)
    kissat_extremely_verbose (
        solver, "need to sweep %u more variables %.0f%% for completion",
        incomplete, kissat_percent (incomplete, solver->active));
  else {
    kissat_extremely_verbose (solver,
                              "no more variables needed to complete sweep");
    solver->sweep_incomplete = false;
    INC (sweep_completed);
  }
  kissat_phase (solver, "sweep", GET (sweep),
                "swept %u variables (%u remain %.0f%%)", swept, incomplete,
                kissat_percent (incomplete, scheduled));
}

bool shweep_var_still_open(sweeper *sweeper, unsigned idx) {
  kissat *solver = sweeper->solver;
  unsigned lit = LIT(idx);
  if (!FLAGS(idx)->sweep) {
    return false;
  }
  if (!ACTIVE(idx)) {
    return false;
  }
  if (sweep_repr (sweeper, lit) != lit) {
    return false;
  }
  size_t occ;
  if (!scheduable_variable (sweeper, idx, &occ)) {
    FLAGS (idx)->sweep = false;
    return false;
  }
  return true;
}


void shweep_import_single_unit(sweeper *sweeper, unsigned ilit) {
  kissat *solver = sweeper->solver;
  assert(VALID_INTERNAL_LITERAL (ilit) || kissat_custom_assert_message (
    solver, "SWEEP ERROR: imported invalid unit ilit %u", ilit));
  const unsigned repr_ilit = sweep_repr (sweeper, ilit);
  solver->shweep.units_seen++;
  assert(VALID_INTERNAL_LITERAL (repr_ilit) || kissat_custom_assert_message (
    solver, "SWEEP ERROR: got invalid repr_unit ilit %u from imported ilit %u", repr_ilit, ilit));
  const unsigned repr_idx = IDX (repr_ilit);
  flags *flags = FLAGS (repr_idx);
  if (!flags->active) {
    if (solver->values[repr_ilit] != 1) {
      kissat_custom_message (solver, 1, "Sweeper detected an inconsistent Unit-import, expect official un-sat result soon.");
      solver->shweep.detected_early_unsat++;
    }
    solver->shweep.units_skipped_fixed++;
    return;
  }
  assert(!flags->eliminated || kissat_custom_assert_message (
    solver, "SWEEP ERROR/Error: imported eliminated unit %u", ilit));
  if (ilit != repr_ilit) {
    solver->shweep.units_transitive++;
  }
  assert (!solver->values[repr_ilit] || kissat_custom_assert_message (
    solver, "Sweep ERROR : assigning repr_ilit %u (original lit %i), but already has a value %i", repr_ilit, ilit, solver->values[repr_ilit]));
  assert (!solver->values[NOT(repr_ilit)] || kissat_custom_assert_message (
    solver, "Sweep ERROR : assigning not_repr_ilit %u, but already has a value %i", NOT(repr_ilit), solver->values[NOT(repr_ilit)]));
  kissat_assign_unit (solver, repr_ilit, "shweep imported unit");
  solver->shweep.units_useful++;
  INC (sweep_units);
}

void shweep_import_single_equivalence(sweeper *sweeper, unsigned ilit1, unsigned ilit2) {
  kissat *solver = sweeper->solver;
  solver->shweep.eqs_seen++;
  unsigned imported_ilits[2] = {ilit1, ilit2};
  unsigned repr_ilits[2];
  bool is_transitive = false;
  int already_fixed = 0;
  for (int i=0; i<2; i++) {
    const unsigned ilit = imported_ilits[i];
    assert(VALID_INTERNAL_LITERAL (ilit) || kissat_custom_assert_message(
      solver, "SWEEP ERROR/Error: imported ilit %u not valid internal literal", ilit));
    //We might have some other internal representative literal for this imported literal
    const unsigned repr_ilit = sweep_repr(sweeper, ilit);
    assert(VALID_INTERNAL_LITERAL (repr_ilit) || kissat_custom_assert_message(
      solver, "SWEEP ERROR/Error: repr_ilit %u not valid internal literal", repr_ilit));
    if (ilit != repr_ilit)
      is_transitive = true;
    const unsigned repr_idx = IDX (repr_ilit);
    flags *flags = FLAGS (repr_idx);
    if (!flags->active) {
      already_fixed++;
      assert(solver->values[repr_ilit]!=0 || kissat_custom_assert_message(
        solver,  "SWEEP ERROR/Error: eq-imported lit not active , but also no value set. ilit/repr_ilit %i/%i  val %i", ilit, repr_ilit, solver->values[repr_ilit]));
    }
    assert(!flags->eliminated || kissat_custom_assert_message(
      solver,  "SWEEP ERROR/Error: imported an eq-literal ilit(%u) that is locally eliminated", ilit));
    repr_ilits[i]=repr_ilit;
  }
  unsigned lit    = repr_ilits[0];
  unsigned other  = repr_ilits[1];
  if (IDX(lit) == IDX(other)) {
    solver->shweep.eqs_skipped_known++;
    return;
  }
  if (already_fixed==2) {
    //We learned about a new equivalence, but both values happen to be
    //already fixed, independently of each other. Thus, they better be equal.
    //If not, we just detected UNSAT.
    if (solver->values[lit] != solver->values[other]) {
      //Found UNSAT! The imported equivalence is inconsistent with the local clause database.
      //We could officially claim UNSAT (to Mallob) at this point.
      //It feels however a bit shaky to do this here via our custom import function.
      //We rather wait until the solver finds UNSAT through normal sweeping,
      //which anyways happens almost immediately after such an import, to our experience
      kissat_custom_message (solver, 1, "Sweeper detected an inconsistent Equality-import, expect official un-sat result soon.");
      solver->shweep.detected_early_unsat++;
    }
    solver->shweep.eqs_skipped_doublefixed++;
    return;
  }
  if (is_transitive)
    solver->shweep.eqs_transitive++;
  //Interesting edge case: One of the two eq variables is already fixed
  //but the other is not, so we just got a propagating unit clause
  if (already_fixed==1)
    solver->shweep.eqs_unitprop++;
  if (other < lit) {
    unsigned tmp = lit;
    lit = other;
    other = tmp;
  }
  assert(lit < other);
  const unsigned not_lit = NOT (lit);
  const unsigned not_other = NOT (other);
  add_binary (solver, lit, not_other);
  add_binary (solver, not_lit, other);
  sweeper->reprs[other] = lit;
  sweeper->reprs[not_other] = not_lit;
  substitute_connected_clauses (sweeper, other, lit);
  substitute_connected_clauses (sweeper, not_other, not_lit);
  // Update 17.03: tried adding 'sweep_remove (sweeper, other)' here,
  // reflecting kissats own equivalence handling (at the end of sweep_equivalence_candidates(...))
  // but adding it caused immediate crashes, so I didnt put it here
  solver->shweep.eqs_useful++;
  INC (sweep_equivalences);
}

//Imports all units from MallobSweep that are available.
void shweep_import_SweepJob_units(sweeper *sweeper) {
  kissat *solver = sweeper->solver;
  if (!solver->shweep_import_SweepJob_unit_callback) {
    return;
  }
  if (solver->inconsistent) {
    return;
  }
  int count = 0;
  for (;;) {
    if ((solver->shweep_end_job_signal || solver->shweep_end_iteration_signal)) {
      //(@2) Exit immediately when we receive a stop signal from MallobSweep.
      //Prevents blocking behaviour, which happened especially when solvers
      //joined late to the party and first started to import a lot of things,
      //which could take a lot of time and prevent MallobSweep
      //from shutting down this solver
      kissat_custom_message (solver, V1_INFO_SWEEP, "SWEEP skip import due to iter/job end");
      break;
    }
    int elit = 0;
    solver->shweep_import_SweepJob_unit_callback (solver->shweep_mallob_SweepJobState, &elit, sweeper->localId);
    if (elit==INVALID_ELIT) {
      //there are no more units to import. exit
      break;
    }
    if (elit==0) {
      //the current import round is fully imported,
      //but that there are more import rounds ready,
      //access them by repeating this loop
      continue;
    }
    count++;
    assert(VALID_EXTERNAL_LITERAL (elit) || kissat_custom_assert_message (
      solver, "Sweeper ERROR : imported invalid external elit %i ", elit));
    unsigned ilit = kissat_import_literal (solver, elit);
    if (ilit==INVALID_LIT) {
      kissat_custom_message (solver, V4_UVERB_SWEEP, "import:  i(%u) <- e[%i] skipped - is already locally eliminated ",ilit,elit);
      continue;
    }
    kissat_custom_message (solver, V4_UVERB_SWEEP, "import:  i(%u) <- e[%i]",ilit,elit);
    shweep_import_single_unit (sweeper, ilit);

    if (solver->inconsistent) {
      kissat_custom_message (solver, V1_INFO_SWEEP, "SWEEP found UNSAT while importing units!");
      return;
    }
  }
  if (count>0) {
    kissat_custom_message(solver, V3_VVERB_SWEEP,  "UnitImport saw %i units", count);
  }

}

void shweep_import_SweepJob_equivalences(sweeper *sweeper) {
  kissat *solver = sweeper->solver;
  if (!solver->shweep_import_SweepJob_eq_callback) {
    return;
  }
  if (solver->inconsistent) {
    return;
  }
  int count = 0;
  for (;;) {
    if ((solver->shweep_end_job_signal || solver->shweep_end_iteration_signal)) {
      //Prevent blocking, see also (@2)
      kissat_custom_message (solver, V1_INFO_SWEEP, "SWEEP skip import due to iter/job end");
      break;
    }
    int elit1 = 0;
    int elit2 = 0;
    solver->shweep_import_SweepJob_eq_callback (solver->shweep_mallob_SweepJobState, &elit1, &elit2, sweeper->localId);
    if (elit1 == INVALID_ELIT && elit2 == INVALID_ELIT) {
      //there are no more equivalences to import. exit
      break;
    }
    if (elit1==0 && elit2 == 0) {
      //the current import round is fully imported,
      //but that there are more import rounds ready,
      //access them by repeating this loop
      continue;
    }
    if (solver->inconsistent) {
      return;
    }
    count++;
    assert(VALID_EXTERNAL_LITERAL (elit1) || kissat_custom_assert_message (solver, "Sweeper ERROR : imported invalid external elit1 %i ", elit1));
    assert(VALID_EXTERNAL_LITERAL (elit2) || kissat_custom_assert_message (solver, "Sweeper ERROR : imported invalid external elit2 %i ", elit2));
    unsigned ilit1 = kissat_import_literal (solver, elit1);
    unsigned ilit2 = kissat_import_literal (solver, elit2);
    if (ilit1==INVALID_LIT || ilit2==INVALID_LIT) {
      kissat_custom_message (solver, V4_UVERB_SWEEP, "import:  i(%i,%i) <- e[%i,%i]  skipped - at least one already locally eliminated", ilit1, ilit2, elit1, elit2);
      continue;
    }
    kissat_custom_message (solver, V4_UVERB_SWEEP, "import:  i(%i,%i) <- e{%i,%i} ", ilit1, ilit2, elit1, elit2);
    shweep_import_single_equivalence (sweeper, ilit1, ilit2);
    if (solver->inconsistent) {
      kissat_custom_message (solver, V1_INFO_SWEEP, "SWEEP found UNSAT while importing equivalences!");
      return;
    }
  }
  if (count > 0) {
    kissat_custom_message(solver, V3_VVERB_SWEEP,  "EqImport saw %i eqs", count);
  }

}

//Another solver wants to steal from this solver here.
//The stealer wants to know beforehand how much there is to steal,
//to pre-allocate a respective amount of memory (done in Mallob in C++)
//The stealers thread calls this method, which is ok because it is read-only.
int shweep_get_max_steal_amount(kissat *solver) {
  //guard against stealing when the victim solver is not ready yet, i.e.
  //doesnt even have all of its necessary field initialized
  if (!solver || !solver->shweeper_allows_stealing || !solver->sweeper) {
    kissat_custom_message(solver,V4_UVERB_SWEEP, "SWEEP STEAL Guard: not allowing stealing right now");
    return 0;
  }
  sweeper *sweeper = solver->sweeper;
  //We have two different ways to estimate the amount of remaining work,
  //without needing to actually iterate through every variable in the worklist
  //1. via the remaining range
  //2. via the count during the last steal (where each variable in the worklist was last checked)
  int range_estimate = sweeper->work_end - sweeper->work_head;
  int last_estimate = sweeper->max_work_after_steal;
  int max_work_left = MIN(last_estimate, range_estimate);
  int half = max_work_left/2;
  assert( (half>=0 && half<=solver->vars) || kissat_custom_assert_message (solver, "SWEEPER ERROR: unexpected amount half=%i work\n", half));
  return half;
}

int shweep_get_work_estimate(kissat *solver) {
  if (!solver || !solver->shweeper_allows_stealing || !solver->sweeper) {
    return -1;
  }
  sweeper *sweeper = solver->sweeper;
  return sweeper->work_end - sweeper->work_head;
}

//Another solver decided that it wants to steal work from this solver
//and it already inquired for the maximum steal amount
//This method is called by the stealers thread, which means we can now have concurrent access on the ->work array
//Such individual 32-bit integer writes should be atomic however on almost all hardware, so we keep it this simple way
int shweep_steal_from_this_solver(kissat *solver, unsigned *stolen_work, int max_steal_count) {
  if (!solver || !solver->shweeper_allows_stealing) {
    kissat_custom_message (solver, V1_INFO_SWEEP, "Guarded against executed steal attempt (solver null or stealing not allowed)");
    return 0;
  }
  sweeper *sweeper = solver->sweeper;
  if (!sweeper) {
    kissat_custom_message (solver, V1_INFO_SWEEP, "Guarded against executed steal attempt (sweeper null)");
    return 0;
  }
  //It can happen that this victim solver finds UNSAT while a stealer solver is still
  //stealing. In that case, the stealer solver expects all the references
  //to still remain valid during stealing. Thus the victim solver
  //must be reminded to wait with deallocating itself until any active stealing is finished.
  sweeper->somebody_is_stealing_from_me = true;
  //Steal every second variable in the worklist that is still open for sweeping
  int stolen_count=0;
  int locally_left = 0;
  bool steal_flipflop=false;
  unsigned *work = sweeper->work;
  const int work_end = sweeper->work_end;
  for (int i = sweeper->work_head; i < work_end; i++) {
    unsigned idx = work[i];
    if (idx==INVALID_IDX) //the variable written at this spot has already been stolen or deactivated
      continue;
    if (!shweep_var_still_open(sweeper, idx)) {
      //this variable is no longer relevant for sweeping, skip it
      continue;
    }
    //variable is still open for sweeping.
    if (steal_flipflop && stolen_count < max_steal_count) {
      stolen_work[stolen_count]=idx; //steal
      stolen_count++;
      //deactivate in local worklist, such that the local solver no longer sweeps this variable
      work[i] = INVALID_IDX;
      //also mark that this variable is no longer in our work set,
      //i.e. no longer to-sweep. Relevant when considered as a resweep-candidate
      FLAGS(idx)->sweep=false;
    } else {
      locally_left++;
    }
    steal_flipflop = !steal_flipflop;
  }
  if (stolen_count > max_steal_count) {
    kissat_custom_message (solver, V0_CRIT_SWEEP, "Error: stolen_count=%i, max_steal_count=%i", stolen_count, max_steal_count);
    assert(kissat_custom_assert_message (solver, "stolen count > max_steal_count"));
  }
  sweeper->max_work_after_steal = locally_left;
  sweeper->somebody_is_stealing_from_me = false;
  return stolen_count;
}


unsigned shweep_search_work_from_others(sweeper *sweeper) {
  kissat *solver = sweeper->solver;
  sweeper->work_head = 0;
  sweeper->work_end = 0;
  sweeper->max_work_after_steal = 0;
  int stolen_amount = 0;
  kissat_custom_message(solver,V1_INFO_SWEEP, "searching work @ %.3f", shweep_wallclock (solver));
  //The callback brings the solver thread goes into the Mallob/C++ codebase,
  //where it will loop continuously until it can steal some work.
  //If work could be stolen, the worklist will be allocated by Mallob/C++,
  //and here we only operate on it within the provided allocation.
  //We thus also trust Mallob/C++ that it won't deallocate this worklist as long as we operate on it.
  if (solver->shweep_search_work_callback) {
    solver->shweep_search_work_callback(solver->shweep_mallob_SweepJobState, &sweeper->work, &stolen_amount, sweeper->localId);
  }
  assert((stolen_amount>=0 && stolen_amount <= 2*VARS) || kissat_custom_assert_message (solver, "ERROR: stolen amount %i is negative or too big \n", stolen_amount));
  if (stolen_amount>0) {
    kissat_custom_message (solver, V3_VVERB_SWEEP, "stole %i", stolen_amount);
  }
  const unsigned *work = sweeper->work;
  //mark all variables that we have stolen as to-sweep
  flags *flags = solver->flags;
  for (int i=0; i<stolen_amount; i++) {
    flags[work[i]].sweep = true;
  }
  sweeper->work_head = 0;
  sweeper->work_end = stolen_amount;
  sweeper->max_work_after_steal = stolen_amount;
  return sweeper->work_end;
}

//check here whether a variable can be swept at all
//We do not check for FLAGS->sweep, because variables can arrive here also from resweeping,
//where they might not be marked with the "to be swept" flag, yet we want to sweep them now
bool shweep_sweepable_variable(sweeper *sweeper, unsigned idx) {
  kissat *solver = sweeper->solver;
  assert(idx!=INVALID_IDX || kissat_custom_assert_message (solver, "Sweeper ERROR : invalid idx %u was schedulded for sweeping ", idx));
  if (!ACTIVE (idx))
    return false;
  const unsigned lit = LIT (idx);
  if (sweeper->reprs[lit] != lit)
    return false;
  size_t occ;
  if (!scheduable_variable (sweeper, idx, &occ)) {
    FLAGS (idx)->sweep = false;
    return false;
  }
  return true;
}


//Wrapper around kissats 'sweep_variable' method to allow immediate custom resweeping
//in MallobSweep. Though, by default we have resweeping deactivated now,
//so currently this wrapper is needlessly complex for the default behaviour.
void shweep_sweep_variable_with_prop(sweeper *sweeper, unsigned idx, bool isWorkVar) {
  kissat *solver = sweeper->solver;
  bool is_work_var = isWorkVar;
  //Recurse immediately on resweep variables, implemented via an iterative stack
  for (;;) {
    if (solver->shweep_end_job_signal) {
      kissat_custom_message (solver, V1_INFO_SWEEP, "Sweeper break out of sweep_with_prop (endjob) @ %.3f", shweep_wallclock(solver));
      break;
    }
    if (solver->shweep_end_iteration_signal) {
      kissat_custom_message (solver, V1_INFO_SWEEP, "Sweeper break out of sweep_with_prop (enditer) @ %.3f", shweep_wallclock(solver));
      break;
    }
    if (solver->termination.flagged) break;
    if (solver->inconsistent)        break;
    shweep_do_EU_imports (solver);
    if (shweep_sweepable_variable(sweeper, idx)) {
      shweep_do_EU_imports (solver);
      kissat_custom_message(solver, V3_VVERB_SWEEP,
                            "sweeping idx %u [%i=head, %i max left]",
                            idx, sweeper->work_head, sweeper->max_work_after_steal);
      //Variables can be swept either because it is their turn in the work schedule (worksweep)
      //or because they were part of a recent found equivalence
      //and we want to make further progress around them (resweep)
      //track the different cases via counters
      if (is_work_var) {
        assert(FLAGS(idx)->sweep || kissat_custom_assert_message(solver, "SWEEPER ERROR: scheduled work-var whose but its flag is already sweep==false \n"));
        solver->shweep.progress_work_sweeps++;
      } else {
        if (FLAGS(idx)->sweep)
          solver->shweep.progress_work_sweeps++;
        else
          solver->shweep.progress_unsched_resweeps++;
      }
      FLAGS(idx)->sweep = false;
      //Actual sweep call we are wrapping around
      sweep_variable(sweeper, idx);
    }
    if (EMPTY_STACK(sweeper->RESWEEP))
      break;
    idx         = POP_STACK(sweeper->RESWEEP);
    is_work_var = false;
  }
}

//Replace kissats original scheduling by choosing the next variable from the worklist
unsigned shweep_next_scheduled(sweeper *sweeper) {
  unsigned *work = sweeper->work;
  const int end  = sweeper->work_end;
  while (sweeper->work_head < end) {
    unsigned idx = work[sweeper->work_head];
    sweeper->work_head++;
    sweeper->max_work_after_steal = MIN(sweeper->max_work_after_steal, end - sweeper->work_head);
    if (idx==INVALID_IDX) //there is no work in this slot anymore, was stolen by somebody else
      continue;
    if (shweep_var_still_open(sweeper, idx)) {
      return idx;
    }
    sweeper->solver->shweep.progress_work_stepovers++;
  }
  return INVALID_IDX;
}

void shweep_terminate(kissat *solver) {
  kissat_terminate(solver);
  kissat_custom_message(solver, V2_VERB_SWEEP, "SWEEPER received termination signal");
}

bool kissat_is_inconsistent (kissat *solver) {
  return solver->inconsistent;
}

unsigned shweep_get_num_vars(kissat *solver) {
  return solver->vars;
}

struct shweep_statistics shweep_get_statistics (kissat * solver) {
  //some statistics are updated live incremental during the sweeping
  //others are now added here
  solver->shweep.sweep_eqs      = solver->statistics.sweep_equivalences;
  solver->shweep.sweep_units    = solver->statistics.sweep_units;
  solver->shweep.local_iteration = solver->shweep_local_iteration;
  solver->shweep.curr_active    = solver->active;
  solver->shweep.curr_units     = SIZE_STACK(solver->units);
  solver->shweep.curr_eliminated= SIZE_STACK(solver->eliminated);
  solver->shweep.clauses        = CLAUSES;
  solver->shweep.binirr         = BINIRR_CLAUSES;
  solver->shweep.kitten_calls   = solver->statistics.sweep_solved;
  return solver->shweep;
}

bool is_nonroot_nonzero(kissat *solver) {
  return ((! GET_OPTION (mallob_is_root)) || !(GET_OPTION (mallob_local_id)==0));
}

bool is_localid_nonzero(kissat *solver) {
  return GET_OPTION (mallob_local_id) != 0;
}

void shweep_print_import_statistics(kissat *solver) {
  #define VX_STATS V2_VERB_SWEEP
  kissat_custom_message(solver, VX_STATS, "--------------");
  kissat_custom_message(solver, VX_STATS, "IMPORT EQS Useful     %i / %i ", solver->shweep.eqs_useful, solver->shweep.eqs_seen);
  kissat_custom_message(solver, VX_STATS, "IMPORT EQS Unitprop   %i", solver->shweep.eqs_unitprop);
  kissat_custom_message(solver, VX_STATS, "IMPORT EQS Doublefixd %i", solver->shweep.eqs_skipped_doublefixed);
  kissat_custom_message(solver, VX_STATS, "IMPORT EQS Known      %i", solver->shweep.eqs_skipped_known);
  kissat_custom_message(solver, VX_STATS, "--------------");
  kissat_custom_message(solver, VX_STATS, "IMPORT UNITS Useful     %i / %i", solver->shweep.units_useful, solver->shweep.units_seen);
  kissat_custom_message(solver, VX_STATS, "IMPORT UNITS Fixed      %i", solver->shweep.units_skipped_fixed);
  kissat_custom_message(solver, VX_STATS, "IMPORT UNITS Transitive %i", solver->shweep.units_transitive);
  kissat_custom_message(solver, VX_STATS, "--------------");
  kissat_custom_message(solver, VX_STATS, "Stumbled Units          %i", solver->shweep.stumbled_units);
  kissat_custom_message(solver, VX_STATS, "Detected early un-sat   %i", solver->shweep.detected_early_unsat);
  kissat_custom_message(solver, VX_STATS, "Maxxed kittens         %i", solver->shweep.maxxed_kittens);
}

void shweep_print_var_stats(kissat *solver, int verb) {
  if (is_localid_nonzero (solver))
    return;
  kissat_custom_message(solver, verb, "SWEEPER VARS total %i, active %i, units %i, eliminated %i , CLAUSES irr+binary %i, Import stacksize %i", solver->vars,
    solver->active, SIZE_STACK(solver->units), SIZE_STACK(solver->eliminated),solver->statistics.clauses_irredundant + solver->statistics.clauses_binary, SIZE_STACK(solver->import));
}

bool kissat_sweep (kissat *solver) {
  if (!GET_OPTION (sweep))
    return false;
  if (solver->inconsistent)
    return false;
  if (TERMINATED (sweep_terminated_7))
    return false;
  if (DELAYING (sweep))
    return false;
  assert (!solver->level);
  assert (!solver->unflushed);
  START (sweep);
  INC (sweep);
  statistics *statistics = &solver->statistics;
  uint64_t equivalences = statistics->sweep_equivalences;
  uint64_t units = statistics->sweep_units;
  sweeper sweeper;
  init_sweeper (solver, &sweeper);
  const unsigned scheduled = schedule_sweeping (&sweeper);
  uint64_t swept = 0, limit = 10;
  for (;;) {
    if (solver->inconsistent)
      break;
    if (TERMINATED (sweep_terminated_8))
      break;
    if (solver->statistics.kitten_ticks > sweeper.limit.ticks)
      break;
    if (GET_OPTION (puresweep) && GET_OPTION (puresweep_timelim)>0 &&  kissat_time (solver) > GET_OPTION (puresweep_timelim)) {
        kissat_custom_message (solver, V1_INFO_SWEEP, "Puresweep exit iteration due to time limit %zu", GET_OPTION (puresweep_timelim));
        break;
    }
    unsigned idx = next_scheduled (&sweeper);
    if (idx == INVALID_IDX)
      break;
    FLAGS (idx)->sweep = false;
#ifndef QUIET
    const char *res =
#endif
        sweep_variable (&sweeper, idx);
    kissat_extremely_verbose (
        solver, "swept[%" PRIu64 "] external variable %d %s", swept,
        kissat_export_literal (solver, LIT (idx)), res);
    if (++swept == limit) {
      kissat_very_verbose (solver,
                           "found %" PRIu64 " equivalences and %" PRIu64
                           " units after sweeping %" PRIu64 " variables ",
                           statistics->sweep_equivalences - equivalences,
                           solver->statistics.sweep_units - units, swept);
      limit *= 10;
    }
  }
  kissat_very_verbose (solver, "swept %" PRIu64 " variables", swept);
  equivalences = statistics->sweep_equivalences - equivalences,
  units = solver->statistics.sweep_units - units;
  kissat_phase (solver, "sweep", GET (sweep),
                "found %" PRIu64 " equivalences and %" PRIu64 " units",
                equivalences, units);
  unschedule_sweeping (&sweeper, swept, scheduled);
  unsigned inactive = release_sweeper (&sweeper);
  if (!solver->inconsistent) {
    solver->propagate = solver->trail.begin;
    kissat_probing_propagate (solver, 0, true);
  }

  uint64_t eliminated = equivalences + units;
#ifndef QUIET
  assert (solver->active >= inactive);
  solver->active -= inactive;
  REPORT (!eliminated, '=');
  solver->active += inactive;
#else
  (void) inactive;
#endif
  if (kissat_average (eliminated, swept) < 0.001)
    BUMP_DELAY (sweep);
  else
    REDUCE_DELAY (sweep);
  STOP (sweep);
  return eliminated;
}

static void kissat_puresweep_report(kissat *solver, const char *prefix, unsigned active_before, int iteration) {
  kissat_custom_message(solver, V2_VERB_SWEEP, "%s_ITER    %i", prefix, iteration);
  kissat_custom_message(solver, V2_VERB_SWEEP, "%s_TIME    %.2f", prefix, kissat_time(solver));
  kissat_custom_message(solver, V2_VERB_SWEEP, "%s_FIXED   %i",   prefix, solver->vars - solver->active);
  kissat_custom_message(solver, V2_VERB_SWEEP, "%s_ACTIVE  %i",   prefix, solver->active);
  kissat_custom_message(solver, V2_VERB_SWEEP, "%s_CLAUSES %i",   prefix, CLAUSES);
  kissat_custom_message(solver, V2_VERB_SWEEP, "%s maxxedKittens: %i",   prefix, solver->shweep.maxxed_kittens);
  kissat_custom_message(solver, V2_VERB_SWEEP, "%s new fixed variables: %i",   prefix, active_before - solver->active);
}

//The implementation of single-core (1-core) MallobSweep, directly in Kissat
int kissat_pure_sequential_sweeping(kissat *solver) {
  assert(GET_OPTION (puresweep) || kissat_custom_assert_message (
    solver, "Kissat ERROR : entered pure sweeping without the flag set"));
  if (!kissat_initially_propagate (solver)) {
    assert (solver->inconsistent);
    return 20;
  }
  kissat_puresweep_report (solver, "START", VARS, -1);
  solver->probing=true;
  unsigned active_start = solver->active;
  //Start with CCC
  if (kissat_congruence (solver)) {
    kissat_substitute (solver, true);
  }
  kissat_puresweep_report (solver, "CONGR", active_start, 0);
  solver->shweep.maxxed_kittens=0;
  //Now loop over sweep iterations
  for (int i=1; i<=GET_OPTION (puresweep_iterations); i++) {
    solver->shweep_local_iteration++;
    unsigned active_vars_before_iter = solver->active;
    kissat_custom_message (solver, V2_VERB_SWEEP, "start iteration %i ", i);
    kissat_sweep(solver);
    kissat_substitute(solver, true);
    kissat_puresweep_report (solver, "SWEEP", active_vars_before_iter, i);
    if (solver->inconsistent) {
      kissat_custom_message (solver, V1_INFO_SWEEP, "SWEEP found UNSAT !", i, solver->active);
      break;
    }
    if (GET_OPTION (puresweep_timelim)!=0) {
      if (kissat_time (solver) > GET_OPTION (puresweep_timelim)) {
        kissat_custom_message (solver, V1_INFO_SWEEP, "Puresweep exit global loop due to time limit %zu", GET_OPTION (puresweep_timelim));
        break;
      }
    }
  }
  //Pure sweeping is finished, now leaving the binary.
  //To skip all other steps in search.c, we report anything but 0.
  //i.e. a hacky report of 10 in case no progress was made...
  //this specific sequential path/call was only ever used with UNSAT MITER instances, so leave for now experimental
  if (solver->inconsistent)
    return 20;
  if (solver->active < active_start)
    return 40;
  return 10;
}


bool shweep_has_sweeper_obj(kissat *solver) {
  return solver->sweeper;
}


unsigned long shweep_kitten_propagations(kissat *solver) {
  return solver->statistics.kitten_propagations;
}

const char *shweep_get_profilename(kissat *solver) {
  //Allows Mallob to inquire in which profile we are currently in.
  //Not mutex safe, but only a read, and we only use it for debugging.
  return TOP_STACK(solver->profiles.stack)->name;
}

double shweep_wallclock(kissat *solver) {
  return kissat_wall_clock_time () - solver->shweep_t0;
}

void shweep_set_wallclock_offset(kissat *solver, double offset) {
  solver->shweep_t0 = offset;
}

void shweep_do_EU_imports(kissat *solver) {
  //In case the sweep job is ended, only the representative solver
  //needs to import the last sharing data, as its database is eventually forwarded to Mallob
  //as the result of the MallobSweep app
  if (solver->shweep_end_job_signal && !solver->shweep_report_finished_iteration_callback) {
    return;
  }
  shweep_import_SweepJob_units (solver->sweeper);
  shweep_import_SweepJob_equivalences (solver->sweeper);
}

void shweep_stop_iteration(kissat *solver) {
  //Hijack the tick limit counter to immediately exit all nested sweep functions
  //Do the same for kitten
  if (solver->sweeper) {
    solver->sweeper->limit.ticks = 0;
  } else {
    kissat_custom_message (solver, V1_INFO_SWEEP, "no sweeper object");
  }
  if (solver->kitten) {
    set_kitten_ticks_limit (solver->sweeper);
  } else {
    kissat_custom_message (solver, V1_INFO_SWEEP, "no kitten object");
  }
}

void shweep_set_end_iteration_signal(kissat *solver) {
  solver->shweep_end_iteration_signal = true;
  shweep_stop_iteration (solver);
  kissat_custom_message (solver, V2_VERB_SWEEP, "SWEEPER received end_iteration signal!");
}

void shweep_set_end_job_signal(kissat *solver) {
  solver->shweep_end_job_signal = true;
  shweep_stop_iteration (solver);
  kissat_custom_message (solver, V1_INFO_SWEEP, "SWEEPER received end_sweepjob signal! limit.ticks=0. @ %.3f", shweep_wallclock (solver));
}


bool shweep_get_end_iteration_signal(kissat *solver) {
  return solver->shweep_end_iteration_signal;
}

bool shweep_get_end_job_signal(kissat *solver) {
  return solver->shweep_end_job_signal;
}

int shweep_get_curr_iteration(kissat *solver) {
  return solver->shweep_local_iteration;
}

void shweep_set_global_iteration(kissat *solver, int global_iteration) {
  solver->shweep.global_iteration = global_iteration;
}


int mallob_shweep_single_iteration(kissat *solver) {
  kissat_custom_message(solver,V2_VERB_SWEEP, "SWEEPER Start new iteration %i", solver->shweep_local_iteration);
  if (!GET_OPTION (mallob_sweeping)) {
    kissat_custom_message(solver,V1_INFO_SWEEP, "SWEEPER WARN : mallob_sweeping is false, but are in shweep_single_iteration");
    return false;
  }
  if (solver->inconsistent) {
    kissat_custom_message(solver,V1_INFO_SWEEP, "SWEEPER directly UNSAT. not even starting loop");
    return false;
  }
  if (TERMINATED (sweep_terminated_7))
    return false;
  assert (!solver->level);
  assert (!solver->unflushed);
  START (sweep);
  INC (sweep);
  statistics *statistics = &solver->statistics;
  uint64_t equivalences = statistics->sweep_equivalences;
  uint64_t units = statistics->sweep_units;
  sweeper sweeper;
  init_sweeper (solver, &sweeper);
  for (;;) {
    if (solver->inconsistent) {
      kissat_custom_message(solver,V1_INFO_SWEEP, "SWEEPER found UNSAT! (in sweep work loop)");
      break;
    }
    if (TERMINATED (sweep_terminated_8)) {
      kissat_custom_message(solver,V0_CRIT_SWEEP, "Sweeper WARN : exiting sweep loop due to termination.flagged instead of end_iteration !!\n");
      break;
    }
    if (solver->shweep_local_iteration < solver->shweep.global_iteration) {
      kissat_custom_message(solver,V1_INFO_SWEEP, "local iteration outdated, %i vs %i", solver->shweep_local_iteration, solver->shweep.global_iteration);
      break;
    }
    if (solver->statistics.kitten_ticks > sweeper.limit.ticks) {
      kissat_custom_message(solver,V1_INFO_SWEEP, "kitten tick limit -> exit iteration");
      break;
    }
    if (solver->shweep_end_job_signal) {
      kissat_custom_message(solver,V1_INFO_SWEEP, "Sweeper : exiting sweeping loop (endjob) @ %.3f",shweep_wallclock (solver));
      break;
    }
    if (solver->shweep_end_iteration_signal) {
      kissat_custom_message(solver,V1_INFO_SWEEP, "SWEEPER exiting sweeping loop (enditer) @ %.3f", shweep_wallclock (solver));
      break;
    }
    unsigned idx = shweep_next_scheduled (&sweeper);
    if (solver->shweep_end_job_signal) {
      kissat_custom_message(solver,V1_INFO_SWEEP, "Sweeper : got next scheduled (while endjob) @ %.3f",shweep_wallclock (solver));
    }
    shweep_do_EU_imports (solver);
    if (idx == INVALID_IDX) {
      //we have no more work, try to steal from somebody else
      shweep_search_work_from_others (&sweeper);
      if (solver->shweep_end_job_signal) {
        kissat_custom_message(solver,V1_INFO_SWEEP, "Sweeper : exit search work (while endjob) @ %.3f", shweep_wallclock (solver));
      }
    }
    else {
      shweep_sweep_variable_with_prop (&sweeper, idx, true);
    }
  }

  //immediately reset these, to prevent that they linger for the next sharing round
  solver->shweep_end_iteration_signal = false;
  solver->shweep.progress_work_sweeps=0;
  solver->shweep.progress_work_stepovers=0;
  solver->shweep.progress_unsched_resweeps=0;
  // kissat_custom_message (solver, V2_VERB_SWEEP, "Sweeper END single iteration loop");
  //since we are soon deallocating this sweeper,
  //prevent already now other solvers from stealing,
  //as a badly-timed steal access would lead to a segfault
  solver->shweeper_allows_stealing = false;
  //at the very end of a SweepJob there exist some Eqs and Units to
  //import from the last sharing round which brought the termination signal
  //for the representative solver we want to also have those
  //update: no longer import at the end of an iteration, can lead to stalls
  // shweep_do_EU_imports (solver);

  equivalences = statistics->sweep_equivalences - equivalences,
  units = solver->statistics.sweep_units - units;
  kissat_phase (solver, "sweep", GET (sweep), "found %" PRIu64 " equivalences and %" PRIu64 " units", equivalences, units);
  kissat_custom_message (solver, V2_VERB_SWEEP,
    "SWEEP this round: E %i, U %i, E+U %i   Cumulative: E %i, U %i, E+U %i ",
    equivalences, units, equivalences+units, statistics->sweep_equivalences, statistics->sweep_units, statistics->sweep_equivalences + statistics->sweep_units);

  //Some other solver might be stealing from us right now (accessing our work array),
  //so we can not just immediately release / deallocate ourselves
  //This can happen especially if a new iteration just started
  //and this solver both quickly finds UNSAT, but also already has another solver
  //stealing a large amount of work (which takes some time), and UNSAT falls right
  //within this stealing process
  while (sweeper.somebody_is_stealing_from_me) {
    kissat_custom_message(solver,V1_INFO_SWEEP, "Guard solver release - another solver is still stealing from us @ %.3f", shweep_wallclock (solver));
    usleep (5000);
  }
  unsigned inactive = release_sweeper (&sweeper);
  //dont need to unschedule because we also never scheduled
  if (!solver->inconsistent) {
    kissat_custom_message(solver,V2_VERB_SWEEP, "propagating");
    solver->propagate = solver->trail.begin;
    kissat_probing_propagate (solver, 0, true);
  }
  uint64_t eliminated = equivalences + units;
#ifndef QUIET
  assert (solver->active >= inactive);
  solver->active -= inactive;
  REPORT (!eliminated, '=');
  solver->active += inactive;
#else
  (void) inactive;
#endif
  STOP (sweep);
  if (solver->inconsistent)
    kissat_custom_message (solver, V1_INFO_SWEEP, "SWEEPER found UNSAT! (exit single iter method)");
  return eliminated;
}

//Report to Mallob about the current Solver state
//only the representative solver at the root node reports this
void representative_report_finished_iteration(kissat *solver) {
  if (solver->shweep_report_finished_iteration_callback) {
    solver->shweep_report_finished_iteration_callback (solver->shweep_mallob_SweepJobState, GET_OPTION (mallob_local_id));
  }
}

bool shweep_is_representative(kissat *solver) {
  return solver->shweep_report_finished_iteration_callback;
}

int kissat_mallob_distributed_sweep_multiple_iterations(kissat *solver) {
  kissat_custom_message (solver, V1_INFO_SWEEP, "kissat sweep main");
  solver->shweep_t0 += kissat_wall_clock_time ();
  if (!kissat_initially_propagate (solver)) {
    assert (solver->inconsistent);
    kissat_custom_message (solver, V1_INFO_SWEEP, "SWEEPER found directly UNSAT in initial propagation");
    return 20;
  }
  solver->shweep.maxxed_kittens=0;
  solver->shweep.signalskipped_kittens=0;
  solver->shweep.kitten_calls=0;
  solver->shweep.global_iteration=0;
  solver->shweep_end_iteration_signal=false;
  solver->shweep_end_job_signal=false;

  solver->probing = true;
  solver->shweep.orig_vars = solver->vars;
  solver->shweep.start_units   = SIZE_STACK(solver->units);
  solver->shweep.start_active  = solver->active;
  solver->shweep.start_clauses = CLAUSES;
  solver->shweep.start_binirr  = BINIRR_CLAUSES;
  solver->shweep_local_iteration = -1; //-1 before any CEC algos started, 0 in congruence, 1..n in sweep
  if (shweep_is_representative (solver)) {
    kissat_custom_message (solver, V1_INFO_SWEEP, "SWEEPER orig vars : %i", solver->shweep.orig_vars);
    kissat_custom_message (solver, V1_INFO_SWEEP, "SWEEPER start units: %i", solver->shweep.start_units);
    kissat_custom_message (solver, V1_INFO_SWEEP, "SWEEPER start activ: %i", solver->shweep.start_active);
    kissat_custom_message (solver, V1_INFO_SWEEP, "SWEEPER start CLAUSES: %i", CLAUSES);
    kissat_custom_message (solver, V1_INFO_SWEEP, "SWEEPER start BINIRR : %i", BINIRR_CLAUSES);
  }

  //Report the state before CCC and Sweeping. Reported as iteration -1
  representative_report_finished_iteration (solver);

  //Do CCC once at the start, every solver for itself. Reported as iteration 0
  solver->shweep_local_iteration++;
  if (GET_OPTION (mallob_initial_congruence)) {
    if (kissat_congruence (solver)) {
      if (!solver->shweep_end_job_signal || shweep_is_representative (solver)) {
        kissat_substitute (solver, true);
      }
    }
    representative_report_finished_iteration (solver);
  }
  kissat_custom_message (solver, V1_INFO_SWEEP, "finished CCC");
  //Sweeping
  while (!solver->shweep_end_job_signal && !solver->inconsistent) {
    solver->shweep_local_iteration++;
    //One sweep iteration
    //Track that now we no longer do internal work, but communicate with others
    unsigned active_before = solver->active;
    mallob_shweep_single_iteration (solver);
    //Burn the new equivalences into the local clause database
    //Track that Substitute is again internal work, independent of others
    if (solver->active != active_before) {
      if (!solver->shweep_end_job_signal || shweep_is_representative (solver)) {
        const double t = shweep_wallclock (solver);
        kissat_custom_message (solver, V2_VERB_SWEEP, "substituting");
        kissat_substitute(solver, true);
        kissat_custom_message (solver, V2_VERB_SWEEP, "substitute time: %.3f", shweep_wallclock (solver) - t);
      }
    }
    //Now, after database is up-to-date, can report metrics of this iteration
    representative_report_finished_iteration (solver);
    //increase the environment size of the next iteration
    INC(sweep_completed);
  }
  shweep_print_import_statistics(solver);
  kissat_custom_message (solver, V1_INFO_SWEEP, "SWEEPER ENDED, now triggering own termination @ %.3f", shweep_wallclock (solver));
  kissat_terminate (solver);
  return solver->inconsistent ? 20 : 0 ;
}
