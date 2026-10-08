#ifndef _kissat_h_INCLUDED
#define _kissat_h_INCLUDED

#include <stdbool.h>

typedef struct kissat kissat;

// Default (partial) IPASIR interface.

const char *kissat_signature (void);
kissat *kissat_init (void);
void kissat_add (kissat *solver, int lit);
int kissat_solve (kissat *solver);
int kissat_value (kissat *solver, int lit);
void kissat_release (kissat *solver);

void kissat_set_terminate (kissat *solver, void *state,
                           int (*terminate) (void *state));

// Additional API functions.

void kissat_terminate (kissat *solver);
void kissat_reserve (kissat *solver, int max_var);

const char *kissat_id (void);
const char *kissat_version (void);
const char *kissat_compiler (void);

const char **kissat_copyright (void);
void kissat_build (const char *line_prefix);
void kissat_banner (const char *line_prefix, const char *name_of_app);

int kissat_get_option (kissat *solver, const char *name);
int kissat_set_option (kissat *solver, const char *name, int new_value);

void kissat_set_prefix (kissat *solver, const char *prefix);

int kissat_has_configuration (const char *name);
int kissat_set_configuration (kissat *solver, const char *name);

void kissat_set_conflict_limit (kissat *solver, unsigned);
void kissat_set_decision_limit (kissat *solver, unsigned);

void kissat_print_statistics (kissat *solver);

void kissat_write_profile (kissat *solver, const char *path);

const char *kissat_get_current_profilename(kissat *solver);

// *** API for Mallob ***

// Sets a function to be called whenever kissat learns a clause no longer than the specified max. size.
// The function is called with the provided state and the size and glue value of the learnt clause.
// The clause itself is stored in the provided buffer before the function is called.
void kissat_set_clause_export_callback (kissat * solver, void *state, int *buffer, unsigned max_size, void (*consume) (void *state, int size, int glue));

// Sets a function which kissat may call to import a clause from another solver. The function is called
// with the provided state and expects a literal buffer (or zero), the clause size, and the glue value as out parameters.
// If no clause is available, the function must return clause == 0.
void kissat_set_clause_import_callback (kissat * solver, void *state, void (*produce) (void *state, int **clause, int *size, int *glue, unsigned long *id, unsigned char *sig));


//--------------------------------------------------------------------------
// Sub-API for SWEEP App
void shweep_set_equivalence_export_callback(kissat *solver, void *state, int *buffer, void (*export_callback) (void *state));
void shweep_set_SweepJob_eq_import_callback(kissat *solver, void *SweepJobState, void (*import_eq_callback) (void *SweepJobState, int *lit1, int *lit2, int localId));

void shweep_set_unit_export_callback(kissat *solver, void *state, void (*export_callback) (void *state, int lit));
void shweep_set_SweepJob_unit_import_callback(kissat *solver, void *SweepJobState, void (*import_unit_callback) (void *SweepJobState, int *lit, int localId));

void shweep_set_search_work_callback(kissat *solver, void *SweepJobState, void (*search_callback) (void *SweepJob_state, unsigned **work, int *work_size, int local_id));
void shweep_set_report_finished_iteration_callback(kissat *solver, void *SweepJobState, void (*report_callback) (void *SweepJob_state, int localId));

int shweep_get_work_estimate(kissat *solver);
int shweep_get_max_steal_amount(kissat *solver);
int shweep_steal_from_this_solver(kissat *solver, unsigned *stolen_work, int max_steal_count);
unsigned shweep_get_num_vars (kissat *solver);

void shweep_terminate(kissat *solver);
void shweep_set_end_iteration_signal(kissat *solver);
bool shweep_get_end_iteration_signal(kissat *solver);
void shweep_set_end_job_signal(kissat *solver);
bool shweep_get_end_job_signal(kissat *solver);
int shweep_get_curr_iteration(kissat *solver);
void shweep_do_EU_imports(kissat *solver);
void shweep_set_wallclock_offset(kissat *solver, double offset);
double shweep_wallclock(kissat *solver);
const char *shweep_get_profilename(kissat *solver);
unsigned long shweep_kitten_propagations(kissat *solver);
bool shweep_has_sweeper_obj(kissat *solver);
void shweep_set_global_iteration(kissat *solver, int global_iteration);
bool shweep_is_representative(kissat *solver);

bool kissat_is_inconsistent (kissat *solver);

struct shweep_statistics {
  //importing
  unsigned long eqs_seen, eqs_useful, eqs_skipped_known, eqs_transitive, eqs_unitprop, eqs_skipped_doublefixed;
  unsigned long units_seen, units_useful, units_skipped_fixed, units_transitive;
  unsigned long stumbled_units;
  unsigned long detected_early_unsat;
  //tracking the worklist
  unsigned long progress_work_sweeps;
  unsigned long progress_work_stepovers;
  unsigned long progress_unsched_resweeps;
  //info that already kissat tracks
  unsigned long start_active, orig_vars, start_units;
  unsigned long sweep_eqs, sweep_units, units_new, units_end;
  unsigned long clauses, binirr, start_clauses, start_binirr;
  //the current sweep iteration
  //Counting convention:
  //  -1 = Before ClausalCongruenceClosure (CCC)
  //   0 = After CCC
  //1..n = After sweeping iterations 1..n
  int local_iteration;
  int global_iteration;
  unsigned long curr_active, curr_units, curr_eliminated;
  unsigned long env_limit_depth, env_limit_vars, env_limit_clauses;
  unsigned long maxxed_kittens, signalskipped_kittens, kitten_calls;
};
struct shweep_statistics shweep_get_statistics(kissat *solver);
//--------------------------------------------------------------------------

struct exportmore_statistics {
  unsigned long unit_sweep;
  unsigned long unit_inlineassign;
  
  unsigned long bin_sweep; 
  unsigned long bin_strengthen;
  unsigned long bin_forwardsub;
  unsigned long bin_congruence;
  unsigned long bin_vivify;
  
  unsigned long cls_strengthen;
  unsigned long cls_forwardsub;
  unsigned long cls_vivify;
};
struct exportmore_statistics kissat_get_exportmore_statistics(kissat *solver);

// Basic "external" statistics struct with some interesting properties of kissat's search.
struct kissat_statistics {unsigned long propagations; unsigned long decisions; unsigned long conflicts; unsigned long restarts; 
unsigned long imported; unsigned long discarded; unsigned long r_ee,r_ed,r_pb,r_ss,r_sw,r_tr,r_fx,r_ia,r_tl;};
// Get the statistics of kissat's current search. Not thread-safe, but only reading, i.e., 
// may (rarely) return improper values.
struct kissat_statistics kissat_get_statistics (kissat * solver);

// Provides to kissat an array of variable phase values. lookup[i] corresponds to external variable i 
// and should be 1, -1, or 0. Kissat may lookup this value for a variable and use the sign to decide
// on the variable's initial phase. The array must be valid during the entire search procedure.
void kissat_set_initial_variable_phases (kissat * solver, signed char *lookup, int size);

void kissat_set_preprocessing_report_callback (kissat * solver, void *state,
    bool (*begin_report) (void *state, int vars, int cls),
    void (*report_lit) (void *state, int lit));

void kissat_import_model (kissat * solver, const int *literals, int size);

// TODO get branching literal: use kissat_next_decision_variable in decide.h ?

void kissat_trace_proof_internally (kissat * solver, void *state,
    void (*on_drup_derivation) (void* state, const int* lits, int nbLits, int glue),
    void (*on_lrup_import)     (void* state, unsigned long id, const int* lits, int nbLits, const unsigned char* sigData),
    void (*on_drup_deletion)   (void* state, const int* lits, int nbLits));

#endif
