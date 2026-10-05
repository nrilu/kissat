#include "internal.h"
#include "inline.h"
#include "utilities.h"
#include "print.h"

void kissat_export_redundant_clause (kissat * solver, unsigned glue, unsigned size, unsigned *lits) {
  if (!solver->consume_clause) return;
  if (size > solver->consume_clause_max_size) return;
  glue = MAX(glue, 1);
  glue = MIN(glue, size-1);
  // Export clause.
  for (unsigned i = 0; i < size; i++) {
    // Externalize each literal
    const unsigned ilit = lits[i];
    const int elit = kissat_export_literal (solver, ilit);
    solver->consume_clause_buffer[i] = elit;
  }
  // Execute learnt clause callback
  solver->consume_clause (solver->consume_clause_state, size, glue);
}

void kissat_export_redundant_binary (kissat * solver, unsigned lit, unsigned other) {
  unsigned lits[2] = {lit, other};
  kissat_export_redundant_clause (solver, 1, 2, lits);
}


void shweep_export_equivalence(kissat *solver, unsigned lit, unsigned other) {
  if (!solver->shweep_export_eq_callback) return;
  if (solver->inconsistent) {
    kissat_custom_message (solver, 1, "Sweeper: Prevented eq export after having found UNSAT");
    return;
  }
  //Dont have any variable deletion/addition/renaming in shweep,
  //so we can directly work with internal literals, no need to convert to external representation
  //  Update: Now switche to externalizing literals because we need this generality for Cross-Job-Communication
  int elit = kissat_export_literal (solver, lit);
  int eother = kissat_export_literal (solver, other);
  //bring all equivalences in a normal form (smaller index first), to allow stricter assertions and easier duplicate detection
  if (abs(elit) > abs(eother)) {
    int tmp = elit;
    elit = eother;
    eother = tmp;
  }
  assert(abs(elit)<abs(eother) || kissat_custom_assert_message (solver, "ERROR in Sweep Export: Invariant abs(elit)<abs(eother) violated. %i , %i\n",abs(elit),abs(eother)));

  // kissat_custom_message (solver, 1, "export: i(%i,%i) -> e{%i,%i}",lit,other,elit,eother);
  solver->shweep_export_eq_buffer[0] = elit;
  solver->shweep_export_eq_buffer[1] = eother;
  solver->shweep_export_eq_callback (solver->shweep_mallob_KissatState);
}

void shweep_export_unit(kissat *solver, unsigned lit) {
  if (!solver->shweep_export_unit_callback) return;
  if (solver->inconsistent) {
    kissat_custom_message (solver, 1, "Sweeper: Prevented unit export after having found UNSAT");
    return;
  }
  int elit = kissat_export_literal (solver, lit);
  // kissat_custom_message (solver, 1, "export: i(%i) -> e{%i}",lit,elit);
  solver->shweep_export_unit_callback (solver->shweep_mallob_KissatState, elit);
}
