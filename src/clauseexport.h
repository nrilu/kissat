#ifndef _clauseexport_h_INCLUDED
#define _clauseexport_h_INCLUDED

struct kissat;

void kissat_export_redundant_clause (kissat * solver, unsigned glue, unsigned size, unsigned *lits);
void kissat_export_redundant_binary (kissat * solver, unsigned lit, unsigned other);

void shweep_export_equivalence(kissat *solver, unsigned lit, unsigned other);
void shweep_export_unit(kissat *solver, unsigned lit);

#endif