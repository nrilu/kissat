#ifndef QUIET

#include "internal.h"
#include "resources.h"
#include "sort.h"

#include <stdio.h>
#include <string.h>
#include <pthread.h>

void kissat_init_profiles (profiles *profiles) {
#define PROF(NAME, LEVEL) profiles->NAME = (profile){LEVEL, #NAME, 0, 0};
  PROFS
#undef PROF
  pthread_mutex_init(&profiles->mtx, 0);
}

#define SIZE_PROFS (sizeof (profiles) / sizeof (profile))

static inline bool less_profile (profile *p, profile *q) {
  if (p->time > q->time)
    return true;
  if (p->time < q->time)
    return false;
  return strcmp (p->name, q->name) < 0;
}

static void print_profile (kissat *solver, profile *p, double total) {
  printf ("%s%14.2f %7.2f %%  %s\n", solver->prefix, p->time,
          kissat_percent (p->time, total), p->name);
}

static void write_profile (profile *p, double total, FILE* f) {
  fprintf (f, "c %14.2f %7.2f %%  %s\n", p->time,
          kissat_percent (p->time, total), p->name);
}

static double flush_profile (profile *profile, double now) {
  const double delta = now - profile->entered;
  profile->time += delta;
  profile->entered = now;
  return delta;
}

static void flush_profiles (profiles *profiles, const double now) {
  for (all_pointers (profile, p, profiles->stack))
    flush_profile (p, now);
}

static void push_profile (kissat *solver, profile *profile, double now) {
  profile->entered = now;
  PUSH_STACK (solver->profiles.stack, profile);
}

void kissat_profiles_print (kissat *solver) {
  pthread_mutex_lock(&solver->profiles.mtx);
  profiles *named = &solver->profiles;
  double now = kissat_wall_clock_time ();
  flush_profiles (named, now);
  profile *unsorted = (profile *) named;
  profile *sorted[SIZE_PROFS];
  const profile *const end = unsorted + SIZE_PROFS;
  size_t size = 0;
  for (profile *p = unsorted; p != end; p++)
    if (p->level <= GET_OPTION (profile) &&
        (p == &named->search || p == &named->simplify ||
         (p != &named->total && p->time)))
      sorted[size++] = p;
  INSERTION_SORT (profile *, size, sorted, less_profile);
  const double total = named->total.time;
  for (size_t i = 0; i < size; i++)
    print_profile (solver, sorted[i], total);
  printf ("%s=============================================\n",
          solver->prefix);
  print_profile (solver, &named->total, total);
  pthread_mutex_unlock(&solver->profiles.mtx);
}

void kissat_write_profile (kissat *solver, const char *path) {
  pthread_mutex_lock(&solver->profiles.mtx);
  profiles *named = &solver->profiles;
  double now = kissat_wall_clock_time ();
  flush_profiles (named, now);
  profile *unsorted = (profile *) named;
  profile *sorted[SIZE_PROFS];
  const profile *const end = unsorted + SIZE_PROFS;
  size_t size = 0;
  for (profile *p = unsorted; p != end; p++)
    if (p->level <= GET_OPTION (profile) &&
        (p == &named->search || p == &named->simplify ||
         (p != &named->total && p->time)))
      sorted[size++] = p;
  INSERTION_SORT (profile *, size, sorted, less_profile);
  const double total = named->total.time;
  FILE* f = fopen(path, "w");
  for (size_t i = 0; i < size; i++)
    write_profile (sorted[i], total, f);
  write_profile (&named->total, total, f);
  pthread_mutex_unlock(&solver->profiles.mtx);
}

void kissat_start (kissat *solver, profile *profile) {
  pthread_mutex_lock(&solver->profiles.mtx);
  const double now = kissat_wall_clock_time ();
  push_profile (solver, profile, now);
  pthread_mutex_unlock(&solver->profiles.mtx);
}

void kissat_stop (kissat *solver, profile *profile) {
  pthread_mutex_lock(&solver->profiles.mtx);
  assert (TOP_STACK (solver->profiles.stack) == profile);
  (void) POP_STACK (solver->profiles.stack);
  const double now = kissat_wall_clock_time ();
  flush_profile (profile, now);
  pthread_mutex_unlock(&solver->profiles.mtx);
}

const char *kissat_get_current_profilename(kissat *solver) {
  pthread_mutex_lock(&solver->profiles.mtx);
  const char* name = EMPTY_STACK(solver->profiles.stack) 
    ? "kissats_profile_stack_is_empty" 
    : TOP_STACK(solver->profiles.stack)->name;
  pthread_mutex_unlock(&solver->profiles.mtx);
  return name;
}

void kissat_stop_search_and_start_simplifier (kissat *solver,
                                              profile *profile) {
  pthread_mutex_lock(&solver->profiles.mtx);
  struct profile *search = &PROFILE (search);
  assert (search->level <= GET_OPTION (profile));
  const double now = kissat_wall_clock_time ();
  while (TOP_STACK (solver->profiles.stack) != search) {
    struct profile *mode = POP_STACK (solver->profiles.stack);
    assert (search->level <= mode->level);
#ifndef NDEBUG
    if (solver->stable)
      assert (mode == &PROFILE (stable));
    else
      assert (mode == &PROFILE (focused));
#endif
    flush_profile (mode, now);
  }
  (void) POP_STACK (solver->profiles.stack);
  struct profile *simplify = &PROFILE (simplify);
  assert (search->level == simplify->level);
  assert (simplify->level <= profile->level);
  flush_profile (search, now);
  push_profile (solver, simplify, now);
  if (profile->level <= GET_OPTION (profile))
    push_profile (solver, profile, now);
  pthread_mutex_unlock(&solver->profiles.mtx);
}

void kissat_stop_simplifier_and_resume_search (kissat *solver,
                                               profile *profile) {
  pthread_mutex_lock(&solver->profiles.mtx);
  struct profile *simplify = &PROFILE (simplify);
  struct profile *top = POP_STACK (solver->profiles.stack);
  const double now = kissat_wall_clock_time ();
  const double delta = flush_profile (simplify, now);
#ifndef NDEBUG
  const double entered = now - delta;
  assert (solver->mode.entered <= entered);
#endif
  solver->mode.entered += delta;
  if (top == profile) {
    flush_profile (profile, now);
    assert (TOP_STACK (solver->profiles.stack) == simplify);
    (void) POP_STACK (solver->profiles.stack);
  } else {
    assert (simplify == top);
    assert (profile->level > GET_OPTION (profile));
  }
#ifndef NDEBUG
  struct profile *search = &PROFILE (search);
  assert (search->level == simplify->level);
#endif
  assert (simplify->level <= profile->level);
  push_profile (solver, &PROFILE (search), now);
  struct profile *mode =
      solver->stable ? &PROFILE (stable) : &PROFILE (focused);
  assert (search->level <= mode->level);
  if (mode->level <= GET_OPTION (profile))
    push_profile (solver, mode, now);
  pthread_mutex_unlock(&solver->profiles.mtx);
}

double kissat_time (kissat *solver) {
  pthread_mutex_lock(&solver->profiles.mtx);
  const double now = kissat_wall_clock_time ();
  flush_profiles (&solver->profiles, now);
  double res = PROFILE (total).time;
  pthread_mutex_unlock(&solver->profiles.mtx);
  return res;
}

#else
int kissat_profile_dummy_to_avoid_warning;
#endif
