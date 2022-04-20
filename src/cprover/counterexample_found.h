/*******************************************************************\

Module: Counterexample Found

Author:

\*******************************************************************/

/// \file
/// Counterexample Found

#ifndef CPROVER_CPROVER_COUNTEREXAMPLE_FOUND_H
#define CPROVER_CPROVER_COUNTEREXAMPLE_FOUND_H

#include "solver_types.h"

#include <unordered_set>

bool counterexample_found(
  const std::vector<framet> &,
  const workt &,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &);

class bv_pointerst;

void show_assignment(const bv_pointerst &);

#endif // CPROVER_CPROVER_COUNTEREXAMPLE_FOUND_H
