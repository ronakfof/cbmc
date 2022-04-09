/*******************************************************************\

Module: Propagate

Author:

\*******************************************************************/

/// \file
/// Propagate

#ifndef CPROVER_CPROVER_PROPAGATE_H
#define CPROVER_CPROVER_PROPAGATE_H

#include "solver_types.h"

#include <unordered_set>

enum class propagate_resultt
{
  PROPAGATED,
  CONFLICT
};

propagate_resultt propagate(
  std::vector<framet> &,
  const workt &,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &,
  const std::function<void(const symbol_exprt &, exprt)> &propagator);

#endif // CPROVER_CPROVER_PROPAGATE_H
