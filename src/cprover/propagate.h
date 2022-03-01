/*******************************************************************\

Module: Propagate

Author:

\*******************************************************************/

/// \file
/// Propagate

#ifndef CPROVER_CPROVER_PROPAGATE_H
#define CPROVER_CPROVER_PROPAGATE_H

#include "solver_types.h"

enum class propagate_resultt
{
  PROPAGATED,
  CONFLICT
};

propagate_resultt propagate(
  std::vector<framet> &,
  const workt &,
  const namespacet &,
  const std::function<void(const symbol_exprt &, exprt)> &propagator);

#endif // CPROVER_CPROVER_PROPAGATE_H
