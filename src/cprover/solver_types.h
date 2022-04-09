/*******************************************************************\

Module: Solver

Author:

\*******************************************************************/

/// \file
/// Solver

#ifndef CPROVER_CPROVER_SOLVER_TYPES_H
#define CPROVER_CPROVER_SOLVER_TYPES_H

#include <util/mathematical_expr.h>
#include <util/std_expr.h>

#include <unordered_map>

class frame_reft
{
public:
  frame_reft() : index(0)
  {
  }
  explicit frame_reft(std::size_t __index) : index(__index)
  {
  }
  std::size_t index;
  friend bool operator==(const frame_reft &a, const frame_reft &b)
  {
    return a.index == b.index;
  }
};

using frame_mapt = std::unordered_map<symbol_exprt, frame_reft, irep_hash>;

class framet
{
public:
  framet(symbol_exprt _symbol, frame_reft __ref)
    : symbol(std::move(_symbol)), ref(std::move(__ref))
  {
  }

  symbol_exprt symbol;

  // our current hypothesis invariant
  std::vector<exprt> invariants;

  // auxiliary facts
  std::vector<exprt> auxiliaries;

  // formulas where this frame is on the rhs of ⇒
  struct implicationt
  {
    implicationt(exprt __lhs, function_application_exprt __rhs)
      : lhs(std::move(__lhs)), rhs(std::move(__rhs))
    {
    }
    exprt lhs;
    function_application_exprt rhs;
  };

  std::vector<implicationt> implications;

  void add_invariant(exprt);
  void add_auxiliary(exprt);

  void reset()
  {
    invariants.clear();
    auxiliaries.clear();
  }

  frame_reft ref;
};

class propertyt
{
public:
  propertyt(
    source_locationt __source_location,
    frame_reft __frame,
    exprt __condition)
    : source_location(std::move(__source_location)),
      frame(std::move(__frame)),
      condition(std::move(__condition))
  {
  }

  // formulas where this frame is on the lhs of ⇒
  source_locationt source_location;
  frame_reft frame;
  exprt condition;

  using statust = enum { UNKNOWN, PASS, REFUTED, ERROR };
  statust status = UNKNOWN;
};

struct workt
{
  workt(frame_reft __frame, exprt __invariant)
    : frame(std::move(__frame)), invariant(std::move(__invariant))
  {
  }
  frame_reft frame;
  exprt invariant;
};

#endif // CPROVER_CPROVER_SOLVER_TYPES_H