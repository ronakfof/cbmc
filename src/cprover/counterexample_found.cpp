/*******************************************************************\

Module: Counterexample Found

Author:

\*******************************************************************/

/// \file
/// Counterexample Found

#include "counterexample_found.h"

#include <util/cout_message.h>
#include <util/format_expr.h>
#include <util/simplify_expr.h>

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>

#include "state.h"

#include <iostream>

bool counterexample_found(
  const std::vector<framet> &frames,
  const workt &work,
  const namespacet &ns)
{
  auto &f = frames[work.frame.index];

  for(const auto &implication : f.implications)
  {
    if(implication.lhs.is_true())
    {
      // these are initial states, i.e., true ⇒ SInitial(ς)
      auto cond_replaced = replace_evaluate(work.invariant);
      std::cout << "CE: " << format(cond_replaced) << "\n";

      // ask the solver whether the invariant is 'true'
      cout_message_handlert message_handler;
      satcheckt satcheck(message_handler);
      bv_pointerst solver(ns, satcheck, message_handler);
      solver.set_to_false(cond_replaced);
      switch(solver())
      {
      case decision_proceduret::resultt::D_SATISFIABLE:
        return true;
      case decision_proceduret::resultt::D_UNSATISFIABLE:
        break;
      case decision_proceduret::resultt::D_ERROR:
        throw "error reported by solver";
      }
    }
  }

  return false;
}
