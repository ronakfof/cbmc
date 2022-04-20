/*******************************************************************\

Module: Axioms

Author:

\*******************************************************************/

/// \file
/// Axioms

#include "axioms.h"

#include "state.h"

void axioms_node(const exprt &src, decision_proceduret &dest)
{
  if(src.id() == ID_state_is_cstring)
  {
    // is_cstring(ς, X) ⇒ r_ok(ς, X)
  }
}

void axioms(const exprt &src, decision_proceduret &dest)
{
  src.visit_post([&dest](const exprt &src) {
    axioms_node(src, dest);
  });
}
