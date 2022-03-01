/*******************************************************************\

Module: Solver

Author:

\*******************************************************************/

/// \file
/// May Alias

#ifndef CPROVER_CPROVER_MAY_ALIAS_H
#define CPROVER_CPROVER_MAY_ALIAS_H

#include <util/expr.h>

class namespacet;

bool permitted_by_strict_aliasing(const typet &, const typet &);

bool is_object_field_element(const exprt &);

exprt simple_may_alias(const exprt &, const exprt &, const namespacet &);

#endif // CPROVER_CPROVER_MAY_ALIAS_H
