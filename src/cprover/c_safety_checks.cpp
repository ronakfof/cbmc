/*******************************************************************\

Module: Checks for Errors in C/C++ Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Checks for Errors in C/C++ Programs

#include "c_safety_checks.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/options.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>

#include <goto-programs/goto_model.h>

#include <ansi-c/expr2c.h>

exprt index_array_size(const typet &type)
{
  if(type.id() == ID_array)
    return to_array_type(type).size();
  else if(type.id() == ID_vector)
    return to_vector_type(type).size();
  else
    PRECONDITION(false);
}

void c_safety_checks_rec(
  goto_functionst::function_mapt::value_type &f,
  const exprt::operandst &guards,
  const exprt &expr,
  const namespacet &ns,
  goto_programt &dest)
{
  if(expr.id() == ID_address_of)
  {
  }
  else if(expr.id() == ID_and)
  {
    auto new_guards = guards;
    for(auto &op : expr.operands())
    {
      c_safety_checks_rec(f, new_guards, op, ns, dest); // rec. call
      new_guards.push_back(op);
    }
    return;
  }
  else if(expr.id() == ID_or)
  {
    auto new_guards = guards;
    for(auto &op : expr.operands())
    {
      c_safety_checks_rec(f, new_guards, op, ns, dest); // rec. call
      new_guards.push_back(not_exprt(op));
    }
    return;
  }
  else if(expr.id() == ID_if)
  {
    const auto &if_expr = to_if_expr(expr);
    auto new_guards = guards;
    new_guards.push_back(if_expr.cond());
    c_safety_checks_rec(
      f, new_guards, if_expr.true_case(), ns, dest); // rec. call
    new_guards.pop_back();
    new_guards.push_back(not_exprt(if_expr.cond()));
    c_safety_checks_rec(
      f, new_guards, if_expr.false_case(), ns, dest); // rec. call
    return;
  }
  else if(expr.id() == ID_forall || expr.id() == ID_exists)
  {
    return;
  }

  // now do operands
  for(auto &op : expr.operands())
    c_safety_checks_rec(f, guards, op, ns, dest); // rec. call

  if(expr.id() == ID_dereference)
  {
    auto size_opt = pointer_offset_size(expr.type(), ns);
    if(size_opt.has_value())
    {
      auto size = from_integer(*size_opt, size_type());
      auto pointer = to_dereference_expr(expr).pointer();
      auto condition = r_or_w_ok_exprt(ID_r_ok, pointer, size);
      auto source_location = expr.source_location();
      condition.add_source_location() = expr.source_location();
      source_location.set_property_class("pointer");
      source_location.set_comment("pointer safe");
      dest.add(goto_programt::make_assertion(condition, source_location));
    }
  }
  else if(expr.id() == ID_div)
  {
    const auto &div_expr = to_div_expr(expr);
    if(
      div_expr.divisor().is_constant() &&
      !to_constant_expr(div_expr.divisor()).is_zero())
    {
    }
    else
    {
      auto zero = from_integer(0, div_expr.type());
      auto condition = notequal_exprt(div_expr.divisor(), zero);
      auto source_location = expr.source_location();
      condition.add_source_location() = expr.source_location();
      source_location.set_property_class("division-by-zero");
      source_location.set_comment("division by zero in " + expr2c(expr, ns));
      dest.add(goto_programt::make_assertion(condition, source_location));
    }
  }
  else if(expr.id() == ID_mod)
  {
    const auto &mod_expr = to_mod_expr(expr);
    if(
      mod_expr.divisor().is_constant() &&
      !to_constant_expr(mod_expr.divisor()).is_zero())
    {
    }
    else
    {
      auto zero = from_integer(0, mod_expr.type());
      auto condition = notequal_exprt(mod_expr.divisor(), zero);
      auto source_location = expr.source_location();
      condition.add_source_location() = expr.source_location();
      source_location.set_property_class("division-by-zero");
      source_location.set_comment("division by zero in " + expr2c(expr, ns));
      dest.add(goto_programt::make_assertion(condition, source_location));
    }
  }
  else if(expr.id() == ID_index)
  {
    const auto &index_expr = to_index_expr(expr);
    auto zero = from_integer(0, index_expr.index().type());
    auto size = typecast_exprt::conditional_cast(
      index_array_size(index_expr.array().type()), index_expr.index().type());
    auto condition = and_exprt(
      binary_relation_exprt(zero, ID_le, index_expr.index()),
      binary_relation_exprt(size, ID_gt, index_expr.index()));
    auto source_location = expr.source_location();
    condition.add_source_location() = expr.source_location();
    source_location.set_property_class("array bounds");
    source_location.set_comment("array bounds in " + expr2c(expr, ns));
    dest.add(goto_programt::make_assertion(condition, source_location));
  }
}

void c_safety_checks(
  goto_functionst::function_mapt::value_type &f,
  const exprt &expr,
  const namespacet &ns,
  goto_programt &dest)
{
  c_safety_checks_rec(f, {}, expr, ns, dest);
}

void c_safety_checks(
  goto_functionst::function_mapt::value_type &f,
  const namespacet &ns)
{
  auto &body = f.second.body;
  goto_programt dest;

  for(auto it = body.instructions.begin(); it != body.instructions.end(); it++)
  {
    it->apply([&f, &ns, &dest](const exprt &expr) {
      c_safety_checks(f, expr, ns, dest);
    });
    std::size_t n = dest.instructions.size();
    if(n != 0)
    {
      body.insert_before_swap(it, dest);
      dest.clear();
      it = std::next(it, n);
    }
  }
}

void c_safety_checks(goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);

  for(auto &f : goto_model.goto_functions.function_map)
    c_safety_checks(f, ns);
}