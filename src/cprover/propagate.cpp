/*******************************************************************\

Module: Propagate

Author:

\*******************************************************************/

/// \file
/// Propagate

#include "propagate.h"

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/cout_message.h>
#include <util/format_expr.h>
#include <util/mathematical_expr.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>

#include "may_alias.h"
#include "state.h"

#include <iostream>

std::size_t allocate_counter = 0;

exprt simplify_evaluate_update(
  evaluate_exprt evaluate_expr,
  const namespacet &ns)
{
  PRECONDITION(evaluate_expr.state().id() == ID_update_state);

  const auto &update_state_expr = to_update_state_expr(evaluate_expr.state());

  auto may_alias =
    ::may_alias(evaluate_expr.address(), update_state_expr.address(), ns);

  if(may_alias.has_value())
  {
    // 'simple' case
    if(may_alias->is_true())
    {
      // The object is known to be the same.
      // (ς[A:=V])(A) --> V
      return typecast_exprt::conditional_cast(
        update_state_expr.new_value(), evaluate_expr.type());
    }
    else if(may_alias->is_false())
    {
      // The object is known to be different.
      // (ς[❝x❞:=V])(❝y❞) --> ς(❝y❞)
      auto new_evaluate_expr = evaluate_expr;
      new_evaluate_expr.state() = update_state_expr.state();
      return std::move(new_evaluate_expr);
    }
    else
    {
      // The object may or may not be the same.
      // (ς[A:=V])(B) --> if cond then V else ς(B) endif
      auto new_evaluate_expr = evaluate_expr;
      new_evaluate_expr.state() = update_state_expr.state();
      return if_exprt(
        std::move(*may_alias),
        typecast_exprt::conditional_cast(
          update_state_expr.new_value(), evaluate_expr.type()),
        std::move(new_evaluate_expr));
    }
  }

  // Complex case.
  auto same_object =
    ::same_object(evaluate_expr.address(), update_state_expr.address());
  auto object = update_state_expr.new_value();
  auto offset = pointer_offset(evaluate_expr.address());
  auto byte_extract = make_byte_extract(object, offset, evaluate_expr.type());
  auto new_evaluate_expr = evaluate_expr;
  new_evaluate_expr.state() = update_state_expr.state();
  return if_exprt(
    std::move(same_object),
    std::move(byte_extract),
    std::move(new_evaluate_expr));
}

exprt simplify_evaluate_allocate(
  evaluate_exprt evaluate_expr,
  const namespacet &ns)
{
  PRECONDITION(evaluate_expr.state().id() == ID_allocate);

  const auto &allocate_expr = to_allocate_expr(evaluate_expr.state());

  // Same address?
  if(evaluate_expr.address() == allocate_expr.address())
  {
    irep_idt identifier = "allocate-" + std::to_string(++allocate_counter);
    auto object_size = allocate_expr.size();
    auto object_type = array_typet(char_type(), object_size);
    auto symbol_expr = symbol_exprt(identifier, object_type);
    return object_address_exprt(symbol_expr);
  }
  else // different
  {
    auto new_evaluate_expr = evaluate_expr;
    new_evaluate_expr.state() = allocate_expr.state();
    return std::move(new_evaluate_expr);
  }
}

exprt simplify_ok_expr(ternary_exprt src, const namespacet &ns)
{
  const auto &pointer = src.op1();
  const auto &size = src.op2();

  if(pointer.id() == ID_object_address)
  {
    const auto &symbol =
      ns.lookup(to_object_address_expr(pointer).object_identifier());
    if(symbol.is_static_lifetime)
    {
      auto symbol_size = size_of_expr(symbol.type, ns);
      if(symbol_size.has_value())
        return binary_relation_exprt(size, ID_le, *symbol_size);
    }
    else
    {
      // might be 'dead'
      auto symbol_size = size_of_expr(symbol.type, ns);
      if(symbol_size.has_value())
        return binary_relation_exprt(size, ID_le, *symbol_size);
    }
  }

  return std::move(src);
}

static bool is_one(const exprt &src)
{
  if(src.id() == ID_typecast)
    return is_one(to_typecast_expr(src).op());
  else if(src.id() == ID_constant)
  {
    auto value_opt = numeric_cast<mp_integer>(src);
    return value_opt.has_value() && *value_opt == 1;
  }
  else
    return false;
}

exprt simplify_is_cstring_expr(binary_exprt src, const namespacet &ns)
{
  PRECONDITION(src.type().id() == ID_bool);
  const auto &state = src.op0();
  const auto &pointer = src.op1();

  if(state.id() == ID_update_state)
  {
    const auto &update_state_expr = to_update_state_expr(state);

    auto cstring_in_old_state = src;
    cstring_in_old_state.op0() = update_state_expr.state();

    auto may_alias = ::may_alias(pointer, update_state_expr.address(), ns);

    if(may_alias.has_value() && may_alias->is_false())
    {
      // different objects
      // cstring(s[x:=v], p) --> cstring(s, p)
      return cstring_in_old_state;
    }

    // maybe the same

    // Are we writing zero?
    if(update_state_expr.new_value().is_zero())
    {
      // cstring(s[p:=0], q) --> if p alias q then true else cstring(s, q)
      return if_exprt(
        same_object(pointer, update_state_expr.address()),
        true_exprt(),
        cstring_in_old_state);
    }
  }

  if(pointer.id() == ID_plus)
  {
    auto &plus_expr = to_plus_expr(pointer);
    if(plus_expr.operands().size() == 2 && is_one(plus_expr.op1()))
    {
      // is_cstring(ς, p + 1)) --> is_cstring(ς, p) ∨ ς(p)=0
    }
  }

  return std::move(src);
}

exprt simplify_state_expr(exprt src, const namespacet &ns)
{
  // operands first
  for(auto &op : src.operands())
    op = simplify_state_expr(op, ns);

  if(src.id() == ID_evaluate)
  {
    auto &evaluate_expr = to_evaluate_expr(src);

    if(evaluate_expr.state().id() == ID_update_state)
    {
      return simplify_evaluate_update(evaluate_expr, ns);
    }
    else if(evaluate_expr.state().id() == ID_allocate)
    {
      return simplify_evaluate_allocate(evaluate_expr, ns);
    }
  }
  else if(src.id() == ID_r_ok || src.id() == ID_w_ok || src.id() == ID_rw_ok)
  {
    return simplify_ok_expr(to_ternary_expr(src), ns);
  }
  else if(src.id() == ID_is_cstring)
  {
    return simplify_is_cstring_expr(to_binary_expr(src), ns);
  }

  return src;
}

propagate_resultt propagate(
  std::vector<framet> &frames,
  const workt &work,
  const namespacet &ns,
  const std::function<void(const symbol_exprt &, exprt)> &propagator)
{
  auto result = propagate_resultt::PROPAGATED;
  auto &f = frames[work.frame.index];

  for(const auto &implication : f.implications)
  {
    auto &next_state = implication.rhs.arguments().front();
    auto lambda_expr = lambda_exprt({state_expr()}, work.invariant);
    auto instance = lambda_expr.instantiate({next_state});
    auto simplified1 = simplify_state_expr(instance, ns);
    auto simplified2 = simplify_expr(simplified1, ns);

    if(implication.lhs.id() == ID_function_application)
    {
      // Sxx(ς) ⇒ Syy(ς[update])
      auto &state = to_symbol_expr(
        to_function_application_expr(implication.lhs).function());
      propagator(state, simplified2);
    }
    else if(
      implication.lhs.id() == ID_and &&
      to_and_expr(implication.lhs).op0().id() == ID_function_application)
    {
      // Sxx(ς) ∧ ς(COND) ⇒ Syy(ς)
      auto &function_application =
        to_function_application_expr(to_and_expr(implication.lhs).op0());
      auto &state = to_symbol_expr(function_application.function());
      auto cond = to_and_expr(implication.lhs).op1();
      propagator(state, implies_exprt(cond, simplified2));
    }
    else
    {
      // these are preconditions, e.g., true ⇒ SInitial(ς)
      auto cond = implies_exprt(implication.lhs, simplified2);
      std::cout << "PREa: " << format(cond) << "\n";
      auto cond_replaced = replace_evaluate(cond);
      std::cout << "PREb: " << format(cond_replaced) << "\n";

      // ask the solver
      cout_message_handlert message_handler;
      satcheckt satcheck(message_handler);
      bv_pointerst solver(ns, satcheck, message_handler);
      solver.set_to_false(cond_replaced);
      switch(solver())
      {
      case decision_proceduret::resultt::D_SATISFIABLE:
        result = propagate_resultt::CONFLICT;
        break;
      case decision_proceduret::resultt::D_UNSATISFIABLE:
        break;
      case decision_proceduret::resultt::D_ERROR:
        throw "error reported by solver";
      }
    }
  }

  return result;
}
