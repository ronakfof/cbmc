/*******************************************************************\

Module: Solver

Author:

\*******************************************************************/

/// \file
/// Solver

#include "solver.h"

#include <util/cout_message.h>
#include <util/format_expr.h>
#include <util/std_expr.h>

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>

#include "console.h"
#include "free_symbols.h"
#include "propagate.h"
#include "report_properties.h"
#include "solver_types.h"
#include "state.h"

#include <iomanip>
#include <iostream>
#include <map>
#include <set>

frame_mapt build_frame_map(const std::vector<framet> &frames)
{
  frame_mapt frame_map;

  for(std::size_t i = 0; i < frames.size(); i++)
    frame_map[frames[i].symbol] = frame_reft(i);

  return frame_map;
}

void framet::add_invariant(exprt invariant)
{
  if(invariant.id() == ID_and)
  {
    for(const auto &conjunct : to_and_expr(invariant).operands())
      add_invariant(conjunct);
  }
  else
    invariants.push_back(std::move(invariant));
}

void framet::add_auxiliary(exprt invariant)
{
  if(invariant.id() == ID_and)
  {
    for(const auto &conjunct : to_and_expr(invariant).operands())
      add_auxiliary(conjunct);
  }
  else
    auxiliaries.push_back(std::move(invariant));
}

std::vector<framet> setup_frames(const std::vector<exprt> &constraints)
{
  std::set<symbol_exprt> states_set;
  std::vector<framet> frames;

  for(auto &c : constraints)
  {
    free_symbols(c, [&states_set, &frames](const symbol_exprt &s) {
      auto insert_result = states_set.insert(s);
      if(insert_result.second)
        frames.emplace_back(s, frame_reft(frames.size()));
    });
  }

  return frames;
}

void find_implications(
  const std::vector<exprt> &constraints,
  std::vector<framet> &frames)
{
  const auto frame_map = build_frame_map(frames);

  for(const auto &c : constraints)
  {
    // look for ∀ ς : state . Sxx(ς) ⇒ Syy(...)
    //      and ∀ ς : state . Sxx(ς) ⇒ ...
    if(c.id() == ID_forall && to_forall_expr(c).where().id() == ID_implies)
    {
      auto &implication = to_implies_expr(to_forall_expr(c).where());

      if(
        implication.rhs().id() == ID_function_application &&
        to_function_application_expr(implication.rhs()).function().id() ==
          ID_symbol)
      {
        auto &rhs_symbol = to_symbol_expr(
          to_function_application_expr(implication.rhs()).function());
        auto s_it = frame_map.find(rhs_symbol);
        if(s_it != frame_map.end())
        {
          frames[s_it->second.index].implications.emplace_back(
            implication.lhs(), to_function_application_expr(implication.rhs()));
        }
      }
    }
  }
}

frame_reft
find_frame(const frame_mapt &frame_map, const symbol_exprt &frame_symbol)
{
  auto entry = frame_map.find(frame_symbol);

  if(entry == frame_map.end())
    PRECONDITION(false);

  return entry->second;
}

std::vector<propertyt> find_properties(
  const std::vector<exprt> &constraints,
  const std::vector<framet> &frames)
{
  const auto frame_map = build_frame_map(frames);
  std::vector<propertyt> properties;

  for(const auto &c : constraints)
  {
    // look for ∀ ς : state . Sxx(ς) ⇒ ...
    if(c.id() == ID_forall && to_forall_expr(c).where().id() == ID_implies)
    {
      auto &implication = to_implies_expr(to_forall_expr(c).where());

      if(
        implication.rhs().id() != ID_function_application &&
        implication.lhs().id() == ID_function_application &&
        to_function_application_expr(implication.lhs()).function().id() ==
          ID_symbol)
      {
        auto &lhs_symbol = to_symbol_expr(
          to_function_application_expr(implication.lhs()).function());
        auto lhs_frame = find_frame(frame_map, lhs_symbol);
        properties.emplace_back(
          c.source_location(), lhs_frame, implication.rhs());
      }
    }
  }

  return properties;
}

exprt property_predicate(const implies_exprt &src)
{
  // Sxx(ς) ⇒ p(ς)
  return src.rhs();
}

void dump(
  const std::vector<framet> &frames,
  const propertyt &property,
  bool values,
  bool implications)
{
  for(const auto &f : frames)
  {
    std::cout << "FRAME: " << format(f.symbol) << '\n';

    if(implications)
    {
      for(auto &c : f.implications)
      {
        std::cout << "  implication: ";
        std::cout << format(c.lhs) << " -> " << format(c.rhs);
        std::cout << '\n';
      }
    }

    if(values)
    {
      for(auto &i : f.invariants)
        std::cout << "  invariant: " << format(i) << '\n';

      for(auto &i : f.auxiliaries)
        std::cout << "  auxiliary: " << format(i) << '\n';
    }

    if(property.frame == f.ref)
      std::cout << "  property: " << format(property.condition) << '\n';
  }
}

bool is_subsumed(
  const std::vector<exprt> &a1,
  const std::vector<exprt> &a2,
  const exprt &b,
  const namespacet &ns)
{
  if(b.is_true())
    return true; // anything subsumes 'true'

  for(auto &a_conjunct : a1)
    if(a_conjunct.is_false())
      return true; // 'false' subsumes anything

  for(auto &a_conjunct : a1)
    if(a_conjunct == b)
      return true; // b is subsumed by a conjunct in a

  // Invariant is empty? (true)
  if(a1.empty() && a2.empty())
    return false; // Doesn't subsume anything.

  cout_message_handlert message_handler;
  satcheckt satcheck(message_handler);
  bv_pointerst solver(ns, satcheck, message_handler);

  // check if a => b, or (!a || b), or (a && !b) is unsat
  for(auto &a_conjunct : a1)
    solver.set_to_true(replace_evaluate(a_conjunct));

  for(auto &a_conjunct : a2)
    solver.set_to_true(replace_evaluate(a_conjunct));

  solver.set_to_false(replace_evaluate(b));

  switch(solver())
  {
  case decision_proceduret::resultt::D_SATISFIABLE:
    return false;
  case decision_proceduret::resultt::D_UNSATISFIABLE:
    return true;
  case decision_proceduret::resultt::D_ERROR:
    throw "error reported by solver";
  }

  UNREACHABLE; // to silence a warning
}

void solver(
  std::vector<framet> &frames,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &ns,
  std::vector<propertyt> &properties,
  std::size_t property_index)
{
  const auto frame_map = build_frame_map(frames);
  auto &property = properties[property_index];

  std::cout << "\nDoing " << format(property.condition) << '\n';

  for(auto &frame : frames)
    frame.reset();

  // add properties proven so far as auxiliaries
  for(std::size_t i = 0; i<property_index; i++)
  {
    const auto &p = properties[i];
    if(p.status == propertyt::PASS)
      frames[p.frame.index].add_auxiliary(p.condition);
  }

  std::vector<workt> queue;

  auto propagator = [&frames, &frame_map, &queue, &ns](
                      const symbol_exprt &symbol, exprt invariant) {
    auto &f = frames[find_frame(frame_map, symbol).index];

    std::cout << "F: " << format(symbol) << " <- " << format(invariant) << '\n';

    // check if already subsumed
    if(is_subsumed(f.invariants, f.auxiliaries, invariant, ns))
    {
      std::cout << "*** SUBSUMED\n";
    }
    else
    {
      queue.emplace_back(f.ref, std::move(invariant));
    }
  };

  // we start with I = P
  queue.emplace_back(property.frame, property.condition);

  while(!queue.empty())
  {
    auto work = queue.back();
    queue.pop_back();

    frames[work.frame.index].add_invariant(work.invariant);

    dump(frames, property, true, true);
    std::cout << '\n';

    switch(propagate(frames, work, address_taken, ns, propagator))
    {
    case propagate_resultt::CONFLICT:
      property.status = propertyt::REFUTED;
      return;

    case propagate_resultt::PROPAGATED:
      break;
    }
  }

  property.status = propertyt::PASS;
}

solver_resultt
solver(const std::vector<exprt> &constraints, const namespacet &ns)
{
  auto frames = setup_frames(constraints);

  find_implications(constraints, frames);

  auto properties = find_properties(constraints, frames);

  if(properties.empty())
  {
    std::cout << "\nThere are no properties to show.\n";
    return solver_resultt::ALL_PASS;
  }

  const std::unordered_set<symbol_exprt, irep_hash> address_taken;

  // solve each property separately, in order of occurence
  for(std::size_t i = 0; i<properties.size(); i++)
    solver(frames, address_taken, ns, properties, i);

  // reporting
  report_properties(properties);

  // overall outcome
  return overall_outcome(properties);
}
