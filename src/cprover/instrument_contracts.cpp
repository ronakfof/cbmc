/*******************************************************************\

Module: Instrument Contracts

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Instrument Contracts

#include "instrument_contracts.h"

#include <util/c_types.h>
#include <util/format_expr.h>

#include <goto-programs/goto_model.h>

#include <iostream>

static bool
permitted_by_assigns_clause(const exprt::operandst &assigns, const exprt &lhs)
{
  if(lhs.id() == ID_symbol)
  {
    for(auto &a : assigns)
      if(lhs == a)
        return true;
  }

  return false;
}

static bool
is_procedure_local(const irep_idt &function_identifier, const exprt &lhs)
{
  return false;
}

void instrument_contracts(
  goto_functionst::function_mapt::value_type &f,
  const namespacet &ns)
{
  auto &symbol = ns.lookup(f.first);
  auto &contract = to_code_with_contract_type(symbol.type);
  auto &body = f.second.body;

  if(body.instructions.empty())
    return; // nothing to check

  // precondition?
  if(!contract.requires().empty())
  {
    // stick these in as assumptions
    for(auto &assumption : contract.requires())
    {
      body.insert_before(
        body.instructions.begin(),
        goto_programt::make_assumption(
          assumption, assumption.source_location()));
    }
  }

  // postcondition?
  if(!contract.ensures().empty())
  {
    // stick these in as assertions at the end
    auto last = body.instructions.end();
    if(std::prev(last)->is_end_function())
      last = std::prev(last);
    for(auto &assertion : contract.ensures())
    {
      auto location = assertion.source_location();
      location.set_property_class(ID_postcondition);
      location.set_comment("postcondition");
      auto assertion_instruction =
        goto_programt::make_assertion(assertion, std::move(location));
      body.insert_before_swap(last, assertion_instruction);
    }
  }

  std::cout << "check: " << f.first << "\n";

  // assigns?
  if(!contract.assigns().empty() || !contract.ensures().empty())
  {
    std::cout << "assigns: " << f.first << "\n";
    for(auto it = body.instructions.begin(); it != body.instructions.end();
        it++)
    {
      if(it->is_assign())
      {
        const auto &lhs = it->assign_lhs();

        std::cout << "LHS: " << format(lhs) << "\n";

        // is it in the 'assigns' clause?
        if(permitted_by_assigns_clause(contract.assigns(), lhs))
        {
          std::cout << "LHS-assigns"
                    << "\n";
          // ok
        }
        else if(is_procedure_local(f.first, lhs))
        {
          std::cout << "LHS-procedure-local"
                    << "\n";
          // ok
        }
        else
        {
          std::cout << "LHS-fail"
                    << "\n";
          // maybe not ok
          auto location = it->source_location();
          location.set_property_class("assigns");
          location.set_comment("assigns clause");
          auto assertion_instruction =
            goto_programt::make_assertion(false_exprt(), std::move(location));
          body.insert_before_swap(it, assertion_instruction);
          it++; // skip over the assertion we have just generated
        }
      }
    }
  }
}

void instrument_contracts(goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);

  for(auto &f : goto_model.goto_functions.function_map)
    instrument_contracts(f, ns);
}
