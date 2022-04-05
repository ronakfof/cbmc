/*******************************************************************\

Module: Instrument Contracts

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Instrument Contracts

#include "instrument_contracts.h"

#include <util/c_types.h>

#include <goto-programs/goto_model.h>

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

  // assigns?
  if(!contract.assigns().empty())
  {
    for(auto it = body.instructions.begin(); it != body.instructions.end();
        it++)
    {
      if(it->is_assign())
      {
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
