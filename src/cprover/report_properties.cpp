/*******************************************************************\

Module: Solver

Author:

\*******************************************************************/

/// \file
/// Solver

#include <util/cout_message.h>
#include <util/format_expr.h>
#include <util/mathematical_expr.h>
#include <util/pointer_expr.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>

#include "console.h"
#include "free_symbols.h"
#include "may_alias.h"
#include "solver.h"
#include "solver_types.h"
#include "state.h"

#include <iomanip>
#include <iostream>
#include <map>
#include <set>

void report_properties(const std::vector<propertyt> &properties)
{
  irep_idt current_file, current_function;

  for(auto &property : properties)
  {
    const auto &l = property.source_location;

    if(l.get_function() != current_function)
    {
      if(!current_function.empty())
        consolet::out() << '\n';
      current_function = l.get_function();
      if(!current_function.empty())
      {
        current_file = l.get_file();
        if(!current_file.empty())
          consolet::out() << current_file << ' ';
        if(!l.get_function().empty())
          consolet::out() << "function " << l.get_function();
        consolet::out() << '\n';
      }
    }

    auto property_id = l.get_property_id();
    consolet::out() << consolet::faint << '[';
    if(property_id.empty())
      consolet::out() << '?';
    else
      consolet::out() << property_id;
    consolet::out() << ']' << consolet::reset;

    if(l.get_file() != current_file)
      consolet::out() << ' ' << l.get_file();

    if(!l.get_line().empty())
      consolet::out() << " line " << l.get_line();

    auto comment = l.get_comment();
    if(!comment.empty())
      consolet::out() << ' ' << comment;

    consolet::out() << ": ";

    switch(property.status)
    {
    case propertyt::PASS:
      consolet::out() << consolet::green << "SUCCESS" << consolet::reset;
      break;

    case propertyt::REFUTED:
      consolet::out() << consolet::red << "REFUTED" << consolet::reset;
      break;

    case propertyt::ERROR:
      consolet::out() << consolet::red << consolet::bold << "ERROR"
                      << consolet::reset;
      break;

    case propertyt::UNKNOWN:
      consolet::out() << consolet::yellow << "UNKNOWN" << consolet::reset;
      break;
    }

    consolet::out() << '\n';
  }
}

solver_resultt overall_outcome(const std::vector<propertyt> &properties)
{
  auto result = solver_resultt::ALL_PASS;

  for(auto &property : properties)
    if(property.status == propertyt::ERROR)
      result = solver_resultt::ERROR;
    else if(property.status == propertyt::REFUTED)
      result = solver_resultt::SOME_FAIL;

  return result;
}