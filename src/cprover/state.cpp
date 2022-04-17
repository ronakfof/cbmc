/*******************************************************************\

Module: State Encoding

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "state.h"

#include <util/pointer_expr.h>

void replace_evaluate(typet &src)
{
  if(src.id() == ID_array)
  {
    replace_evaluate(to_array_type(src).element_type());
    to_array_type(src).size() = replace_evaluate(to_array_type(src).size());
  }
  else if(src.id() == ID_pointer)
  {
    replace_evaluate(to_pointer_type(src).base_type());
  }
}

exprt replace_evaluate(exprt src)
{
  replace_evaluate(src.type());

  if(src.id() == ID_evaluate)
  {
    auto &evaluate_expr = to_evaluate_expr(src);
    auto &address = evaluate_expr.address();
    if(address.id() == ID_object_address)
    {
      const auto &object_address = to_object_address_expr(address);
      auto id = object_address.object_identifier();
      return symbol_exprt(
        "evaluate-" + id2string(id), object_address.object_type());
    }
    else if(address.id() == ID_element_address)
    {
      auto &element_address_expr = to_element_address_expr(address);
      if(element_address_expr.base().id() == ID_object_address)
      {
        const auto &object_address =
          to_object_address_expr(element_address_expr.base());
        auto id = object_address.object_identifier();
        auto index = replace_evaluate(element_address_expr.index());
        auto object_type =
          array_typet(object_address.object_type(), nil_exprt());
        return index_exprt(
          symbol_exprt("evaluate-" + id2string(id), object_type),
          index,
          element_address_expr.element_type());
      }
    }
  }

  for(auto &op : src.operands())
    op = replace_evaluate(op);

  return src;
}
