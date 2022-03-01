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
    auto &evaluate_expr = to_binary_expr(src);
    if(evaluate_expr.op1().id() == ID_object_address)
    {
      const auto &object_address = to_object_address_expr(evaluate_expr.op1());
      auto id = object_address.object_identifier();
      return symbol_exprt(
        "evaluate-" + id2string(id), object_address.object_type());
    }
  }

  for(auto &op : src.operands())
    op = replace_evaluate(op);

  return src;
}
