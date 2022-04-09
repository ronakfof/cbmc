#include <util/format_expr.h>
#include <util/pointer_expr.h>

#include "state.h"

void format_hooks()
{
  add_format_hook(
    ID_object_address,
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
      const auto &object_address_expr = to_object_address_expr(expr);
      os << u8"\u275d" << object_address_expr.object_identifier() << u8"\u275e";
      return os;
    });

  add_format_hook(
    ID_object_size, [](std::ostream &os, const exprt &expr) -> std::ostream & {
      const auto &object_size_expr = to_unary_expr(expr);
      os << "object_size(" << format(object_size_expr.op()) << ')';
      return os;
    });

  add_format_hook(
    ID_field_address,
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
      const auto &field_address_expr = to_field_address_expr(expr);
      os << format(field_address_expr.base()) << u8".\u275d"
         << field_address_expr.component_name() << u8"\u275e";
      return os;
    });

  add_format_hook(
    ID_evaluate, [](std::ostream &os, const exprt &expr) -> std::ostream & {
      const auto &evaluate_expr = to_evaluate_expr(expr);
      if(evaluate_expr.op0().id() == ID_symbol)
        os << format(evaluate_expr.op0());
      else
        os << '(' << format(evaluate_expr.op0()) << ')';
      os << '(' << format(evaluate_expr.op1()) << ')';
      return os;
    });

  add_format_hook(
    ID_update_state, [](std::ostream &os, const exprt &expr) -> std::ostream & {
      const auto &update_state_expr = to_update_state_expr(expr);
      os << format(update_state_expr.state()) << '['
         << format(update_state_expr.address())
         << ":=" << format(update_state_expr.new_value()) << ']';
      return os;
    });

  add_format_hook(
    ID_is_cstring, [](std::ostream &os, const exprt &expr) -> std::ostream & {
      if(expr.operands().size() == 1)
      {
        const auto &is_cstring_expr = to_unary_expr(expr);
        os << "is_cstring(" << format(is_cstring_expr.op()) << ')';
      }
      else
      {
        const auto &is_cstring_expr = to_binary_expr(expr);
        os << "is_cstring(" << format(is_cstring_expr.op0()) << ", "
           << format(is_cstring_expr.op1()) << ')';
      }
      return os;
    });
}
