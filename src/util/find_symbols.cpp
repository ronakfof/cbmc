/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "find_symbols.h"

#include "c_types.h"
#include "expr_iterator.h"
#include "range.h"
#include "std_expr.h"

enum class kindt
{
  F_TYPE,
  F_TYPE_NON_PTR,
  F_EXPR_CURRENT,
  F_EXPR_NEXT,
  F_EXPR_BOTH,
  F_ALL
};

bool has_symbol(
  const exprt &src,
  const find_symbols_sett &symbols,
  bool current,
  bool next)
{
  if(src.id() == ID_symbol && current)
    return symbols.count(to_symbol_expr(src).get_identifier()) != 0;
  else if(src.id() == ID_next_symbol && next)
    return symbols.count(src.get(ID_identifier))!=0;
  else
  {
    forall_operands(it, src)
      if(has_symbol(*it, symbols, current, next))
        return true;
  }

  return false;
}

bool has_symbol(
  const exprt &src,
  const find_symbols_sett &symbols)
{
  return has_symbol(src, symbols, true, true);
}

static void find_symbols(const typet &src, std::set<symbol_exprt> &dest)
{
  if(src.has_subtype())
    find_symbols(to_type_with_subtype(src).subtype(), dest);

  for(const typet &subtype : to_type_with_subtypes(src).subtypes())
    find_symbols(subtype, dest);

  if(src.id() == ID_struct || src.id() == ID_union)
  {
    const struct_union_typet &struct_union_type = to_struct_union_type(src);

    for(const auto &c : struct_union_type.components())
      find_symbols(c, dest);
  }
  else if(src.id() == ID_code)
  {
    const code_typet &code_type = to_code_type(src);
    find_symbols(code_type.return_type(), dest);

    for(const auto &p : code_type.parameters())
    {
      find_symbols(p, dest);
    }
  }
  else if(src.id() == ID_array)
  {
    // do the size -- the subtype is already done
    find_symbols(to_array_type(src).size(), dest);
  }
}

void find_symbols(
  const exprt &src,
  std::set<symbol_exprt> &dest)
{
  src.visit_pre([&dest](const exprt &e) {
    find_symbols(e.type(), dest);

    if(e.id() == ID_symbol)
      dest.insert(to_symbol_expr(e));

    const irept &c_sizeof_type = e.find(ID_C_c_sizeof_type);

    if(c_sizeof_type.is_not_nil())
      find_symbols(static_cast<const typet &>(c_sizeof_type), dest);

    const irept &va_arg_type = e.find(ID_C_va_arg_type);

    if(va_arg_type.is_not_nil())
      find_symbols(static_cast<const typet &>(va_arg_type), dest);
  });
}

void find_symbols(kindt kind, const typet &src, find_symbols_sett &dest);

void find_symbols(kindt kind, const exprt &src, find_symbols_sett &dest)
{
  src.visit_pre([&dest, kind](const exprt &e) {
    find_symbols(kind, e.type(), dest);

    if(
      kind == kindt::F_ALL || kind == kindt::F_EXPR_CURRENT ||
      kind == kindt::F_EXPR_BOTH)
    {
      if(e.id() == ID_symbol)
        dest.insert(to_symbol_expr(e).get_identifier());
    }

    if(
      kind == kindt::F_ALL || kind == kindt::F_EXPR_NEXT ||
      kind == kindt::F_EXPR_BOTH)
    {
      if(e.id() == ID_next_symbol)
        dest.insert(e.get(ID_identifier));
    }

    const irept &c_sizeof_type = e.find(ID_C_c_sizeof_type);

    if(c_sizeof_type.is_not_nil())
      find_symbols(kind, static_cast<const typet &>(c_sizeof_type), dest);

    const irept &va_arg_type = e.find(ID_C_va_arg_type);

    if(va_arg_type.is_not_nil())
      find_symbols(kind, static_cast<const typet &>(va_arg_type), dest);
  });
}

void find_symbols(kindt kind, const typet &src, find_symbols_sett &dest)
{
  if(kind!=kindt::F_TYPE_NON_PTR ||
     src.id()!=ID_pointer)
  {
    if(src.has_subtype())
      find_symbols(kind, to_type_with_subtype(src).subtype(), dest);

    for(const typet &subtype : to_type_with_subtypes(src).subtypes())
      find_symbols(kind, subtype, dest);

    if(
      kind == kindt::F_TYPE || kind == kindt::F_TYPE_NON_PTR ||
      kind == kindt::F_ALL)
    {
      const irep_idt &typedef_name = src.get(ID_C_typedef);
      if(!typedef_name.empty())
        dest.insert(typedef_name);
    }
  }

  if(src.id()==ID_struct ||
     src.id()==ID_union)
  {
    const struct_union_typet &struct_union_type=to_struct_union_type(src);

    for(const auto &c : struct_union_type.components())
      find_symbols(kind, c, dest);
  }
  else if(src.id()==ID_code)
  {
    const code_typet &code_type=to_code_type(src);
    find_symbols(kind, code_type.return_type(), dest);

    for(const auto &p : code_type.parameters())
    {
      find_symbols(kind, p, dest);
    }
  }
  else if(src.id()==ID_array)
  {
    // do the size -- the subtype is already done
    find_symbols(kind, to_array_type(src).size(), dest);
  }
  else if(
    kind == kindt::F_TYPE || kind == kindt::F_TYPE_NON_PTR ||
    kind == kindt::F_ALL)
  {
    if(src.id() == ID_c_enum_tag)
    {
      dest.insert(to_c_enum_tag_type(src).get_identifier());
    }
    else if(src.id() == ID_struct_tag)
    {
      dest.insert(to_struct_tag_type(src).get_identifier());
    }
    else if(src.id() == ID_union_tag)
    {
      dest.insert(to_union_tag_type(src).get_identifier());
    }
  }
}

void find_type_symbols(const exprt &src, find_symbols_sett &dest)
{
  find_symbols(kindt::F_TYPE, src, dest);
}

void find_type_symbols(const typet &src, find_symbols_sett &dest)
{
  find_symbols(kindt::F_TYPE, src, dest);
}

void find_non_pointer_type_symbols(
  const exprt &src,
  find_symbols_sett &dest)
{
  find_symbols(kindt::F_TYPE_NON_PTR, src, dest);
}

void find_non_pointer_type_symbols(
  const typet &src,
  find_symbols_sett &dest)
{
  find_symbols(kindt::F_TYPE_NON_PTR, src, dest);
}

void find_type_and_expr_symbols(const exprt &src, find_symbols_sett &dest)
{
  find_symbols(kindt::F_ALL, src, dest);
}

void find_type_and_expr_symbols(const typet &src, find_symbols_sett &dest)
{
  find_symbols(kindt::F_ALL, src, dest);
}

void find_symbols_or_nexts(const exprt &src, find_symbols_sett &dest)
{
  find_symbols(kindt::F_EXPR_BOTH, src, dest);
}

void find_symbols(
  const exprt &src,
  find_symbols_sett &dest,
  bool current,
  bool next)
{
  if(current)
  {
    if(next)
      find_symbols(kindt::F_EXPR_BOTH, src, dest);
    else
      find_symbols(kindt::F_EXPR_CURRENT, src, dest);
  }
  else if(next)
    find_symbols(kindt::F_EXPR_NEXT, src, dest);
}
