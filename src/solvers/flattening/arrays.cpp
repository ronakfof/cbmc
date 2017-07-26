/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "arrays.h"

#include <util/arith_tools.h>
#include <util/json.h>
#include <util/message.h>
#include <util/replace_expr.h>
#include <util/std_expr.h>

#include <solvers/prop/literal_expr.h>
#include <solvers/prop/prop.h>

// #ifdef DEBUG
#include <iostream>
// #endif

arrayst::arrayst(
  const namespacet &_ns,
  propt &_prop,
  message_handlert &_message_handler,
  bool _get_array_constraints)
  : equalityt(_prop, _message_handler),
    ns(_ns),
    log(_message_handler),
    message_handler(_message_handler)
{
  // get_array_constraints is true when --show-array-constraints is used
  get_array_constraints = _get_array_constraints;
}

void arrayst::record_array_index(const index_exprt &index)
{
  wegt::node_indext number = arrays.number(index.array());
  collect_arrays(index.array(), number);
  index_map[number].insert(index.index());
}

literalt arrayst::record_array_equality(
  const equal_exprt &equality)
{
  const exprt &op0=equality.op0();
  const exprt &op1=equality.op1();

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    op0.type() == op1.type(),
    "record_array_equality got equality without matching types",
    irep_pretty_diagnosticst{equality});

  DATA_INVARIANT(
    op0.type().id() == ID_array,
    "record_array_equality parameter should be array-typed");

  wegt::node_indext a1 = arrays.number(op0);
  wegt::node_indext a2 = arrays.number(op1);

  literalt l = SUB::equality(op0, op1);
#if 0
  std::cerr << "LIT " << l.get() << " == " << format(equality) << std::endl;
#endif

  // one undirected edge for each array equality
  add_weg_edge(a1, a2, literal_exprt{l});

  collect_arrays(op0, a1);
  collect_arrays(op1, a2);

  return l;
}

void arrayst::collect_indices(const exprt &expr)
{
  if(expr.id()!=ID_index)
  {
    if(expr.id() == ID_array_comprehension)
      array_comprehension_args.insert(
        to_array_comprehension_expr(expr).arg().get_identifier());

    forall_operands(op, expr) collect_indices(*op);
  }
  else
  {
    const index_exprt &e = to_index_expr(expr);

    if(
      e.index().id() == ID_symbol &&
      array_comprehension_args.count(
        to_symbol_expr(e.index()).get_identifier()) != 0)
    {
      return;
    }

    collect_indices(e.index());
    collect_indices(e.array());

    const typet &array_op_type = e.array().type();

    if(array_op_type.id()==ID_array)
    {
      const array_typet &array_type=
        to_array_type(array_op_type);

      if(is_unbounded_array(array_type))
        record_array_index(e);
    }
  }
}

void arrayst::collect_arrays(const exprt &a, wegt::node_indext a_ind)
{
  const array_typet &array_type = to_array_type(a.type());

  // remember it
  if(a.id()==ID_with)
  {
    const with_exprt &with_expr=to_with_expr(a);

    DATA_INVARIANT_WITH_DIAGNOSTICS(
      array_type == with_expr.old().type(),
      "collect_arrays got 'with' without matching types",
      irep_pretty_diagnosticst{a});

    for(std::size_t i = 1; i < with_expr.operands().size(); i += 2)
    {
      collect_indices(with_expr.operands()[i]);     // where
      collect_indices(with_expr.operands()[i + 1]); // new value
    }

    // one undirected edge for each array update
    std::size_t expr_old_ind = arrays.number(with_expr.old());
    add_weg_edge(a_ind, expr_old_ind, with_expr);

    // record 'old'
    collect_arrays(with_expr.old(), expr_old_ind);
  }
  else if(a.id()==ID_update)
  {
    const update_exprt &update_expr=to_update_expr(a);

    DATA_INVARIANT_WITH_DIAGNOSTICS(
      array_type == update_expr.old().type(),
      "collect_arrays got 'update' without matching types",
      irep_pretty_diagnosticst{a});

    UNIMPLEMENTED;
  }
  else if(a.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(a);

    DATA_INVARIANT_WITH_DIAGNOSTICS(
      array_type == if_expr.true_case().type(),
      "collect_arrays got if without matching types",
      irep_pretty_diagnosticst{a});

    DATA_INVARIANT_WITH_DIAGNOSTICS(
      array_type == if_expr.false_case().type(),
      "collect_arrays got if without matching types",
      irep_pretty_diagnosticst{a});

    // do weg edges
    wegt::node_indext expr_true_ind = arrays.number(if_expr.true_case());
    wegt::node_indext expr_false_ind = arrays.number(if_expr.false_case());
    literalt cond = convert(if_expr.cond());
#if 0
    std::cerr << "LIT " << cond.get() << " == " << format(if_expr.cond()) << std::endl;
#endif
    add_weg_edge(a_ind, expr_true_ind, literal_exprt{cond});
    add_weg_edge(a_ind, expr_false_ind, literal_exprt{!cond});

    collect_arrays(if_expr.true_case(), expr_true_ind);
    collect_arrays(if_expr.false_case(), expr_false_ind);
  }
  else if(a.id()==ID_symbol)
  {
  }
  else if(a.id()==ID_nondet_symbol)
  {
  }
  else if(a.id()==ID_member)
  {
    const auto &struct_op = to_member_expr(a).struct_op();

    DATA_INVARIANT(
      struct_op.id() == ID_symbol || struct_op.id() == ID_nondet_symbol,
      "unexpected array expression: member with '" + struct_op.id_string() +
        "'");
  }
  else if(a.id()==ID_constant ||
          a.id()==ID_array ||
          a.id()==ID_string_constant)
  {
  }
  else if(a.id()==ID_array_of)
  {
  }
  else if(a.id()==ID_byte_update_little_endian ||
          a.id()==ID_byte_update_big_endian)
  {
    UNREACHABLE;
  }
  else if(a.id()==ID_typecast)
  {
    const auto &typecast_op = to_typecast_expr(a).op();

    // cast between array types?
    DATA_INVARIANT(
      typecast_op.type().id() == ID_array,
      "unexpected array type cast from " + typecast_op.type().id_string());

    wegt::node_indext op_ind = arrays.number(typecast_op);
    add_weg_edge(a_ind, op_ind, literal_exprt{const_literal(true)});

    collect_arrays(typecast_op, op_ind);
  }
  else if(a.id()==ID_index)
  {
    // an array of arrays!
    const exprt &array = to_index_expr(a).array();

    collect_arrays(array, arrays.number(array));
  }
  else if(a.id() == ID_array_comprehension)
  {
  }
  else
    throw "unexpected array expression (collect_arrays): `" + a.id_string() +
      "'";
}

bool arrayst::must_be_different(const exprt &x, const exprt &y)
{
  return false;
}

void arrayst::weg_path_condition(
  const weg_patht &path,
  const exprt &index_a,
  exprt::operandst &cond)
{
  for(const auto &pn : path)
  {
    if(!pn.edge.has_value())
      break;

#if ARRAY_SPEEDUP_DEBUG
    std::cout << "edge: " << pn.n << "->" << pn.edge->first << " "
              << format(arrays[pn.n]) << "\n";
#endif

    const exprt &weg_edge = (*pn.edge)->second;

    // TODO: we should filter out trivially-false conjunctions when literals and
    // their negations or equalities and their notequal counterparts are
    // included
    if(weg_edge.id() == ID_with)
    {
      const auto &with_expr = to_with_expr(weg_edge);
      notequal_exprt inequality(with_expr.where(), index_a);
      cond.push_back(inequality);
    }
    else if(weg_edge != literal_exprt{const_literal(true)})
      cond.push_back(weg_edge);
  }
}

void arrayst::process_weg_path(const weg_patht &path)
{
  INVARIANT(!path.empty(), "path is not empty");
  wegt::node_indext a = path.front().n;
  wegt::node_indext b = path.back().n;

#if 0
  std::cerr << "PATH: ";
  for(const auto &n : path)
    std::cerr << n.n << ",";
  std::cerr << std::endl;
#endif

  // do constraints
  const index_sett &index_set_a = index_map[a];
  const index_sett &index_set_b = index_map[b];

#if ARRAY_SPEEDUP_DEBUG
  std::cout << "b is: " << format(arrays[b]) << '\n';
#endif

  for(const auto &index_a : index_set_a)
  {
    // lazily instantiate read-over-write
    if(arrays[b].id() == ID_with)
    {
      // TODO: add support for multi-operand "with"
      PRECONDITION(arrays[b].operands().size() == 3);
      // we got x=(y with [i:=v])
      const auto &expr_b = to_with_expr(arrays[b]);
      const exprt &index_b = expr_b.where();
      const exprt &value_b = expr_b.new_value();

      // 1. we got a[i]...b[j], given as edges on the stack
      // 2. add (i=j AND path_cond)=>a[i]=b[j]
      // 3. The path condition requires the update indices
      //    on the stack to be different from i.
      exprt::operandst cond;
      cond.reserve(path.size() + 1);
      cond.push_back(equal_exprt(index_a, index_b));
      weg_path_condition(path, index_a, cond);

      // a_i=b_i
      index_exprt a_i(arrays[a], index_a);
      // cond => a_i=b_i
      implies_exprt implication(conjunction(cond), equal_exprt(a_i, value_b));
      //#if ARRAY_SPEEDUP_DEBUG
      std::cout << "C2a: " << format(implication) << '\n';
      //#endif
      set_to_true(implication);
    }
    else if(arrays[b].id() == ID_array_of)
    {
      const auto &expr_b = to_array_of_expr(arrays[b]);
      const exprt &value_b = expr_b.what();

      // 1. we got a[i]...b[j], given as edges on the stack
      // 2. add (i=j AND path_cond)=>a[i]=b[j]
      // 3. The path condition requires the update indices
      //    on the stack to be different from i.
      exprt::operandst cond;
      cond.reserve(path.size());
      weg_path_condition(path, index_a, cond);

      // a_i=value
      index_exprt a_i(arrays[a], index_a);
      // cond => a_i=b_i
      implies_exprt implication(conjunction(cond), equal_exprt(a_i, value_b));
      //#if ARRAY_SPEEDUP_DEBUG
      std::cout << "C2b: " << format(implication) << '\n';
      //#endif
      set_to_true(implication);
    }
    else if(arrays[b].id() == ID_array)
    {
      UNIMPLEMENTED;
    }
    else
    {
      DATA_INVARIANT_WITH_DIAGNOSTICS(
        arrays[b].id() == ID_nondet_symbol || arrays[b].id() == ID_symbol ||
          arrays[b].id() == ID_if,
        "expected symbol or if; got ",
        arrays[b].pretty());
    }

    if(a != b)
    {
      for(const auto &index_b : index_set_b)
      {
        if(must_be_different(index_a, index_b))
          continue;

        // 1. we got a[i]...b[j], given as edges on the stack
        // 2. add (i=j AND path_cond)=>a[i]=b[j]
        // 3. The path condition requires the update indices
        //    on the stack to be different from i.
        exprt::operandst cond;
        cond.reserve(path.size() + 1);
        cond.push_back(equal_exprt(index_a, index_b));
        weg_path_condition(path, index_a, cond);

        // a_i=b_i
        index_exprt a_i(arrays[a], index_a);
        index_exprt b_i(arrays[b], index_b);
        // cond => a_i=b_i
        implies_exprt implication(conjunction(cond), equal_exprt(a_i, b_i));
        //#if ARRAY_SPEEDUP_DEBUG
        std::cout << "C3: " << format(implication) << '\n';
        //#endif
        set_to_true(implication);
      }
    }
  }
}

void arrayst::add_array_constraints()
{
#if 0
  weg.output_dot(std::cerr);
#endif
#if ARRAY_SPEEDUP_DEBUG
  for(const auto &a : arrays)
  {
    std::cout << "array: " << format(a) << '\n';
  }
#endif

  // Implement Algorithms 7.4.1 and 7.4.2 by enumerating all simple paths
  // instead of iterating of all pairs of arrays and indices. Paths are
  // enumerated by performing depth-first search from each node.

  // auxiliary bit per node for DFS
  std::vector<bool> visited;
  visited.resize(weg.size());

  for(wegt::node_indext a = 0; a < arrays.size(); a++)
  {
#if ARRAY_SPEEDUP_DEBUG
    std::cout << "a is: " << format(arrays[a]) << '\n';
#endif

    // DFS from a_i to anything reachable in 'weg'
    std::fill(visited.begin(), visited.end(), false);

    weg_patht path;
    path.emplace_back(a, std::set<wegt::node_indext>());
    visited[a] = true;

    while(!path.empty())
    {
      // get next edge a->b
      stack_entryt &entry = path.back();

      if(!entry.edge.has_value())
      {
        if(weg[entry.n].out.empty())
        {
          // no successors
          path.pop_back();
          continue;
        }

        entry.edge = weg[entry.n].out.cbegin();
      }
      else if(std::next(*entry.edge) == weg[entry.n].out.end())
      {
        // no further successor
        path.pop_back();
        continue;
      }
      else
        ++(*entry.edge);

      wegt::node_indext b = (*entry.edge)->first;

      if(entry.path_nodes.find(b) != entry.path_nodes.end())
        continue; // already done it

      visited[b] = true;

      // add node 'b' to path
      path.emplace_back(b, entry.path_nodes);

      // process
      process_weg_path(path);
    }
  }

  // add the Ackermann constraints
  add_array_Ackermann_constraints();
}

#if 1
void arrayst::add_array_Ackermann_constraints()
{
  // this is quadratic!

#  if 0
  std::cout << "arrays.size(): " << arrays.size() << '\n';
#  endif

  // iterate over arrays
  for(std::size_t i = 0; i < arrays.size(); i++)
  {
    if(arrays[i].id() != ID_nondet_symbol && arrays[i].id() != ID_symbol)
      continue;

    const index_sett &index_set = index_map[i];

#  if 0
    std::cout << "index_set.size(): " << index_set.size() << '\n';
#  endif

    // iterate over indices, 2x!
    for(index_sett::const_iterator i1 = index_set.begin();
        i1 != index_set.end();
        i1++)
    {
      index_sett::const_iterator next = i1;
      next++;
      for(index_sett::const_iterator i2 = next; i2 != index_set.end(); i2++)
      {
        if(i1->is_constant() && i2->is_constant())
          continue;

        // index equality
        equal_exprt indices_equal(*i1, *i2);

        if(indices_equal.op0().type() != indices_equal.op1().type())
        {
          indices_equal.op1() =
            typecast_exprt(indices_equal.op1(), indices_equal.op0().type());
        }

        literalt indices_equal_lit = convert(indices_equal);

        if(indices_equal_lit != const_literal(false))
        {
          const typet &subtype = arrays[i].type().subtype();
          index_exprt index_expr1(arrays[i], *i1, subtype);

          index_exprt index_expr2 = index_expr1;
          index_expr2.index() = *i2;

          equal_exprt values_equal(index_expr1, index_expr2);
          prop.lcnf(!indices_equal_lit, convert(values_equal));

#  if ARRAY_SPEEDUP_DEBUG
          std::cout << "C4: " << format(indices_equal) << " => "
                    << format(values_equal) << '\n';
#  endif
        }
      }
    }
  }
}
#endif

std::string arrayst::enum_to_string(constraint_typet type)
{
  switch(type)
  {
  case constraint_typet::ARRAY_ACKERMANN:
    return "arrayAckermann";
  case constraint_typet::ARRAY_WITH:
    return "arrayWith";
  case constraint_typet::ARRAY_IF:
    return "arrayIf";
  case constraint_typet::ARRAY_OF:
    return "arrayOf";
  case constraint_typet::ARRAY_TYPECAST:
    return "arrayTypecast";
  case constraint_typet::ARRAY_CONSTANT:
    return "arrayConstant";
  case constraint_typet::ARRAY_COMPREHENSION:
    return "arrayComprehension";
  case constraint_typet::ARRAY_EQUALITY:
    return "arrayEquality";
  default:
    UNREACHABLE;
  }
}

void arrayst::display_array_constraint_count()
{
  json_objectt json_result;
  json_objectt &json_array_theory =
    json_result["arrayConstraints"].make_object();

  size_t num_constraints = 0;

  array_constraint_countt::iterator it = array_constraint_count.begin();
  while(it != array_constraint_count.end())
  {
    std::string contraint_type_string = enum_to_string(it->first);
    json_array_theory[contraint_type_string] =
      json_numbert(std::to_string(it->second));

    num_constraints += it->second;
    it++;
  }

  json_result["numOfConstraints"] =
    json_numbert(std::to_string(num_constraints));
  log.status() << ",\n" << json_result;
}
