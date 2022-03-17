//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <vector>

#include <triton/coreUtils.hpp>
#include <triton/cpuSize.hpp>
#include <triton/exceptions.hpp>
#include <triton/symbolicExpression.hpp>
#include <triton/symbolicVariable.hpp>
#include <triton/tritonToZ3.hpp>



namespace triton {
  namespace ast {

    TritonToZ3::TritonToZ3(bool eval)
      : context() {
      this->isEval = eval;
    }


    TritonToZ3::~TritonToZ3() {
      /* See #828: Release ownership before calling container destructor */
      this->symbols.clear();
      this->variables.clear();
    }


    std::string TritonToZ3::getStringValue(const z3::expr& expr) {
      return Z3_get_numeral_string(this->context, expr);
    }


    z3::expr TritonToZ3::convert(const triton::ast::SharedAbstractNode& node) {
      std::unordered_map<triton::ast::SharedAbstractNode, z3::expr> results;

      auto nodes = triton::ast::childrenExtraction(node, true /* unroll*/, true /* revert */);

      for (auto&& n : nodes) {
        results.insert(std::make_pair(n, this->do_convert(n, &results)));
      }

      return results.at(node);
    }


    z3::expr TritonToZ3::do_convert(const triton::ast::SharedAbstractNode& node, std::unordered_map<triton::ast::SharedAbstractNode, z3::expr>* results) {
      if (node == nullptr)
        throw triton::exceptions::AstLifting("TritonToZ3::do_convert(): node cannot be null.");

      /* Prepare z3's children */
      std::vector<z3::expr> children;
      for (auto&& n : node->getChildren()) {
        children.emplace_back(results->at(n));
      }

      switch (node->getType()) {

        case ARRAY_NODE: {
          auto size  = triton::ast::getInteger<triton::uint32>(node->getChildren()[0]);
          auto isort = this->context.bv_sort(size);
          auto value = this->context.bv_val(0, 8);
          return to_expr(this->context, Z3_mk_const_array(this->context, isort, value));
        }

        case BSWAP_NODE: {
          auto bvsize = node->getBitvectorSize();
          auto retval = to_expr(this->context, Z3_mk_bvand(this->context, children[0], this->context.bv_val(0xff, bvsize)));
          for (triton::uint32 index = 8 ; index != bvsize ; index += triton::bitsize::byte) {
            retval = to_expr(this->context, Z3_mk_bvshl(this->context, retval, this->context.bv_val(8, bvsize)));
            retval = to_expr(this->context, Z3_mk_bvor(this->context, retval,
                       to_expr(this->context, Z3_mk_bvand(this->context,
                         to_expr(this->context, Z3_mk_bvlshr(this->context, children[0], this->context.bv_val(index, bvsize))),
                                                this->context.bv_val(0xff, bvsize)
                                              ))
                                            ));
          }
          return to_expr(this->context, retval);
        }

        case BVADD_NODE:
          return to_expr(this->context, Z3_mk_bvadd(this->context, children[0], children[1]));

        case BVAND_NODE:
          return to_expr(this->context, Z3_mk_bvand(this->context, children[0], children[1]));

        case BVASHR_NODE:
          return to_expr(this->context, Z3_mk_bvashr(this->context, children[0], children[1]));

        case BVLSHR_NODE:
          return to_expr(this->context, Z3_mk_bvlshr(this->context, children[0], children[1]));

        case BVMUL_NODE:
          return to_expr(this->context, Z3_mk_bvmul(this->context, children[0], children[1]));

        case BVNAND_NODE:
          return to_expr(this->context, Z3_mk_bvnand(this->context, children[0], children[1]));

        case BVNEG_NODE:
          return to_expr(this->context, Z3_mk_bvneg(this->context, children[0]));

        case BVNOR_NODE:
          return to_expr(this->context, Z3_mk_bvnor(this->context, children[0], children[1]));

        case BVNOT_NODE:
          return to_expr(this->context, Z3_mk_bvnot(this->context, children[0]));

        case BVOR_NODE:
          return to_expr(this->context, Z3_mk_bvor(this->context, children[0], children[1]));

        case BVROL_NODE: {
          triton::uint32 rot = triton::ast::getInteger<triton::uint32>(node->getChildren()[1]);
          return to_expr(this->context, Z3_mk_rotate_left(this->context, rot, children[0]));
        }

        case BVROR_NODE: {
          triton::uint32 rot = triton::ast::getInteger<triton::uint32>(node->getChildren()[1]);
          return to_expr(this->context, Z3_mk_rotate_right(this->context, rot, children[0]));
        }

        case BVSDIV_NODE:
          return to_expr(this->context, Z3_mk_bvsdiv(this->context, children[0], children[1]));

        case BVSGE_NODE:
          return to_expr(this->context, Z3_mk_bvsge(this->context, children[0], children[1]));

        case BVSGT_NODE:
          return to_expr(this->context, Z3_mk_bvsgt(this->context, children[0], children[1]));

        case BVSHL_NODE:
          return to_expr(this->context, Z3_mk_bvshl(this->context, children[0], children[1]));

        case BVSLE_NODE:
          return to_expr(this->context, Z3_mk_bvsle(this->context, children[0], children[1]));

        case BVSLT_NODE:
          return to_expr(this->context, Z3_mk_bvslt(this->context, children[0], children[1]));

        case BVSMOD_NODE:
          return to_expr(this->context, Z3_mk_bvsmod(this->context, children[0], children[1]));

        case BVSREM_NODE:
          return to_expr(this->context, Z3_mk_bvsrem(this->context, children[0], children[1]));

        case BVSUB_NODE:
          return to_expr(this->context, Z3_mk_bvsub(this->context, children[0], children[1]));

        case BVUDIV_NODE:
          return to_expr(this->context, Z3_mk_bvudiv(this->context, children[0], children[1]));

        case BVUGE_NODE:
          return to_expr(this->context, Z3_mk_bvuge(this->context, children[0], children[1]));

        case BVUGT_NODE:
          return to_expr(this->context, Z3_mk_bvugt(this->context, children[0], children[1]));

        case BVULE_NODE:
          return to_expr(this->context, Z3_mk_bvule(this->context, children[0], children[1]));

        case BVULT_NODE:
          return to_expr(this->context, Z3_mk_bvult(this->context, children[0], children[1]));

        case BVUREM_NODE:
          return to_expr(this->context, Z3_mk_bvurem(this->context, children[0], children[1]));

        case BVXNOR_NODE:
          return to_expr(this->context, Z3_mk_bvxnor(this->context, children[0], children[1]));

        case BVXOR_NODE:
          return to_expr(this->context, Z3_mk_bvxor(this->context, children[0], children[1]));

        case BV_NODE:
          return this->context.bv_val(this->getStringValue(children[0]).c_str(), children[1].get_numeral_uint());

        case CONCAT_NODE: {
          z3::expr currentValue = children[0];
          z3::expr nextValue(this->context);

          // Child[0] is the LSB
          for (triton::uint32 idx = 1; idx < children.size(); idx++) {
            nextValue = children[idx];
            currentValue = to_expr(this->context, Z3_mk_concat(this->context, currentValue, nextValue));
          }

          return currentValue;
        }

        case DISTINCT_NODE: {
          z3::expr op1 = children[0];
          z3::expr op2 = children[1];
          Z3_ast ops[] = {op1, op2};

          return to_expr(this->context, Z3_mk_distinct(this->context, 2, ops));
        }

        case EQUAL_NODE:
          return to_expr(this->context, Z3_mk_eq(this->context, children[0], children[1]));

        case EXTRACT_NODE:
          return to_expr(this->context, Z3_mk_extract(this->context, children[0].get_numeral_uint(), children[1].get_numeral_uint(), children[2]));

        case FORALL_NODE: {
          triton::uint32 size = static_cast<triton::uint32>(node->getChildren().size() - 1);
          Z3_app* vars = new Z3_app[size];

          for (triton::uint32 i = 0; i != size; i++) {
            vars[i] = children[i];
          }

          z3::expr e = to_expr(this->context, Z3_mk_forall_const(this->context, 0, size, vars, 0, 0, children[size]));
          delete[] vars;

          return e;
        }

        case IFF_NODE: {
          z3::expr op1 = children[0];
          z3::expr op2 = children[1];

          return to_expr(this->context, Z3_mk_iff(this->context, op1, op2));
        }

        case INTEGER_NODE: {
          std::string value(triton::ast::getInteger<std::string>(node));
          return this->context.int_val(value.c_str());
        }

        case ITE_NODE: {
          z3::expr op1 = children[0]; // condition
          z3::expr op2 = children[1]; // if true
          z3::expr op3 = children[2]; // if false

          return to_expr(this->context, Z3_mk_ite(this->context, op1, op2, op3));
        }

        case LAND_NODE: {
          z3::expr currentValue = children[0];
          z3::expr nextValue(this->context);

          for (triton::uint32 idx = 1; idx < children.size(); idx++) {
            nextValue = children[idx];
            Z3_ast ops[] = {currentValue, nextValue};
            currentValue = to_expr(this->context, Z3_mk_and(this->context, 2, ops));
          }

          return currentValue;
        }

        case LET_NODE: {
          std::string symbol    = reinterpret_cast<triton::ast::StringNode*>(node->getChildren()[0].get())->getString();
          this->symbols[symbol] = node->getChildren()[1];

          return children[2];
        }

        case LNOT_NODE: {
          z3::expr value = children[0];
          return to_expr(this->context, Z3_mk_not(this->context, value));
        }

        case LOR_NODE: {
          z3::expr currentValue = children[0];
          z3::expr nextValue(this->context);

          for (triton::uint32 idx = 1; idx < children.size(); idx++) {
            nextValue = children[idx];
            Z3_ast ops[] = {currentValue, nextValue};
            currentValue = to_expr(this->context, Z3_mk_or(this->context, 2, ops));
          }

          return currentValue;
        }

        case LXOR_NODE: {
          z3::expr currentValue = children[0];
          z3::expr nextValue(this->context);

          for (triton::uint32 idx = 1; idx < children.size(); idx++) {
            nextValue = children[idx];
            currentValue = to_expr(this->context, Z3_mk_xor(this->context, currentValue, nextValue));
          }

          return currentValue;
        }

        case REFERENCE_NODE:
          return results->at(reinterpret_cast<triton::ast::ReferenceNode*>(node.get())->getSymbolicExpression()->getAst());

        case STRING_NODE: {
          std::string value = reinterpret_cast<triton::ast::StringNode*>(node.get())->getString();

          if (this->symbols.find(value) == this->symbols.end())
            throw triton::exceptions::AstLifting("TritonToZ3::do_convert(): [STRING_NODE] Symbols not found.");

          return results->at(this->symbols[value]);
        }

        case SELECT_NODE:
          return to_expr(this->context, Z3_mk_select(this->context, children[0], children[1]));

        case STORE_NODE:
          return to_expr(this->context, Z3_mk_store(this->context, children[0], children[1], children[2]));

        case SX_NODE:
          return to_expr(this->context, Z3_mk_sign_ext(this->context, children[0].get_numeral_uint(), children[1]));

        case VARIABLE_NODE: {
          const triton::engines::symbolic::SharedSymbolicVariable& symVar = reinterpret_cast<triton::ast::VariableNode*>(node.get())->getSymbolicVariable();

          /* Record variable */
          this->variables[symVar->getName()] = symVar;

          /* If the conversion is used to evaluate a node, we concretize symbolic variables */
          if (this->isEval) {
            triton::uint512 value = reinterpret_cast<triton::ast::VariableNode*>(node.get())->evaluate();
            return this->context.bv_val(triton::utils::toString(value).c_str(), symVar->getSize());
          }

          /* Otherwise, we keep the symbolic variables for a real conversion */
          return this->context.bv_const(symVar->getName().c_str(), symVar->getSize());
        }

        case ZX_NODE:
          return to_expr(this->context, Z3_mk_zero_ext(this->context, children[0].get_numeral_uint(), children[1]));

        default:
          throw triton::exceptions::AstLifting("TritonToZ3::do_convert(): Invalid kind of node.");
      }
    }

  }; /* ast namespace */
}; /* triton namespace */
