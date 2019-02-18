//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <vector>

#include <triton/cpuSize.hpp>
#include <triton/exceptions.hpp>
#include <triton/symbolicExpression.hpp>
#include <triton/symbolicVariable.hpp>
#include <triton/tritonToZ3Ast.hpp>



namespace triton {
  namespace ast {

    TritonToZ3Ast::TritonToZ3Ast(bool eval)
      : context() {
      this->isEval = eval;
    }


    triton::__uint TritonToZ3Ast::getUintValue(const z3::expr& expr) {
      if (!expr.is_int())
        throw triton::exceptions::Exception("TritonToZ3Ast::getUintValue(): The ast is not a numerical value.");

      #if defined(__x86_64__) || defined(_M_X64)
      return expr.get_numeral_uint64();
      #endif
      #if defined(__i386) || defined(_M_IX86)
      return expr.get_numeral_uint();
      #endif
    }


    std::string TritonToZ3Ast::getStringValue(const z3::expr& expr) {
      return Z3_get_numeral_string(this->context, expr);
    }


    z3::expr TritonToZ3Ast::convert(const triton::ast::SharedAbstractNode& node) {
      std::unordered_map<triton::ast::SharedAbstractNode, z3::expr> results;
      std::deque<triton::ast::SharedAbstractNode> nodes;

      triton::ast::nodesExtraction(&nodes, node, true /* unroll*/, true /* revert */);

      for (auto&& n : nodes) {
        results.insert(std::make_pair(n, this->do_convert(n, &results)));
      }

      return results.at(node);
    }


    z3::expr TritonToZ3Ast::do_convert(const triton::ast::SharedAbstractNode& node, std::unordered_map<triton::ast::SharedAbstractNode, z3::expr>* results) {
      if (node == nullptr)
        throw triton::exceptions::AstTranslations("TritonToZ3Ast::do_convert(): node cannot be null.");

      /* Prepare z3's children */
      std::vector<z3::expr> children;
      for (auto&& n : node->getChildren()) {
        children.emplace_back(results->at(n));
      }

      switch (node->getType()) {
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
          triton::uint32 rot = reinterpret_cast<triton::ast::IntegerNode*>(node->getChildren()[1].get())->getInteger().convert_to<triton::uint32>();
          return to_expr(this->context, Z3_mk_rotate_left(this->context, rot, children[0]));
        }

        case BVROR_NODE: {
          triton::uint32 rot = reinterpret_cast<triton::ast::IntegerNode*>(node->getChildren()[1].get())->getInteger().convert_to<triton::uint32>();
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

        case BV_NODE: {
          z3::expr value        = children[0];
          z3::expr size         = children[1];
          triton::uint32 bvsize = static_cast<triton::uint32>(this->getUintValue(size));
          return this->context.bv_val(this->getStringValue(value).c_str(), bvsize);
        }

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

        case EXTRACT_NODE: {
          z3::expr high     = children[0];
          z3::expr low      = children[1];
          z3::expr value    = children[2];
          triton::uint32 hv = static_cast<triton::uint32>(this->getUintValue(high));
          triton::uint32 lv = static_cast<triton::uint32>(this->getUintValue(low));

          return to_expr(this->context, Z3_mk_extract(this->context, hv, lv, value));
        }

        case IFF_NODE: {
          z3::expr op1 = children[0];
          z3::expr op2 = children[1];

          return to_expr(this->context, Z3_mk_iff(this->context, op1, op2));
        }

        case INTEGER_NODE: {
          std::string value(reinterpret_cast<triton::ast::IntegerNode*>(node.get())->getInteger().convert_to<std::string>());
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
          if (!currentValue.get_sort().is_bool()) {
            throw triton::exceptions::AstTranslations("TritonToZ3Ast::LandNode(): Land can be apply only on bool value.");
          }
          z3::expr nextValue(this->context);

          for (triton::uint32 idx = 1; idx < children.size(); idx++) {
            nextValue = children[idx];
            if (!nextValue.get_sort().is_bool()) {
              throw triton::exceptions::AstTranslations("TritonToZ3Ast::LandNode(): Land can be apply only on bool value.");
            }
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
          if (!value.get_sort().is_bool()) {
            throw triton::exceptions::AstTranslations("TritonToZ3Ast::LnotNode(): Lnot can be apply only on bool value.");
          }
          return to_expr(this->context, Z3_mk_not(this->context, value));
        }

        case LOR_NODE: {
          z3::expr currentValue = children[0];
          if (!currentValue.get_sort().is_bool()) {
            throw triton::exceptions::AstTranslations("TritonToZ3Ast::LnotNode(): Lnot can be apply only on bool value.");
          }
          z3::expr nextValue(this->context);

          for (triton::uint32 idx = 1; idx < children.size(); idx++) {
            nextValue = children[idx];
            if (!nextValue.get_sort().is_bool()) {
              throw triton::exceptions::AstTranslations("TritonToZ3Ast::LnotNode(): Lnot can be apply only on bool value.");
            }
            Z3_ast ops[] = {currentValue, nextValue};
            currentValue = to_expr(this->context, Z3_mk_or(this->context, 2, ops));
          }

          return currentValue;
        }

        case REFERENCE_NODE:
          return results->at(reinterpret_cast<triton::ast::ReferenceNode*>(node.get())->getSymbolicExpression()->getAst());

        case STRING_NODE: {
          std::string value = reinterpret_cast<triton::ast::StringNode*>(node.get())->getString();

          if (this->symbols.find(value) == this->symbols.end())
            throw triton::exceptions::AstTranslations("TritonToZ3Ast::do_convert(): [STRING_NODE] Symbols not found.");

          return results->at(this->symbols[value]);
        }

        case SX_NODE: {
          z3::expr ext        = children[0];
          z3::expr value      = children[1];
          triton::uint32 extv = static_cast<triton::uint32>(this->getUintValue(ext));

          return to_expr(this->context, Z3_mk_sign_ext(this->context, extv, value));
        }

        case VARIABLE_NODE: {
          const triton::engines::symbolic::SharedSymbolicVariable& symVar = reinterpret_cast<triton::ast::VariableNode*>(node.get())->getSymbolicVariable();

          /* Record variable */
          this->variables[symVar->getName()] = symVar;

          /* If the conversion is used to evaluate a node, we concretize symbolic variables */
          if (this->isEval) {
            triton::uint512 value = reinterpret_cast<triton::ast::VariableNode*>(node.get())->evaluate();
            std::string strValue(value.convert_to<std::string>());
            return this->context.bv_val(strValue.c_str(), symVar->getSize());
          }

          /* Otherwise, we keep the symbolic variables for a real conversion */
          return this->context.bv_const(symVar->getName().c_str(), symVar->getSize());
        }

        case ZX_NODE: {
          z3::expr ext        = children[0];
          z3::expr value      = children[1];
          triton::uint32 extv = static_cast<triton::uint32>(this->getUintValue(ext));

          return to_expr(this->context, Z3_mk_zero_ext(this->context, extv, value));
        }

        default:
          throw triton::exceptions::AstTranslations("TritonToZ3Ast::do_convert(): Invalid kind of node.");
      }
    }

  }; /* ast namespace */
}; /* triton namespace */
