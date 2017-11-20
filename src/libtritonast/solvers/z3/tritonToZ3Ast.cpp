//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <tritonast/exceptions.hpp>
#include <tritonast/nodes.hpp>
#include <tritonast/solvers/z3/tritonToZ3Ast.hpp>

#include <stack>


namespace {
  template <class T>
  z3::expr pop_back(T & c) {
    z3::expr N = c.top();
    c.pop();
    return N;
  }
}

namespace triton {
  namespace ast {

    TritonToZ3Ast::TritonToZ3Ast(bool eval)
      : isEval(eval)
      , context()
    {}


    TritonToZ3Ast::__uint TritonToZ3Ast::getUintValue(const z3::expr& expr) {
      __uint result = 0;

      if (!expr.is_int())
        throw triton::ast::exceptions::Exception("TritonToZ3Ast::getUintValue(): The ast is not a numerical value.");

      #if defined(__x86_64__) || defined(_M_X64)
      Z3_get_numeral_uint64(this->context, expr, &result);
      #endif
      #if defined(__i386) || defined(_M_IX86)
      Z3_get_numeral_uint(this->context, expr, &result);
      #endif

      return result;
    }


    std::string TritonToZ3Ast::getStringValue(const z3::expr& expr) {
      return Z3_get_numeral_string(this->context, expr);
    }


    z3::expr TritonToZ3Ast::convert(triton::ast::AbstractNode* node) {
      if (node == nullptr)
        throw triton::ast::exceptions::AstTranslations("TritonToZ3Ast::convert(): node cannot be null.");

      std::stack<std::pair<triton::ast::AbstractNode*, bool>> ToVisit;
      std::stack<z3::expr> ComputedExpr;

      ToVisit.emplace(node, false);

//      std::cout << node << std::endl;
      while(!ToVisit.empty()) {
 //       std::cout << ToVisit.size() << std::endl;
//        if(ToVisit.size() > 10)
  //        break;
        auto p = ToVisit.top();
  //      std::cout << p.first << "/" << p.second << "/" << p.first->getChildren().size() << "\n";
        ToVisit.pop();
        if(p.second) {
          ComputedExpr.emplace(do_convert(p.first, ComputedExpr));
        } else if(dynamic_cast<LetNode*>(p.first)) {
          std::string vname = reinterpret_cast<triton::ast::StringNode*>(node->getChildren()[0].get())->getValue();
          this->symbols.emplace(vname, do_convert(p.first->getChildren()[1].get(), ComputedExpr));
          ComputedExpr.emplace(do_convert(p.first->getChildren()[2].get(), ComputedExpr));
          this->symbols.erase(vname);
        } else {
          ToVisit.emplace(p.first, true);
          for(triton::ast::SharedAbstractNode const& n: p.first->getChildren()) {
            ToVisit.emplace(n.get(), false);
          }
        }
      }

      assert(ComputedExpr.size() == 1);
      return ComputedExpr.top();
    }

    z3::expr TritonToZ3Ast::do_convert(triton::ast::AbstractNode* node, std::stack<z3::expr> & childs) {
      switch (node->getKind()) {
        case BVADD_NODE: {
          z3::expr lop = pop_back(childs);
          z3::expr rop = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvadd(this->context, rop, lop));
                         }

        case BVAND_NODE: {
          z3::expr lop = pop_back(childs);
          z3::expr rop = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvand(this->context, rop, lop));
                         }

        case BVASHR_NODE: {
          z3::expr rop = pop_back(childs);
          z3::expr lop = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvashr(this->context, rop, lop));
                          }

        case BVLSHR_NODE: {
          z3::expr rop = pop_back(childs);
          z3::expr lop = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvlshr(this->context, rop, lop));
                          }

        case BVMUL_NODE: {
          z3::expr lop = pop_back(childs);
          z3::expr rop = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvmul(this->context, rop, lop));
                         }

        case BVNAND_NODE: {
          z3::expr lop = pop_back(childs);
          z3::expr rop = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvnand(this->context, rop, lop));
                          }

        case BVNEG_NODE: {
          z3::expr op = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvneg(this->context, op));
                         }

        case BVNOR_NODE: {
          z3::expr lop = pop_back(childs);
          z3::expr rop = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvnor(this->context, rop, lop));
                         }

        case BVNOT_NODE: {
          z3::expr op = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvnot(this->context, op));
                         }

        case BVOR_NODE: {
          z3::expr lop = pop_back(childs);
          z3::expr rop = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvor(this->context, rop, lop));
                        }

        case BVROL_NODE: {
          triton::uint32 op1 = pop_back(childs).get_numeral_uint();
          z3::expr toRol = pop_back(childs);
          return to_expr(this->context, Z3_mk_rotate_left(this->context, op1, toRol));
        }

        case BVROR_NODE: {
          triton::uint32 op1 = pop_back(childs).get_numeral_uint();
          z3::expr toRor = pop_back(childs);
          return to_expr(this->context, Z3_mk_rotate_right(this->context, op1, toRor));
        }

        case BVSDIV_NODE: {
          z3::expr lop = pop_back(childs);
          z3::expr rop = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvsdiv(this->context, lop, rop));
          }

        case BVSGE_NODE: {
          z3::expr lop = pop_back(childs);
          z3::expr rop = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvsge(this->context, lop, rop));
         }

        case BVSGT_NODE: {
          z3::expr lop = pop_back(childs);
          z3::expr rop = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvsgt(this->context, lop, rop));
         }

        case BVSHL_NODE: {
          z3::expr lop = pop_back(childs);
          z3::expr rop = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvshl(this->context, lop, rop));
         }

        case BVSLE_NODE: {
          z3::expr lop = pop_back(childs);
          z3::expr rop = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvsle(this->context, lop, rop));
         }

        case BVSLT_NODE: {
          z3::expr lop = pop_back(childs);
          z3::expr rop = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvslt(this->context, lop, rop));
         }

        case BVSMOD_NODE: {
          z3::expr lop = pop_back(childs);
          z3::expr rop = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvsmod(this->context, lop, rop));
         }

        case BVSREM_NODE: {
          z3::expr lop = pop_back(childs);
          z3::expr rop = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvsrem(this->context, lop, rop));
         }

        case BVSUB_NODE: {
          z3::expr lop = pop_back(childs);
          z3::expr rop = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvsub(this->context, lop, rop));
         }

        case BVUDIV_NODE: {
          z3::expr lop = pop_back(childs);
          z3::expr rop = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvudiv(this->context, lop, rop));
         }

        case BVUGE_NODE: {
          z3::expr lop = pop_back(childs);
          z3::expr rop = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvuge(this->context, lop, rop));
         }

        case BVUGT_NODE: {
          z3::expr lop = pop_back(childs);
          z3::expr rop = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvugt(this->context, lop, rop));
         }

        case BVULE_NODE: {
          z3::expr lop = pop_back(childs);
          z3::expr rop = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvule(this->context, lop, rop));
         }

        case BVULT_NODE: {
          z3::expr lop = pop_back(childs);
          z3::expr rop = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvult(this->context, lop, rop));
         }

        case BVUREM_NODE: {
          z3::expr lop = pop_back(childs);
          z3::expr rop = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvurem(this->context, lop, rop));
         }

        case BVXNOR_NODE: {
          z3::expr lop = pop_back(childs);
          z3::expr rop = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvxnor(this->context, lop, rop));
         }

        case BVXOR_NODE: {
          z3::expr lop = pop_back(childs);
          z3::expr rop = pop_back(childs);
          return to_expr(this->context, Z3_mk_bvxor(this->context, lop, rop));
         }

        case BV_NODE: {
          z3::expr value        = pop_back(childs);
          z3::expr size         = pop_back(childs);
          triton::uint32 bvsize = static_cast<triton::uint32>(this->getUintValue(size));
          return this->context.bv_val(this->getStringValue(value).c_str(), bvsize);
        }

        case CONCAT_NODE: {
          const std::vector<triton::ast::SharedAbstractNode>& children = node->getChildren();

          z3::expr currentValue = pop_back(childs);

          for (triton::uint32 idx = 1; idx < children.size(); idx++) {
            currentValue = to_expr(this->context, Z3_mk_concat(this->context, currentValue, pop_back(childs)));
          }

          return currentValue;
        }

        case DECIMAL_NODE: {
          std::string value(reinterpret_cast<triton::ast::DecimalNode*>(node)->getValue());
          return this->context.int_val(value.c_str());
        }

        case DISTINCT_NODE: {
          z3::expr op2 = pop_back(childs);
          z3::expr op1 = pop_back(childs);
          Z3_ast ops[] = {op1, op2};

          return to_expr(this->context, Z3_mk_distinct(this->context, 2, ops));
        }

        case EQUAL_NODE: {
          z3::expr lop = pop_back(childs);
          z3::expr rop = pop_back(childs);
          return to_expr(this->context, Z3_mk_eq(this->context, lop, rop));
         }

        case EXTRACT_NODE: {
          z3::expr high     = pop_back(childs);
          z3::expr low      = pop_back(childs);
          z3::expr value    = pop_back(childs);
          triton::uint32 hv = static_cast<triton::uint32>(this->getUintValue(high));
          triton::uint32 lv = static_cast<triton::uint32>(this->getUintValue(low));

          return to_expr(this->context, Z3_mk_extract(this->context, hv, lv, value));
        }

        case ITE_NODE: {
          z3::expr op1 = pop_back(childs); // if false
          z3::expr op2 = pop_back(childs); // if true
          z3::expr op3 = pop_back(childs); // condition

          return to_expr(this->context, Z3_mk_ite(this->context, op1, op2, op3));
        }

        case LAND_NODE: {
          const std::vector<triton::ast::SharedAbstractNode>& children = node->getChildren();

          z3::expr currentValue = pop_back(childs);
          if (!currentValue.get_sort().is_bool()) {
            throw triton::ast::exceptions::AstTranslations("TritonToZ3Ast::LandNode(): Land can be apply only on bool value.");
          }
          for (triton::uint32 idx = 1; idx < children.size(); idx++) {
            z3::expr nextValue = pop_back(childs);
            if (!nextValue.get_sort().is_bool()) {
              throw triton::ast::exceptions::AstTranslations("TritonToZ3Ast::LandNode(): Land can be apply only on bool value.");
            }
            Z3_ast ops[] = {currentValue, nextValue};
            currentValue = to_expr(this->context, Z3_mk_and(this->context, 2, ops));
          }

          return currentValue;
        }


        case LET_NODE:
          assert(false && "Should not be visited");

        case LNOT_NODE: {
          z3::expr value = pop_back(childs);
          if (!value.get_sort().is_bool()) {
            throw triton::ast::exceptions::AstTranslations("TritonToZ3Ast::LnotNode(): Lnot can be apply only on bool value.");
          }
          return to_expr(this->context, Z3_mk_not(this->context, value));
        }

        case LOR_NODE: {
          const std::vector<triton::ast::SharedAbstractNode>& children = node->getChildren();

          z3::expr currentValue = pop_back(childs);
          if (!currentValue.get_sort().is_bool()) {
            throw triton::ast::exceptions::AstTranslations("TritonToZ3Ast::LnotNode(): Lnot can be apply only on bool value.");
          }

          for (triton::uint32 idx = 1; idx < children.size(); idx++) {
            z3::expr nextValue = pop_back(childs);
            if (!nextValue.get_sort().is_bool()) {
              throw triton::ast::exceptions::AstTranslations("TritonToZ3Ast::LnotNode(): Lnot can be apply only on bool value.");
            }
            Z3_ast ops[] = {currentValue, nextValue};
            currentValue = to_expr(this->context, Z3_mk_or(this->context, 2, ops));
          }

          return currentValue;
        }

        case REFERENCE_NODE: {
          triton::uint32 id = reinterpret_cast<triton::ast::ReferenceNode*>(node)->getId();

          if (this->refs.find(id) == this->refs.end()) {
            this->refs.emplace(id, this->convert(reinterpret_cast<triton::ast::ReferenceNode*>(node)->getAst().get()));
          }

          // FIXME: We already find it
          return this->refs.at(id);
       }

        case STRING_NODE: {
          std::string value = reinterpret_cast<triton::ast::StringNode*>(node)->getValue();

          if (this->symbols.find(value) == this->symbols.end()) {
            throw triton::ast::exceptions::AstTranslations("TritonToZ3Ast::convert(): [STRING_NODE] Symbols not found.");
          }

          // FIXME: We already find it
          return this->symbols.at(value);
        }

        case SX_NODE: {
          z3::expr ext        = pop_back(childs);
          z3::expr value      = pop_back(childs);
          triton::uint32 extv = static_cast<triton::uint32>(this->getUintValue(ext));

          return to_expr(this->context, Z3_mk_sign_ext(this->context, extv, value));
        }

        case VARIABLE_NODE: {
          auto *vnode = reinterpret_cast<triton::ast::VariableNode*>(node);
          triton::uint32 varSize = vnode->getBitvectorSize();
          std::string const& varName = vnode->getVarName();

          /* If the conversion is used to evaluate a node, we concretize symbolic variables */
          if (this->isEval) {
            triton::uint512 value = reinterpret_cast<triton::ast::VariableNode*>(node)->evaluate();
            std::string strValue(value);
            return this->context.bv_val(varName.c_str(), varSize);
          }

          /* Otherwise, we keep the symbolic variables for a real conversion */
          return this->context.bv_const(varName.c_str(), varSize);
        }

        case ZX_NODE: {
          z3::expr ext        = pop_back(childs);
          z3::expr value      = pop_back(childs);
          triton::uint32 extv = static_cast<triton::uint32>(this->getUintValue(ext));

          return to_expr(this->context, Z3_mk_zero_ext(this->context, extv, value));
        }

        default:
          throw triton::ast::exceptions::AstTranslations("TritonToZ3Ast::convert(): Invalid kind of node.");
      }
    }

  }; /* ast namespace */
}; /* triton namespace */
