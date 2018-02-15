//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <stack>

#include <triton/cpuSize.hpp>
#include <triton/exceptions.hpp>
#include <triton/tritonToZ3Ast.hpp>

#define MAKE_Z3_LOGGED(x) _Z3_ast* log_##x(Z3_context ctx, Z3_ast a, Z3_ast b) { printf(#x " called\n"); return x(ctx, a, b); }

#define MAKE_Z3_LOGGED1(x) _Z3_ast* log_##x(Z3_context ctx, Z3_ast a) { printf(#x " called\n"); return x(ctx, a); }

#define MAKE_Z3_LOGGED2(x) _Z3_ast* log_##x(Z3_context ctx, uint32_t a, Z3_ast b) { printf(#x " called\n"); return x(ctx, a, b); }

#define MAKE_Z3_LOGGED3(x) _Z3_ast* log_##x(Z3_context ctx, Z3_ast a, Z3_ast b, Z3_ast c) { printf(#x " called\n"); return x(ctx, a, b, c); }

#define MAKE_Z3_LOGGED4(x) _Z3_ast* log_##x(Z3_context ctx, uint32_t a, uint32_t b, Z3_ast c) { printf(#x " called\n"); return x(ctx, a, b, c); }

#define MAKE_Z3_LOGGED5(x) _Z3_ast* log_##x(Z3_context ctx, uint32_t a, Z3_ast* ops) { printf(#x " called\n"); return x(ctx, a, ops); }

MAKE_Z3_LOGGED(Z3_mk_bvadd);
MAKE_Z3_LOGGED(Z3_mk_bvand);
MAKE_Z3_LOGGED(Z3_mk_bvashr);
MAKE_Z3_LOGGED(Z3_mk_bvlshr);
MAKE_Z3_LOGGED(Z3_mk_bvmul);
MAKE_Z3_LOGGED(Z3_mk_bvnand);
MAKE_Z3_LOGGED(Z3_mk_bvnor);
MAKE_Z3_LOGGED(Z3_mk_bvor);
MAKE_Z3_LOGGED(Z3_mk_bvsdiv);
MAKE_Z3_LOGGED(Z3_mk_bvsge);
MAKE_Z3_LOGGED(Z3_mk_bvsgt);
MAKE_Z3_LOGGED(Z3_mk_bvshl);
MAKE_Z3_LOGGED(Z3_mk_bvsle);
MAKE_Z3_LOGGED(Z3_mk_bvslt);
MAKE_Z3_LOGGED(Z3_mk_bvsmod);
MAKE_Z3_LOGGED(Z3_mk_bvsrem);
MAKE_Z3_LOGGED(Z3_mk_bvsub);
MAKE_Z3_LOGGED(Z3_mk_bvudiv);
MAKE_Z3_LOGGED(Z3_mk_bvuge);
MAKE_Z3_LOGGED(Z3_mk_bvugt);
MAKE_Z3_LOGGED(Z3_mk_bvule);
MAKE_Z3_LOGGED(Z3_mk_bvult);
MAKE_Z3_LOGGED(Z3_mk_bvurem);
MAKE_Z3_LOGGED(Z3_mk_bvxnor);
MAKE_Z3_LOGGED(Z3_mk_bvxor);
MAKE_Z3_LOGGED(Z3_mk_eq);
MAKE_Z3_LOGGED1(Z3_mk_bvneg);
MAKE_Z3_LOGGED1(Z3_mk_bvnot);
MAKE_Z3_LOGGED1(Z3_mk_not);
MAKE_Z3_LOGGED(Z3_mk_concat);
MAKE_Z3_LOGGED5(Z3_mk_and);
MAKE_Z3_LOGGED5(Z3_mk_or);
MAKE_Z3_LOGGED5(Z3_mk_distinct);
MAKE_Z3_LOGGED2(Z3_mk_sign_ext);
MAKE_Z3_LOGGED2(Z3_mk_zero_ext);
MAKE_Z3_LOGGED2(Z3_mk_rotate_right);
MAKE_Z3_LOGGED2(Z3_mk_rotate_left);
MAKE_Z3_LOGGED3(Z3_mk_ite);
MAKE_Z3_LOGGED4(Z3_mk_extract);


namespace triton {
  namespace ast {
    static bool setZ3logging = Z3_open_log("/tmp/z3.new.code.log");

    class NodeLogger {
      public:
        NodeLogger(triton::ast::AbstractNode* node) : node_(node) {};
        ~NodeLogger() {
          triton::uint512 hash = node_->hash(10);
          printf("[D] Processing %16.16lx kind %d, children are ", (uint64_t)hash, node_->getKind());
          for (const auto& childnode : node_->getChildren()) {
            printf("%16.16lx ", (uint64_t)childnode->hash(10));
          }
          printf("\n");
        }
      private:
        triton::ast::AbstractNode* node_;
    };

    TritonToZ3Ast::TritonToZ3Ast(triton::engines::symbolic::SymbolicEngine* symbolicEngine, bool eval)
      : context() {
      if (symbolicEngine == nullptr)
        throw triton::exceptions::AstTranslations("TritonToZ3Ast::TritonToZ3Ast(): The symbolicEngine API cannot be null.");

      this->symbolicEngine = symbolicEngine;
      this->isEval = eval;
    }

    triton::__uint TritonToZ3Ast::getUintValue(const z3::expr& expr) {
      triton::__uint result = 0;

      if (!expr.is_int())
        throw triton::exceptions::Exception("TritonToZ3Ast::getUintValue(): The ast is not a numerical value.");

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

    typedef _Z3_ast* (*UnaryZ3Function)(Z3_context, Z3_ast);
    typedef _Z3_ast* (*BinaryZ3Function)(Z3_context, Z3_ast, Z3_ast);
    BinaryZ3Function getBinaryZ3Function(kind_e kind) {
      static std::map<kind_e, BinaryZ3Function> function_map = {
        { BVADD_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_bvadd) },
        { BVAND_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_bvand) },
        { BVASHR_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_bvashr) },
        { BVLSHR_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_bvlshr) },
        { BVMUL_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_bvmul) },
        { BVNAND_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_bvnand) },
        { BVNOR_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_bvnor) },
        { BVOR_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_bvor) },
        { BVSDIV_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_bvsdiv) },
        { BVSGE_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_bvsge) },
        { BVSGT_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_bvsgt) },
        { BVSHL_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_bvshl) },
        { BVSLE_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_bvsle) },
        { BVSLT_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_bvslt) },
        { BVSMOD_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_bvsmod) },
        { BVSREM_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_bvsrem) },
        { BVSUB_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_bvsub) },
        { BVUDIV_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_bvudiv) },
        { BVUGE_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_bvuge) },
        { BVUGT_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_bvugt) },
        { BVULE_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_bvule) },
        { BVULT_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_bvult) },
        { BVUREM_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_bvurem) },
        { BVXNOR_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_bvxnor) },
        { BVXOR_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_bvxor) },
        { EQUAL_NODE, static_cast<BinaryZ3Function>(&log_Z3_mk_eq) } };
      const auto& iter = function_map.find(kind);
      if (iter != function_map.end()) {
        return iter->second;
      }
      return nullptr;
    }

    UnaryZ3Function getUnaryZ3Function(kind_e kind) {
      static std::map<kind_e, UnaryZ3Function> function_map = {
        { BVNEG_NODE, static_cast<UnaryZ3Function>(&log_Z3_mk_bvneg) },
        { BVNOT_NODE, static_cast<UnaryZ3Function>(&log_Z3_mk_bvnot) }};
      const auto& iter = function_map.find(kind);
      if (iter != function_map.end()) {
        return iter->second;
      }
      return nullptr;
    }

    void fillWorkStack(triton::ast::AbstractNode* node,
      std::vector<triton::ast::AbstractNode*>* result) {
      std::stack<std::pair<triton::ast::AbstractNode*, uint32_t>> workstack;
      printf("[D] Filling work stack.\n");
      workstack.push( {node, 0} );
      while (!workstack.empty()) {
        const auto& current_item = workstack.top();
        uint32_t child_index = current_item.second;
        triton::ast::AbstractNode* current_node = current_item.first;
        const auto& children = current_node->getChildren();
        if (child_index < children.size()) {
          workstack.pop();
          workstack.push( {current_node, child_index + 1} );
          workstack.push( {children[child_index], 0} );
        } else if ((current_node->getKind() == REFERENCE_NODE) && 
          child_index == 0) {
          workstack.pop();
          workstack.push( {current_node, child_index + 1} );
          workstack.push( {reinterpret_cast<triton::ast::ReferenceNode*>(
            current_node)->getSymbolicExpression().getAst(), 0 });
        } else {
          // All children have been processed, so put the current node into
          // the result vector.
          result->push_back(current_node);
          workstack.pop();
        }
      }
      printf("[D] result vector is %ld elements\n", result->size());
    }

    // Convert a Triton AST to a Z3 AST without recursing, by doing postorder
    // traversal. While the recursive solution is more elegant to read, it ends
    // up running out of stack space on very deep ASTs easily.
    //
    // The code is not pretty to read - as a refresher for how iterative post-
    // order traversal of trees using a stack works, please refer to
    // https://www.geeksforgeeks.org/iterative-postorder-traversal-using-stack/
    z3::expr TritonToZ3Ast::convert(triton::ast::AbstractNode* node) {
      std::stack<triton::ast::AbstractNode*> workStack;
      std::unordered_map<triton::ast::AbstractNode*, z3::expr> z3expressions;

      if (node == nullptr)
        throw triton::exceptions::AstTranslations("TritonToZ3Ast::convert_iterative(): node cannot be null.");

      std::vector<triton::ast::AbstractNode*> visitVector;

      // Calculate the order in which we wish to visit the nodes.
      fillWorkStack(node, &visitVector);

      // Setup code to keep track of the internal stack and make sure we traverse
      // nodes in post-order.

      for (triton::ast::AbstractNode* node : visitVector) {
        // Processes the current node.
        auto children = node->getChildren();
        // Get the function pointers (will be nullptrs potentially);
        auto z3FunctionBinary = getBinaryZ3Function(node->getKind());
        auto z3FunctionUnary = getUnaryZ3Function(node->getKind());

        switch (node->getKind()) {
          // The "standard" cases with 2 operands.
          case BVADD_NODE:
          case BVAND_NODE:
          case BVASHR_NODE:
          case BVLSHR_NODE:
          case BVMUL_NODE:
          case BVNAND_NODE:
          case BVNOR_NODE:
          case BVOR_NODE:
          case BVSDIV_NODE:
          case BVSGE_NODE:
          case BVSGT_NODE:
          case BVSHL_NODE:
          case BVSLE_NODE:
          case BVSLT_NODE:
          case BVSMOD_NODE:
          case BVSREM_NODE:
          case BVSUB_NODE:
          case BVUDIV_NODE:
          case BVUGE_NODE:
          case BVUGT_NODE:
          case BVULE_NODE:
          case BVULT_NODE:
          case BVUREM_NODE:
          case BVXNOR_NODE:
          case BVXOR_NODE:
          case EQUAL_NODE: {
            z3expressions.insert(std::make_pair(node,
              to_expr(this->context, z3FunctionBinary(this->context,
                z3expressions.at(children[0]), z3expressions.at(children[1])))));
            break;
          }
          // The "standard" cases with 1 operand.
          case BVNEG_NODE:
          case BVNOT_NODE: {
            z3expressions.insert(std::make_pair(node,
              to_expr(this->context, z3FunctionUnary(this->context,
                z3expressions.at(children[0])))));
            break;
          }
          // The nonstandard cases with individual handling.
          case BVROL_NODE: {
            triton::uint32 op1 = reinterpret_cast<triton::ast::DecimalNode*>(
              children[0])->getValue().convert_to<triton::uint32>();

            z3expressions.insert({node, to_expr(this->context, log_Z3_mk_rotate_left(
              this->context, op1, z3expressions.at(children[1])))});
            break;
          }
          case BVROR_NODE: {
            triton::uint32 op1 = reinterpret_cast<triton::ast::DecimalNode*>(
              children[0])->getValue().convert_to<triton::uint32>();

            z3expressions.insert(std::make_pair(node,
              to_expr(this->context, log_Z3_mk_rotate_right(
              this->context, op1, z3expressions.at(children[1])))));
            break;
          }
          case BV_NODE: {
            z3::expr value = z3expressions.at(children[0]);
            z3::expr size = z3expressions.at(children[1]);
            triton::uint32 bvsize = static_cast<triton::uint32>(this->getUintValue(size));
            z3expressions.insert({node,
              this->context.bv_val(this->getStringValue(value).c_str(), bvsize)});
            break;
          }
          case CONCAT_NODE: {
            z3::expr currentValue = z3expressions.at(children[0]);
            z3::expr nextValue(this->context);

            // Child[0] is the LSB
            for (triton::uint32 idx = 1; idx < children.size(); idx++) {
              nextValue = z3expressions.at(children[idx]);
              currentValue = to_expr(this->context, log_Z3_mk_concat(this->context, currentValue, nextValue));
            }
            z3expressions.insert({node, currentValue});
            break;
          }
          case DECIMAL_NODE: {
            std::string value(reinterpret_cast<triton::ast::DecimalNode*>(node)->getValue());
            z3expressions.insert({node, this->context.int_val(value.c_str())});
            break;
          }
          case DISTINCT_NODE: {
            z3::expr op1 = z3expressions.at(children[0]);
            z3::expr op2 = z3expressions.at(children[1]);
            Z3_ast ops[] = {op1, op2};

            z3expressions.insert({node, z3::to_expr(this->context, log_Z3_mk_distinct(this->context, 2, ops))});
            break;
          }
          case EXTRACT_NODE: {
            z3::expr high = z3expressions.at(children[0]);
            z3::expr low = z3expressions.at(children[1]);
            z3::expr value = z3expressions.at(children[2]);
            triton::uint32 hv = static_cast<triton::uint32>(this->getUintValue(high));
            triton::uint32 lv = static_cast<triton::uint32>(this->getUintValue(low));

            z3expressions.insert({node, to_expr(this->context, log_Z3_mk_extract(this->context, hv, lv, value))});

            break;
          }

          case ITE_NODE: {
            z3::expr op1 = z3expressions.at(children[0]);
            // condition
            z3::expr op2 = z3expressions.at(children[1]);
            // if true
            z3::expr op3 = z3expressions.at(children[2]);
            // if false

            z3expressions.insert({node, to_expr(this->context, log_Z3_mk_ite(this->context, op1, op2, op3))});
            break;
          }

          case LAND_NODE: {
            z3::expr currentValue = to_expr(this->context, z3expressions.at(children[0]));
            if (!currentValue.get_sort().is_bool()) {
              throw triton::exceptions::AstTranslations("TritonToZ3Ast::LandNode(): Land can be apply only on bool value.");
            }
            z3::expr nextValue(this->context);

            for (triton::uint32 idx = 1; idx < children.size(); idx++) {
              nextValue = z3expressions.at(children[idx]);
              if (!nextValue.get_sort().is_bool()) {
                throw triton::exceptions::AstTranslations("TritonToZ3Ast::LandNode(): Land can be apply only on bool value.");
              }
              Z3_ast ops[] = {currentValue, nextValue};
              currentValue = to_expr(this->context, log_Z3_mk_and(this->context, 2, ops));
            }
            z3expressions.insert({node, currentValue});
            break;
          }

          case LET_NODE: {
            std::string symbol    = reinterpret_cast<triton::ast::StringNode*>(children[0])->getValue();
            this->symbols[symbol] = children[1];
            z3expressions.insert({node, z3expressions.at(children[2])});
            break;
          }

          case LNOT_NODE: {
            z3::expr value = z3expressions.at(children[0]);
            if (!value.get_sort().is_bool()) {
              throw triton::exceptions::AstTranslations("TritonToZ3Ast::LnotNode(): Lnot can be apply only on bool value.");
            }
            z3expressions.insert({node,
              to_expr(this->context, log_Z3_mk_not(this->context, value))});
            break;
          }

          case LOR_NODE: {
            z3::expr currentValue = z3expressions.at(children[0]);
            if (!currentValue.get_sort().is_bool()) {
              throw triton::exceptions::AstTranslations("TritonToZ3Ast::LnotNode(): Lnot can be apply only on bool value.");
            }
            z3::expr nextValue(this->context);

            for (triton::uint32 idx = 1; idx < children.size(); idx++) {
              nextValue = z3expressions.at(children[idx]);
              if (!nextValue.get_sort().is_bool()) {
                throw triton::exceptions::AstTranslations("TritonToZ3Ast::LnotNode(): Lnot can be apply only on bool value.");
              }
              Z3_ast ops[] = {currentValue, nextValue};
              currentValue = to_expr(this->context, log_Z3_mk_or(this->context, 2, ops));
            }
            z3expressions.insert({node, currentValue});
            break;
          }

          case REFERENCE_NODE: {
            // Allow recursion for references. It breaks the intended goal of
            // this function (e.g. conversion of the AST without recursion),
            // but I see no clean way to avoid it right now.
            z3::expr referenced = z3expressions.at(reinterpret_cast<triton::ast::ReferenceNode*>(node)->getSymbolicExpression().getAst());
            z3expressions.insert({node, referenced});
            break;
          }

          case STRING_NODE: {
            std::string value = reinterpret_cast<triton::ast::StringNode*>(node)->getValue();

            if (this->symbols.find(value) == this->symbols.end())
              throw triton::exceptions::AstTranslations("TritonToZ3Ast::convert(): [STRING_NODE] Symbols not found.");

            z3expressions.insert({node, z3expressions.at(this->symbols[value])});
            break;
          }

          case SX_NODE: {
            z3::expr ext        = z3expressions.at(children[0]);
            z3::expr value      = z3expressions.at(children[1]);
            triton::uint32 extv = static_cast<triton::uint32>(this->getUintValue(ext));

            z3expressions.insert({node,  to_expr(this->context, log_Z3_mk_sign_ext(this->context, extv, value))});
            break;
          }

          case VARIABLE_NODE: {
            triton::usize varId = reinterpret_cast<triton::ast::VariableNode*>(node)->getVar().getId();
            triton::engines::symbolic::SymbolicVariable* symVar = this->symbolicEngine->getSymbolicVariableFromId(varId);

            if (symVar == nullptr)
              throw triton::exceptions::AstTranslations("TritonToZ3Ast::convert(): [VARIABLE_NODE] Can't get the symbolic variable (nullptr).");

            // If the conversion is used to evaluate a node, we concretize symbolic variables
            if (this->isEval) {
              triton::uint512 value = reinterpret_cast<triton::ast::VariableNode*>(node)->evaluate();
              std::string strValue(value);
              z3expressions.insert({node, this->context.bv_val(strValue.c_str(), symVar->getSize())});
            } else {
              // Otherwise, we keep the symbolic variables for a real conversion 
              z3expressions.insert({node, this->context.bv_const(symVar->getName().c_str(), symVar->getSize())});
            }
            break;
          }

          case ZX_NODE: {
            z3::expr ext        = z3expressions.at(children[0]);
            z3::expr value      = z3expressions.at(children[1]);
            triton::uint32 extv = static_cast<triton::uint32>(this->getUintValue(ext));

            z3expressions.insert({node, to_expr(this->context, log_Z3_mk_zero_ext(this->context, extv, value))});
            break;
          }

          default:
            throw triton::exceptions::AstTranslations("TritonToZ3Ast::convert(): Invalid kind of node.");
        } // End of switch.
        // TODO(thomasdullien): Check if the key/value for z3expressions for
        // the children of this node can be removed from the map now.
        // (They should, but the fact that we can visit the same nodes multiple
        // times due to references makes it seem like this is a bad idea?)
        {
          NodeLogger n(node);
        }
 
      } // End of iteration over nodes.
      return z3expressions.begin()->second;
    }
  }; /* ast namespace */
}; /* triton namespace */
