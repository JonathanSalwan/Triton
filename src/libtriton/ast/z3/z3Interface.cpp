//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/exceptions.hpp>
#include <triton/tritonToZ3Ast.hpp>
#include <triton/z3Interface.hpp>
#include <triton/z3Result.hpp>
#include <triton/z3ToTritonAst.hpp>



namespace triton {
  namespace ast {

    Z3Interface::Z3Interface(triton::engines::symbolic::SymbolicEngine* symbolicEngine) {
      if (symbolicEngine == nullptr)
        throw triton::exceptions::AstTranslations("Z3Interface::Z3Interface(): The symbolicEngine API cannot be null.");
      this->symbolicEngine = symbolicEngine;
    }


    Z3Interface::~Z3Interface() {
    }


    triton::ast::AbstractNode* Z3Interface::simplify(triton::ast::AbstractNode* node) const {
      triton::ast::TritonToZ3Ast  z3Ast{this->symbolicEngine, false};
      triton::ast::Z3ToTritonAst  tritonAst{this->symbolicEngine};
      triton::ast::Z3Result       result = z3Ast.eval(*node);

      /* Simplify and convert back to Triton's AST */
      z3::expr expr = result.getExpr().simplify();
      tritonAst.setExpr(expr);
      node = tritonAst.convert();

      return node;
    }


    triton::uint512 Z3Interface::evaluate(triton::ast::AbstractNode* node) const {
      if (node == nullptr)
        throw triton::exceptions::AstTranslations("Z3Interface::evaluate(): node cannot be null.");

      triton::ast::TritonToZ3Ast z3ast{this->symbolicEngine};
      triton::ast::Z3Result result = z3ast.eval(*node);
      triton::uint512 nbResult{result.getStringValue()};

      return nbResult;
    }

  }; /* ast namespace */
}; /* triton namespace */
