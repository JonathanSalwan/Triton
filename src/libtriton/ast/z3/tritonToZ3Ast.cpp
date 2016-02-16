//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>
#include <api.hpp>
#include <cpuSize.hpp>
#include <tritonToZ3Ast.hpp>
#include <symbolicExpression.hpp>
#include <symbolicVariable.hpp>



namespace triton {
  namespace ast {

    TritonToZ3Ast::TritonToZ3Ast(bool eval) {
      this->isEval = eval;
    }


    TritonToZ3Ast::~TritonToZ3Ast() {
    }


    Z3Result& TritonToZ3Ast::eval(triton::ast::smtAstAbstractNode& e) {
      e.accept(*this);
      return this->result;
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstAbstractNode& e) {
      e.accept(*this);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstAssertNode& e) {
      throw std::runtime_error("TritonToZ3Ast::smtAstAssertNode(): Not implemented.");
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvaddNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvadd(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvandNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvand(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvashrNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvashr(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvdeclNode& e) {
      throw std::runtime_error("TritonToZ3Ast::smtAstBvdeclNode(): Not implemented.");
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvlshrNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvlshr(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvmulNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvmul(this->result.getContext(), op1.getExpr(), op2.getExpr()));


      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvsmodNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvsmod(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvnandNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvnand(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvnegNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvneg(this->result.getContext(), op1.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvnorNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvnor(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvnotNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvnot(this->result.getContext(), op1.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvorNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvor(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvrolNode& e) {
      triton::uint32  op1 = boost::numeric_cast<triton::uint32>(reinterpret_cast<triton::ast::smtAstDecimalNode*>(e.getChilds()[0])->getValue());
      Z3Result        op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_rotate_left(this->result.getContext(), op1, op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvrorNode& e) {
      triton::uint32  op1 = boost::numeric_cast<triton::uint32>(reinterpret_cast<triton::ast::smtAstDecimalNode*>(e.getChilds()[0])->getValue());
      Z3Result        op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_rotate_right(this->result.getContext(), op1, op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvsdivNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvsdiv(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvsgeNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvsge(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvsgtNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvsgt(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvshlNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvshl(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvsleNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvsle(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvsltNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvslt(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvsremNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvsrem(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvsubNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvsub(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvudivNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvudiv(this->result.getContext(), op1.getExpr(), op2.getExpr()));


      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvugeNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvuge(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvugtNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvugt(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvuleNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvule(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvultNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvult(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvuremNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvurem(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvxnorNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvxnor(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvxorNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvxor(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstBvNode& e) {
      Z3Result value = this->eval(*e.getChilds()[0]);
      Z3Result size = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = this->result.getContext().bv_val(value.getStringValue().c_str(), size.getUintValue());

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstCompoundNode& e) {
      throw std::runtime_error("TritonToZ3Ast::smtAstCompoundNode(): Not implemented.");
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstConcatNode& e) {
      std::vector<triton::ast::smtAstAbstractNode*> childs = e.getChilds();

      triton::uint32 idx;

      z3::expr nextValue(this->result.getContext());
      z3::expr currentValue = eval(*childs[0]).getExpr();

      //Child[0] is the LSB
      for (idx = 1; idx < childs.size(); idx++) {
          nextValue = eval(*childs[idx]).getExpr();
          currentValue = to_expr(this->result.getContext(), Z3_mk_concat(this->result.getContext(), currentValue, nextValue));
      }

      this->result.setExpr(currentValue);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstDecimalNode& e) {
      std::string value(e.getValue());
      z3::expr newexpr = this->result.getContext().int_val(value.c_str());
      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstDeclareFunctionNode& e) {
      throw std::runtime_error("TritonToZ3Ast::smtAstDeclareFunctionNode(): Not implemented.");
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstDistinctNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);

      Z3_ast ops[] = {op1.getExpr(), op2.getExpr()};
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_distinct(this->result.getContext(), 2, ops));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstEqualNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_eq(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstExtractNode& e) {
      Z3Result high = this->eval(*e.getChilds()[0]);
      Z3Result low = this->eval(*e.getChilds()[1]);
      Z3Result value = this->eval(*e.getChilds()[2]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_extract(this->result.getContext(), high.getUintValue(), low.getUintValue(), value.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstIteNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]); // condition
      Z3Result op2 = this->eval(*e.getChilds()[1]); // if true
      Z3Result op3 = this->eval(*e.getChilds()[2]); // if false
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_ite(this->result.getContext(), op1.getExpr(), op2.getExpr(), op3.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstLandNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);

      Z3_ast ops[] = {op1.getExpr(), op2.getExpr()};
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_and(this->result.getContext(), 2, ops));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstLetNode& e) {
      std::string symbol    = reinterpret_cast<triton::ast::smtAstStringNode*>(e.getChilds()[0])->getValue();
      this->symbols[symbol] = e.getChilds()[1];
      Z3Result op2          = this->eval(*e.getChilds()[2]);
      this->result.setExpr(op2.getExpr());
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstLnotNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_not(this->result.getContext(), op1.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstLorNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);

      Z3_ast ops[] = {op1.getExpr(), op2.getExpr()};
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_or(this->result.getContext(), 2, ops));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstReferenceNode& e) {
      triton::engines::symbolic::SymbolicExpression* refNode = triton::api.getSymbolicExpressionFromId(e.getValue());
      if (refNode == nullptr)
        throw std::runtime_error("TritonToZ3Ast::smtAstReferenceNode(): Reference node not found.");
      Z3Result op1 = this->eval(*(refNode->getAst()));
      this->result.setExpr(op1.getExpr());
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstStringNode& e) {
      if (this->symbols.find(e.getValue()) == this->symbols.end())
        throw std::runtime_error("TritonToZ3Ast::smtAstStringNode(): Symbols not found.");
      Z3Result op1 = this->eval(*(this->symbols[e.getValue()]));
      this->result.setExpr(op1.getExpr());
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstSxNode& e) {
      Z3Result i       = this->eval(*e.getChilds()[0]);
      Z3Result value   = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_sign_ext(this->result.getContext(), i.getUintValue(), value.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstVariableNode& e) {
      std::string varName = e.getValue();
      triton::engines::symbolic::SymbolicVariable* symVar = triton::api.getSymbolicVariableFromName(varName);

      if (symVar == nullptr)
        throw std::runtime_error("TritonToZ3Ast::smtAstVariableNode(): Can't get the symbolic variable (nullptr).");

      if (symVar->getSymVarSize() > QWORD_SIZE_BIT)
        throw std::runtime_error("TritonToZ3Ast::smtAstVariableNode(): Size above 64 bits is not supported yet.");

      /* If the conversion is used to evaluate a node, we concretize symbolic variables */
      if (this->isEval) {
        if (symVar->getSymVarKind() == triton::engines::symbolic::MEM) {
          triton::uint32 memSize   = symVar->getSymVarSize();
          triton::uint128 memValue = symVar->getConcreteValue();
          std::string memStrValue(memValue);
          z3::expr newexpr = this->result.getContext().bv_val(memStrValue.c_str(), memSize);
          this->result.setExpr(newexpr);
        }
        else if (symVar->getSymVarKind() == triton::engines::symbolic::REG) {
          triton::uint128 regValue = symVar->getConcreteValue();
          std::string regStrValue(regValue);
          z3::expr newexpr = this->result.getContext().bv_val(regStrValue.c_str(), symVar->getSymVarSize());
          this->result.setExpr(newexpr);
        }
        else
          throw std::runtime_error("TritonToZ3Ast::smtAstVariableNode(): UNSET.");
      }
      /* Otherwise, we keep the symbolic variables for a real conversion */
      else {
        //z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_const(this->result.getContext(), Z3_mk_string_symbol(this->result.getContext(), symVar->getSymVarName().c_str()), Z3_mk_bv_sort(this->result.getContext(), symVar->getSymVarSize())));
        z3::expr newexpr = this->result.getContext().bv_const(symVar->getSymVarName().c_str(), symVar->getSymVarSize());
        this->result.setExpr(newexpr);
      }
    }


    void TritonToZ3Ast::operator()(triton::ast::smtAstZxNode& e) {
      Z3Result i       = this->eval(*e.getChilds()[0]);
      Z3Result value   = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_zero_ext(this->result.getContext(), i.getUintValue(), value.getExpr()));

      this->result.setExpr(newexpr);
    }

  }; /* ast namespace */
}; /* triton namespace */
