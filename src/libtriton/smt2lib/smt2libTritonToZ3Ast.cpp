//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>
#include <api.hpp>
#include <cpuSize.hpp>
#include <smt2libTritonToZ3Ast.hpp>
#include <symbolicExpression.hpp>
#include <symbolicVariable.hpp>



namespace triton {
  namespace smt2lib {

    TritonToZ3Ast::TritonToZ3Ast(bool eval) {
      this->isEval = eval;
    }


    TritonToZ3Ast::~TritonToZ3Ast() {
    }


    Z3Result& TritonToZ3Ast::eval(smtAstAbstractNode& e) {
      e.accept(*this);
      return this->result;
    }


    void TritonToZ3Ast::operator()(smtAstAbstractNode& e) {
      e.accept(*this);
    }


    void TritonToZ3Ast::operator()(smtAstAssertNode& e) {
      throw std::runtime_error("smtAstAssertNode not implemented");
    }


    void TritonToZ3Ast::operator()(smtAstBvaddNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvadd(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvandNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvand(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvashrNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvashr(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvdeclNode& e) {
      throw std::runtime_error("smtAstBvdeclNode not implemented");
    }


    void TritonToZ3Ast::operator()(smtAstBvlshrNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvlshr(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvmulNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvmul(this->result.getContext(), op1.getExpr(), op2.getExpr()));


      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvsmodNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvsmod(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvnandNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvnand(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvnegNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvneg(this->result.getContext(), op1.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvnorNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvnor(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvnotNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvnot(this->result.getContext(), op1.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvorNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvor(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvrolNode& e) {
      triton::uint32  op1 = boost::numeric_cast<triton::uint32>(reinterpret_cast<smtAstDecimalNode*>(e.getChilds()[0])->getValue());
      Z3Result        op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_rotate_left(this->result.getContext(), op1, op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvrorNode& e) {
      triton::uint32  op1 = boost::numeric_cast<triton::uint32>(reinterpret_cast<smtAstDecimalNode*>(e.getChilds()[0])->getValue());
      Z3Result        op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_rotate_right(this->result.getContext(), op1, op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvsdivNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvsdiv(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvsgeNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvsge(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvsgtNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvsgt(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvshlNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvshl(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvsleNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvsle(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvsltNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvslt(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvsremNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvsrem(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvsubNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvsub(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvudivNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvudiv(this->result.getContext(), op1.getExpr(), op2.getExpr()));


      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvugeNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvuge(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvugtNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvugt(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvuleNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvule(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvultNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvult(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvuremNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvurem(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvxnorNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvxnor(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvxorNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvxor(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstBvNode& e) {
      Z3Result value = this->eval(*e.getChilds()[0]);
      Z3Result size = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = this->result.getContext().bv_val(value.getStringValue().c_str(), size.getUintValue());

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstCompoundNode& e) {
      throw std::runtime_error("smtAstCompoundNode not implemented");
    }


    void TritonToZ3Ast::operator()(smtAstConcatNode& e) {
      std::vector<smtAstAbstractNode*> childs = e.getChilds();

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


    void TritonToZ3Ast::operator()(smtAstDecimalNode& e) {
      std::string value(e.getValue());
      z3::expr newexpr = this->result.getContext().int_val(value.c_str());
      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstDeclareFunctionNode& e) {
      throw std::runtime_error("smtAstDeclareFunctionNode not implemented");
    }


    void TritonToZ3Ast::operator()(smtAstDistinctNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);

      Z3_ast ops[] = {op1.getExpr(), op2.getExpr()};
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_distinct(this->result.getContext(), 2, ops));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstEqualNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_eq(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstExtractNode& e) {
      Z3Result high = this->eval(*e.getChilds()[0]);
      Z3Result low = this->eval(*e.getChilds()[1]);
      Z3Result value = this->eval(*e.getChilds()[2]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_extract(this->result.getContext(), high.getUintValue(), low.getUintValue(), value.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstIteNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]); // condition
      Z3Result op2 = this->eval(*e.getChilds()[1]); // if true
      Z3Result op3 = this->eval(*e.getChilds()[2]); // if false
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_ite(this->result.getContext(), op1.getExpr(), op2.getExpr(), op3.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstLandNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);

      Z3_ast ops[] = {op1.getExpr(), op2.getExpr()};
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_and(this->result.getContext(), 2, ops));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstLetNode& e) {
      throw std::runtime_error("smtAstLetNode not implemented");
    }


    void TritonToZ3Ast::operator()(smtAstLnotNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_not(this->result.getContext(), op1.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstLorNode& e) {
      Z3Result op1 = this->eval(*e.getChilds()[0]);
      Z3Result op2 = this->eval(*e.getChilds()[1]);

      Z3_ast ops[] = {op1.getExpr(), op2.getExpr()};
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_or(this->result.getContext(), 2, ops));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstReferenceNode& e) {
      triton::engines::symbolic::SymbolicExpression* refNode = triton::api.getSymbolicExpressionFromId(e.getValue());
      if (refNode == nullptr)
        throw std::runtime_error("TritonToZ3Ast::operator() - Reference node not found");
      Z3Result op1 = this->eval(*(refNode->getAst()));

      this->result.setExpr(op1.getExpr());
    }


    void TritonToZ3Ast::operator()(smtAstStringNode& e) {
      throw std::runtime_error("smtAstStringNode not implemented");
    }


    void TritonToZ3Ast::operator()(smtAstSxNode& e) {
      Z3Result i       = this->eval(*e.getChilds()[0]);
      Z3Result value   = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_sign_ext(this->result.getContext(), i.getUintValue(), value.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(smtAstVariableNode& e) {
      std::string varName = e.getValue();
      triton::engines::symbolic::SymbolicVariable* symVar = triton::api.getSymbolicVariableFromName(varName);

      if (symVar == nullptr)
        throw std::runtime_error("smtAstVariableNode: can't get the symbolic variable (nullptr)");

      if (symVar->getSymVarSize() > QWORD_SIZE_BIT)
        throw std::runtime_error("smtAstVariableNode: size above 64 bits is not supported yet");

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
          throw std::runtime_error("smtAstVariableNode: UNSET");
      }
      /* Otherwise, we keep the symbolic variables for a real conversion */
      else {
        //z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_const(this->result.getContext(), Z3_mk_string_symbol(this->result.getContext(), symVar->getSymVarName().c_str()), Z3_mk_bv_sort(this->result.getContext(), symVar->getSymVarSize())));
        z3::expr newexpr = this->result.getContext().bv_const(symVar->getSymVarName().c_str(), symVar->getSymVarSize());
        this->result.setExpr(newexpr);
      }
    }


    void TritonToZ3Ast::operator()(smtAstZxNode& e) {
      Z3Result i       = this->eval(*e.getChilds()[0]);
      Z3Result value   = this->eval(*e.getChilds()[1]);
      z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_zero_ext(this->result.getContext(), i.getUintValue(), value.getExpr()));

      this->result.setExpr(newexpr);
    }

  }; /* smt2lib namespace */
}; /* triton namespace */
