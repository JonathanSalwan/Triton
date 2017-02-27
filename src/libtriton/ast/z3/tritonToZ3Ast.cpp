//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/cpuSize.hpp>
#include <triton/exceptions.hpp>
#include <triton/tritonToZ3Ast.hpp>



namespace triton {
  namespace ast {

    TritonToZ3Ast::TritonToZ3Ast(triton::engines::symbolic::SymbolicEngine* symbolicEngine, bool eval) {
      if (symbolicEngine == nullptr)
        throw triton::exceptions::AstTranslations("TritonToZ3Ast::TritonToZ3Ast(): The symbolicEngine API cannot be null.");

      this->symbolicEngine = symbolicEngine;
      this->isEval = eval;
    }


    TritonToZ3Ast::~TritonToZ3Ast() {
    }


    Z3Result& TritonToZ3Ast::eval(triton::ast::AbstractNode& e) {
      e.accept(*this);
      return this->result;
    }


    void TritonToZ3Ast::operator()(triton::ast::AbstractNode& e) {
      e.accept(*this);
    }


    void TritonToZ3Ast::operator()(triton::ast::AssertNode& e) {
      throw triton::exceptions::AstTranslations("TritonToZ3Ast::AssertNode(): Not implemented.");
    }


    void TritonToZ3Ast::operator()(triton::ast::BvaddNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvadd(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvandNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvand(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvashrNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvashr(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvdeclNode& e) {
      throw triton::exceptions::AstTranslations("TritonToZ3Ast::BvdeclNode(): Not implemented.");
    }


    void TritonToZ3Ast::operator()(triton::ast::BvlshrNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvlshr(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvmulNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvmul(this->result.getContext(), op1.getExpr(), op2.getExpr()));


      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvsmodNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvsmod(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvnandNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvnand(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvnegNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvneg(this->result.getContext(), op1.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvnorNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvnor(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvnotNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvnot(this->result.getContext(), op1.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvorNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvor(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvrolNode& e) {
      triton::uint32 op1  = reinterpret_cast<triton::ast::DecimalNode*>(e.getChilds()[0])->getValue().convert_to<triton::uint32>();
      Z3Result op2        = this->eval(*e.getChilds()[1]);
      z3::expr newexpr    = to_expr(this->result.getContext(), Z3_mk_rotate_left(this->result.getContext(), op1, op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvrorNode& e) {
      triton::uint32 op1  = reinterpret_cast<triton::ast::DecimalNode*>(e.getChilds()[0])->getValue().convert_to<triton::uint32>();
      Z3Result op2        = this->eval(*e.getChilds()[1]);
      z3::expr newexpr    = to_expr(this->result.getContext(), Z3_mk_rotate_right(this->result.getContext(), op1, op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvsdivNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvsdiv(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvsgeNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvsge(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvsgtNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvsgt(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvshlNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvshl(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvsleNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvsle(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvsltNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvslt(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvsremNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvsrem(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvsubNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvsub(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvudivNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvudiv(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvugeNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvuge(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvugtNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvugt(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvuleNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvule(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvultNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvult(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvuremNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvurem(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvxnorNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvxnor(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvxorNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_bvxor(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::BvNode& e) {
      Z3Result value        = this->eval(*e.getChilds()[0]);
      Z3Result size         = this->eval(*e.getChilds()[1]);
      triton::uint32 bvsize = static_cast<triton::uint32>(size.getUintValue());

      z3::expr newexpr = this->result.getContext().bv_val(value.getStringValue().c_str(), bvsize);

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::CompoundNode& e) {
      throw triton::exceptions::AstTranslations("TritonToZ3Ast::CompoundNode(): Not implemented.");
    }


    void TritonToZ3Ast::operator()(triton::ast::ConcatNode& e) {
      std::vector<triton::ast::AbstractNode*> childs = e.getChilds();

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


    void TritonToZ3Ast::operator()(triton::ast::DecimalNode& e) {
      std::string value(e.getValue());
      z3::expr newexpr = this->result.getContext().int_val(value.c_str());
      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::DeclareFunctionNode& e) {
      throw triton::exceptions::AstTranslations("TritonToZ3Ast::DeclareFunctionNode(): Not implemented.");
    }


    void TritonToZ3Ast::operator()(triton::ast::DistinctNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      Z3_ast ops[]      = {op1.getExpr(), op2.getExpr()};
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_distinct(this->result.getContext(), 2, ops));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::EqualNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_eq(this->result.getContext(), op1.getExpr(), op2.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::ExtractNode& e) {
      Z3Result high     = this->eval(*e.getChilds()[0]);
      Z3Result low      = this->eval(*e.getChilds()[1]);
      Z3Result value    = this->eval(*e.getChilds()[2]);
      triton::uint32 hv = static_cast<triton::uint32>(high.getUintValue());
      triton::uint32 lv = static_cast<triton::uint32>(low.getUintValue());
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_extract(this->result.getContext(), hv, lv, value.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::IteNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]); // condition
      Z3Result op2      = this->eval(*e.getChilds()[1]); // if true
      Z3Result op3      = this->eval(*e.getChilds()[2]); // if false
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_ite(this->result.getContext(), op1.getExpr(), op2.getExpr(), op3.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::LandNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      Z3_ast ops[]      = {op1.getExpr(), op2.getExpr()};
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_and(this->result.getContext(), 2, ops));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::LetNode& e) {
      std::string symbol    = reinterpret_cast<triton::ast::StringNode*>(e.getChilds()[0])->getValue();
      this->symbols[symbol] = e.getChilds()[1];
      Z3Result op2          = this->eval(*e.getChilds()[2]);

      this->result.setExpr(op2.getExpr());
    }


    void TritonToZ3Ast::operator()(triton::ast::LnotNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_not(this->result.getContext(), op1.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::LorNode& e) {
      Z3Result op1      = this->eval(*e.getChilds()[0]);
      Z3Result op2      = this->eval(*e.getChilds()[1]);
      Z3_ast ops[]      = {op1.getExpr(), op2.getExpr()};
      z3::expr newexpr  = to_expr(this->result.getContext(), Z3_mk_or(this->result.getContext(), 2, ops));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::ReferenceNode& e) {
      triton::engines::symbolic::SymbolicExpression* refNode = this->symbolicEngine->getSymbolicExpressionFromId(e.getValue());
      if (refNode == nullptr)
        throw triton::exceptions::AstTranslations("TritonToZ3Ast::ReferenceNode(): Reference node not found.");
      Z3Result op1 = this->eval(*(refNode->getAst()));
      this->result.setExpr(op1.getExpr());
    }


    void TritonToZ3Ast::operator()(triton::ast::StringNode& e) {
      if (this->symbols.find(e.getValue()) == this->symbols.end())
        throw triton::exceptions::AstTranslations("TritonToZ3Ast::StringNode(): Symbols not found.");
      Z3Result op1 = this->eval(*(this->symbols[e.getValue()]));
      this->result.setExpr(op1.getExpr());
    }


    void TritonToZ3Ast::operator()(triton::ast::SxNode& e) {
      Z3Result ext        = this->eval(*e.getChilds()[0]);
      Z3Result value      = this->eval(*e.getChilds()[1]);
      triton::uint32 extv = static_cast<triton::uint32>(ext.getUintValue());
      z3::expr newexpr    = to_expr(this->result.getContext(), Z3_mk_sign_ext(this->result.getContext(), extv, value.getExpr()));

      this->result.setExpr(newexpr);
    }


    void TritonToZ3Ast::operator()(triton::ast::VariableNode& e) {
      std::string varName = e.getValue();
      triton::engines::symbolic::SymbolicVariable* symVar = this->symbolicEngine->getSymbolicVariableFromName(varName);

      if (symVar == nullptr)
        throw triton::exceptions::AstTranslations("TritonToZ3Ast::VariableNode(): Can't get the symbolic variable (nullptr).");

      if (symVar->getSize() > QWORD_SIZE_BIT)
        throw triton::exceptions::AstTranslations("TritonToZ3Ast::VariableNode(): Size above 64 bits is not supported yet.");

      /* If the conversion is used to evaluate a node, we concretize symbolic variables */
      if (this->isEval) {
        if (symVar->getKind() == triton::engines::symbolic::MEM) {
          triton::uint32 memSize   = symVar->getSize();
          triton::uint512 memValue = symVar->getConcreteValue();
          std::string memStrValue(memValue);
          z3::expr newexpr = this->result.getContext().bv_val(memStrValue.c_str(), memSize);
          this->result.setExpr(newexpr);
        }
        else if (symVar->getKind() == triton::engines::symbolic::REG) {
          triton::uint512 regValue = symVar->getConcreteValue();
          std::string regStrValue(regValue);
          z3::expr newexpr = this->result.getContext().bv_val(regStrValue.c_str(), symVar->getSize());
          this->result.setExpr(newexpr);
        }
        else
          throw triton::exceptions::AstTranslations("TritonToZ3Ast::VariableNode(): UNSET.");
      }
      /* Otherwise, we keep the symbolic variables for a real conversion */
      else {
        //z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_const(this->result.getContext(), Z3_mk_string_symbol(this->result.getContext(), symVar->getName().c_str()), Z3_mk_bv_sort(this->result.getContext(), symVar->getSize())));
        z3::expr newexpr = this->result.getContext().bv_const(symVar->getName().c_str(), symVar->getSize());
        this->result.setExpr(newexpr);
      }
    }


    void TritonToZ3Ast::operator()(triton::ast::ZxNode& e) {
      Z3Result ext        = this->eval(*e.getChilds()[0]);
      Z3Result value      = this->eval(*e.getChilds()[1]);
      triton::uint32 extv = static_cast<triton::uint32>(ext.getUintValue());
      z3::expr newexpr    = to_expr(this->result.getContext(), Z3_mk_zero_ext(this->result.getContext(), extv, value.getExpr()));

      this->result.setExpr(newexpr);
    }

  }; /* ast namespace */
}; /* triton namespace */
