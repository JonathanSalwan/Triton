/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <CpuSize.h>
#include <Z3ast.h>


Z3ast::Z3ast() {
}


Z3ast::~Z3ast() {
}


Z3Result& Z3ast::eval(smt2lib::smtAstAbstractNode& e) {
  e.accept(*this);
  return this->result;
}


void Z3ast::operator()(smt2lib::smtAstAbstractNode& e) {
  e.accept(*this);
}


void Z3ast::operator()(smt2lib::smtAstAssertNode& e) {
  throw std::runtime_error("smtAstAssertNode not implemented");
}


void Z3ast::operator()(smt2lib::smtAstBvaddNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvadd(this->result.getContext(), op1.getExpr(), op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvandNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvand(this->result.getContext(), op1.getExpr(), op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvashrNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvashr(this->result.getContext(), op1.getExpr(), op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvlshrNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvlshr(this->result.getContext(), op1.getExpr(), op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvmulNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvmul(this->result.getContext(), op1.getExpr(), op2.getExpr()));


  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvsmodNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvsmod(this->result.getContext(), op1.getExpr(), op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvnandNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvnand(this->result.getContext(), op1.getExpr(), op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvnegNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvneg(this->result.getContext(), op1.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvnorNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvnor(this->result.getContext(), op1.getExpr(), op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvnotNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvnot(this->result.getContext(), op1.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvorNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvor(this->result.getContext(), op1.getExpr(), op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvrolNode& e) {
  uint64   op1 = boost::numeric_cast<uint64>(reinterpret_cast<smt2lib::smtAstDecimalNode*>(e.getChilds()[0])->getValue());
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_rotate_left(this->result.getContext(), op1, op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvrorNode& e) {
  uint64  op1 = boost::numeric_cast<uint64>(reinterpret_cast<smt2lib::smtAstDecimalNode*>(e.getChilds()[0])->getValue());
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_rotate_right(this->result.getContext(), op1, op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvsdivNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvsdiv(this->result.getContext(), op1.getExpr(), op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvsgeNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvsge(this->result.getContext(), op1.getExpr(), op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvsgtNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvsgt(this->result.getContext(), op1.getExpr(), op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvshlNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvshl(this->result.getContext(), op1.getExpr(), op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvsleNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvsle(this->result.getContext(), op1.getExpr(), op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvsltNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvslt(this->result.getContext(), op1.getExpr(), op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvsremNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvsrem(this->result.getContext(), op1.getExpr(), op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvsubNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvsub(this->result.getContext(), op1.getExpr(), op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvudivNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvudiv(this->result.getContext(), op1.getExpr(), op2.getExpr()));


  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvugeNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvuge(this->result.getContext(), op1.getExpr(), op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvugtNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvugt(this->result.getContext(), op1.getExpr(), op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvuleNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvule(this->result.getContext(), op1.getExpr(), op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvultNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvult(this->result.getContext(), op1.getExpr(), op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvuremNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvurem(this->result.getContext(), op1.getExpr(), op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvxnorNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvxnor(this->result.getContext(), op1.getExpr(), op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvxorNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvxor(this->result.getContext(), op1.getExpr(), op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstBvNode& e) {
  Z3Result value = this->eval(*e.getChilds()[0]);
  Z3Result size = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = this->result.getContext().bv_val(value.getStringValue().c_str(), size.getUint64Value());

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstCompoundNode& e) {
  throw std::runtime_error("smtAstCompoundNode not implemented");
}


void Z3ast::operator()(smt2lib::smtAstConcatNode& e) {
  std::vector<smt2lib::smtAstAbstractNode*> childs = e.getChilds();

  uint64 idx;

  z3::expr nextValue(this->result.getContext());
  z3::expr currentValue = eval(*childs[0]).getExpr();

  //Child[0] is the LSB
  for (idx = 1; idx < childs.size(); idx++) {
      nextValue = eval(*childs[idx]).getExpr();
      currentValue = to_expr(this->result.getContext(), Z3_mk_concat(this->result.getContext(), currentValue, nextValue));
  }

  this->result.setExpr(currentValue);
}


void Z3ast::operator()(smt2lib::smtAstDecimalNode& e) {
  std::string value(e.getValue());
  z3::expr newexpr = this->result.getContext().int_val(value.c_str());
  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstDeclareNode& e) {
  throw std::runtime_error("smtAstDeclareNode not implemented");
}


void Z3ast::operator()(smt2lib::smtAstDistinctNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);

  Z3_ast ops[] = {op1.getExpr(), op2.getExpr()};
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_distinct(this->result.getContext(), 2, ops));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstEqualNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]);
  Z3Result op2 = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_eq(this->result.getContext(), op1.getExpr(), op2.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstExtractNode& e) {
  Z3Result high = this->eval(*e.getChilds()[0]);
  Z3Result low = this->eval(*e.getChilds()[1]);
  Z3Result value = this->eval(*e.getChilds()[2]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_extract(this->result.getContext(), high.getUint64Value(), low.getUint64Value(), value.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstIteNode& e) {
  Z3Result op1 = this->eval(*e.getChilds()[0]); //condition
  Z3Result op2 = this->eval(*e.getChilds()[1]); //if true
  Z3Result op3 = this->eval(*e.getChilds()[2]); //if false
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_ite(this->result.getContext(), op1.getExpr(), op2.getExpr(), op3.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstReferenceNode& e) {
  throw std::runtime_error("smtAstReferenceNode not implemented");
}


void Z3ast::operator()(smt2lib::smtAstStringNode& e) {
  throw std::runtime_error("smtAstStringNode not implemented");
}


void Z3ast::operator()(smt2lib::smtAstSxNode& e) {
  Z3Result i = this->eval(*e.getChilds()[0]);
  Z3Result value = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_sign_ext(this->result.getContext(), i.getUint64Value(), value.getExpr()));

  this->result.setExpr(newexpr);
}


void Z3ast::operator()(smt2lib::smtAstVariableNode& e) {
  std::string varName       = e.getValue();
  SymbolicVariable* symVar  = ap.getSymVar(varName);

  if (symVar == nullptr)
    throw std::runtime_error("smtAstVariableNode: can't get the symbolic variable (nullptr)");

  if (symVar->getSymVarSize() > QWORD_SIZE_BIT)
    throw std::runtime_error("smtAstVariableNode: size above 64 bits is not supported yet");

  if (symVar->getSymVarKind() == SymVar::kind::MEM) {
    uint64 memSize   = symVar->getSymVarSize();
    uint128 memValue = symVar->getConcreteValue();
    std::string memStrValue(memValue);
    z3::expr newexpr = this->result.getContext().bv_val(memStrValue.c_str(), memSize);
    this->result.setExpr(newexpr);
  }
  else if (symVar->getSymVarKind() == SymVar::kind::REG) {
    uint128 regValue = symVar->getConcreteValue();
    std::string regStrValue(regValue);
    z3::expr newexpr = this->result.getContext().bv_val(regStrValue.c_str(), symVar->getSymVarSize());
    this->result.setExpr(newexpr);
  }
  else {
    throw std::runtime_error("smtAstVariableNode: UNSET");
  }
}


void Z3ast::operator()(smt2lib::smtAstZxNode& e) {
  Z3Result i = this->eval(*e.getChilds()[0]);
  Z3Result value = this->eval(*e.getChilds()[1]);
  z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_zero_ext(this->result.getContext(), i.getUint64Value(), value.getExpr()));

  this->result.setExpr(newexpr);
}

#endif /* LIGHT_VERSION */

