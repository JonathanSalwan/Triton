/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <RolIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


RolIRBuilder::RolIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void RolIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  uint64 reg     = this->operands[0].getValue();
  uint64 imm     = this->operands[1].getValue();
  uint32 regSize = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg, regSize);
  /*
   * Note that SMT2-LIB doesn't support expression as rotate's value.
   * The op2 must be the concretization's value.
   */
  op2 = smt2lib::decimal(imm);

  /* Finale expr */
  expr = smt2lib::bvrol(op2, op1);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, reg, reg);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::cfRol(inst, se, ap, op2);
  EflagsBuilder::ofRol(inst, se, ap, regSize, op2);
}


void RolIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  uint64 reg1     = this->operands[0].getValue();
  uint32 regSize1 = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg1, regSize1);
  /*
   * Note that SMT2-LIB doesn't support expression as rotate's value.
   * The op2 must be the concretization's value.
   */
  op2 = smt2lib::decimal(ap.getRegisterValue(ID_RCX) & 0xff); /* 0xff -> There is only CL available */

  // Final expr
  expr = smt2lib::bvrol(op2, op1);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg1, regSize1);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, reg1, reg1);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::cfRol(inst, se, ap, op2);
  EflagsBuilder::ofRol(inst, se, ap, regSize1, op2);
}


void RolIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void RolIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  uint32 writeSize = this->operands[0].getSize();
  uint64 mem       = this->operands[0].getValue();
  uint64 imm       = this->operands[1].getValue();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(mem, writeSize);
  /*
   * Note that SMT2-LIB doesn't support expression as rotate's value.
   * The op2 must be the concretization's value.
   */
  op2 = smt2lib::decimal(imm);

  /* Final expr */
  expr = smt2lib::bvrol(op2, op1);

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, mem, writeSize);

  /* Apply the taint */
  ap.aluSpreadTaintMemMem(se, mem, mem, writeSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::cfRol(inst, se, ap, op2);
  EflagsBuilder::ofRol(inst, se, ap, writeSize, op2);
}


void RolIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  uint32 writeSize = this->operands[0].getSize();
  uint64 mem       = this->operands[0].getValue();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(mem, writeSize);
  /*
   * Note that SMT2-LIB doesn't support expression as rotate's value.
   * The op2 must be the concretization's value.
   */
  op2 = smt2lib::decimal(ap.getRegisterValue(ID_RCX) & 0xff); /* 0xff -> There is only CL available */

  // Final expr
  expr = smt2lib::bvrol(op2, op1);

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, mem, writeSize);

  /* Apply the taint */
  ap.aluSpreadTaintMemMem(se, mem, mem, writeSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::cfRol(inst, se, ap, op2);
  EflagsBuilder::ofRol(inst, se, ap, writeSize, op2);
}


Inst *RolIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "ROL");
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

