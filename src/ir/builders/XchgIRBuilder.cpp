/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <XchgIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


XchgIRBuilder::XchgIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void XchgIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void XchgIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se1, *se2;
  smt2lib::smtAstAbstractNode *expr1, *expr2, *op1, *op2;
  uint64 reg1          = this->operands[0].getValue();
  uint64 reg2          = this->operands[1].getValue();
  uint32 regSize1      = this->operands[0].getSize();
  uint32 regSize2      = this->operands[1].getSize();
  uint64 tmpReg1Taint  = ap.isRegTainted(reg1);
  uint64 tmpReg2Taint  = ap.isRegTainted(reg2);

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg1, regSize1);
  op2 = ap.buildSymbolicRegOperand(reg2, regSize2);

  // Final expr
  expr1 = op2;
  expr2 = op1;

  /* Create the symbolic expression */
  se1 = ap.createRegSE(inst, expr1, reg1, regSize1);
  se2 = ap.createRegSE(inst, expr2, reg2, regSize2);

  /* Apply the taint */
  ap.setTaintReg(se1, reg1, tmpReg2Taint);
  ap.setTaintReg(se2, reg2, tmpReg1Taint);
}


void XchgIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se1, *se2;
  smt2lib::smtAstAbstractNode *expr1, *expr2, *op1, *op2;
  uint64 reg1          = this->operands[0].getValue();
  uint64 mem2          = this->operands[1].getValue();
  uint32 regSize1      = this->operands[0].getSize();
  uint32 memSize2      = this->operands[1].getSize();
  uint64 tmpReg1Taint  = ap.isRegTainted(reg1);
  uint64 tmpMem2Taint  = ap.isMemTainted(mem2);

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg1, regSize1);
  op2 = ap.buildSymbolicMemOperand(mem2, memSize2);

  // Final expr
  expr1 = op2;
  expr2 = op1;

  /* Create the symbolic expression */
  se1 = ap.createRegSE(inst, expr1, reg1, regSize1);
  se2 = ap.createMemSE(inst, expr2, mem2, memSize2);

  /* Apply the taint */
  ap.setTaintReg(se1, reg1, tmpMem2Taint);
  ap.setTaintMem(se2, mem2, tmpReg1Taint);
}


void XchgIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void XchgIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se1, *se2;
  smt2lib::smtAstAbstractNode *expr1, *expr2, *op1, *op2;
  uint64 mem1          = this->operands[0].getValue();
  uint64 reg2          = this->operands[1].getValue();
  uint32 memSize1      = this->operands[0].getSize();
  uint32 regSize2      = this->operands[1].getSize();
  uint64 tmpMem1Taint  = ap.isMemTainted(mem1);
  uint64 tmpReg2Taint  = ap.isRegTainted(reg2);

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(mem1, memSize1);
  op2 = ap.buildSymbolicRegOperand(reg2, regSize2);

  // Final expr
  expr1 = op2;
  expr2 = op1;

  /* Create the symbolic expression */
  se1 = ap.createMemSE(inst, expr1, mem1, memSize1);
  se2 = ap.createRegSE(inst, expr2, reg2, regSize2);

  /* Apply the taint */
  ap.setTaintMem(se1, mem1, tmpReg2Taint);
  ap.setTaintReg(se2, reg2, tmpMem1Taint);
}


Inst *XchgIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "XCHG");
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

