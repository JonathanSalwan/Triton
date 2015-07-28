/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <algorithm>
#include <sstream>
#include <stdexcept>

#include <MovapsIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


MovapsIRBuilder::MovapsIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void MovapsIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void MovapsIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint64 reg1      = this->operands[0].getValue();
  uint64 reg1Size  = this->operands[0].getSize();
  uint64 reg2      = this->operands[1].getValue();
  uint64 reg2Size  = this->operands[1].getSize();

  /* Create the SMT semantic */
  expr = ap.buildSymbolicRegOperand(reg2, reg2Size);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg1, reg1Size);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegReg(se, reg1, reg2);

}


void MovapsIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 readSize = this->operands[1].getSize();
  uint64 mem      = this->operands[1].getValue();
  uint64 reg      = this->operands[0].getValue();
  uint64 regSize  = this->operands[0].getSize();

  /* Create the SMT semantic */
  expr = ap.buildSymbolicMemOperand(mem, readSize);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegMem(se, reg, mem, readSize);

}


void MovapsIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void MovapsIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 writeSize = this->operands[0].getSize();
  uint64 mem       = this->operands[0].getValue();
  uint64 reg       = this->operands[1].getValue();
  uint64 regSize   = this->operands[1].getSize();

  /* Create the SMT semantic */
  expr = ap.buildSymbolicRegOperand(reg, regSize);

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, mem, writeSize);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemReg(se, mem, reg, writeSize);

}


Inst *MovapsIRBuilder::process(AnalysisProcessor &ap) const {
  checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "MOVAPS");
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

