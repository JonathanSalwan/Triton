/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <algorithm>
#include <sstream>
#include <stdexcept>

#include <MovIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>



MovIRBuilder::MovIRBuilder(__uint address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void MovIRBuilder::regImm(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  auto reg = this->operands[0].getReg();
  auto regSize = this->operands[0].getReg().getSize();
  auto imm = this->operands[1].getImm().getValue();

  /* Create the SMT semantic */
  expr = smt2lib::bv(imm, regSize * BYTE_SIZE_BIT);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegImm(se, reg);
}


void MovIRBuilder::regReg(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  auto reg1 = this->operands[0].getReg();
  auto reg2 = this->operands[1].getReg();
  auto regSize1 = this->operands[0].getReg().getSize();
  auto regSize2 = this->operands[1].getReg().getSize();

  /* Create the SMT semantic */
  expr = ap.buildSymbolicRegOperand(reg2, regSize2);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg1, regSize1);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegReg(se, reg1, reg2);
}


void MovIRBuilder::regMem(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  auto mem = this->operands[1].getMem();
  auto memSize = this->operands[1].getMem().getSize();
  auto reg = this->operands[0].getReg();
  auto regSize = this->operands[0].getReg().getSize();

  /* Create the SMT semantic */
  expr = ap.buildSymbolicMemOperand(mem, memSize);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegMem(se, reg, mem, memSize);
}


void MovIRBuilder::memImm(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  auto memSize = this->operands[0].getMem().getSize();
  auto mem = this->operands[0].getMem();
  auto imm = this->operands[1].getImm().getValue();

  /* Create the SMT semantic */
  expr = smt2lib::bv(imm, memSize * BYTE_SIZE_BIT);

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, mem, memSize);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemImm(se, mem, memSize);
}


void MovIRBuilder::memReg(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  auto memSize = this->operands[0].getMem().getSize();
  auto mem = this->operands[0].getMem();
  auto reg = this->operands[1].getReg();
  auto regSize = this->operands[1].getReg().getSize();

  /* Create the SMT semantic */
  expr = ap.buildSymbolicRegOperand(reg, regSize);

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, mem, memSize);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemReg(se, mem, reg, memSize);
}


Inst *MovIRBuilder::process(void) const {
  checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(*inst, this->operands, "MOV");
    ControlFlow::rip(*inst, this->nextAddress);
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

#endif /* LIGHT_VERSION */

