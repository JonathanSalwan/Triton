/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <CallIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


CallIRBuilder::CallIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


static SymbolicExpression *alignStack(Inst &inst, AnalysisProcessor &ap, uint64 memSize)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(ID_TMP_RSP, memSize);
  op2 = smt2lib::bv(REG_SIZE, memSize * REG_SIZE);

  expr = smt2lib::bvsub(op1, op2);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, ID_TMP_RSP, REG_SIZE, "Aligns stack");

  /* Apply the taint */
  se->isTainted = ap.isRegTainted(ID_TMP_RSP);

  return se;
}


void CallIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr1, *expr2;
  auto reg = this->operands[0].getReg();
  auto regSize = this->operands[0].getReg().getSize();
  auto mem = this->operands[1].getMem(); // The dst memory write
  auto memSize = this->operands[1].getMem().getSize();

  /* Create the SMT semantic side effect */
  alignStack(inst, ap, memSize);

  /* Create the SMT semantic */
  /* *RSP =  Next_RIP */
  expr1 = smt2lib::bv(this->nextAddress, memSize * REG_SIZE);

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr1, mem, memSize, "Saved RIP");

  /* Apply the taint */
  ap.assignmentSpreadTaintMemImm(se, mem, memSize);

  /* Create the SMT semantic */
  /* RIP = reg */
  expr2 = ap.buildSymbolicRegOperand(reg, regSize);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr2, ID_TMP_RIP, REG_SIZE, "RIP");

  /* Apply the taint */
  ap.assignmentSpreadTaintRegImm(se, ID_TMP_RIP);
}


void CallIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr1, *expr2;
  auto imm = this->operands[0].getImm().getValue();
  auto mem = this->operands[1].getMem(); // The dst memory write
  auto memSize = this->operands[1].getMem().getSize();

  /* Create the SMT semantic side effect */
  alignStack(inst, ap, memSize);

  /* Create the SMT semantic */
  /* *RSP =  Next_RIP */
  expr1 = smt2lib::bv(this->nextAddress, memSize * REG_SIZE);

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr1, mem, memSize, "Saved RIP");

  /* Apply the taint */
  ap.assignmentSpreadTaintMemImm(se, mem, memSize);

  /* Create the SMT semantic */
  /* RIP = imm */
  expr2 = smt2lib::bv(imm, memSize * REG_SIZE);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr2, ID_TMP_RIP, REG_SIZE, "RIP");

  /* Apply the taint */
  ap.assignmentSpreadTaintRegImm(se, ID_TMP_RIP);
}


void CallIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr1, *expr2;
  auto mem1 = this->operands[0].getMem();
  auto memSize1 = this->operands[0].getMem().getSize();
  auto mem2 = this->operands[1].getMem(); // The dst memory write
  auto memSize2 = this->operands[1].getMem().getSize();

  /* Create the SMT semantic side effect */
  alignStack(inst, ap, memSize2);

  /* Create the SMT semantic */
  /* *RSP =  Next_RIP */
  expr1 = smt2lib::bv(this->nextAddress, memSize2 * REG_SIZE);

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr1, mem2, memSize2, "Saved RIP");

  /* Apply the taint */
  ap.assignmentSpreadTaintMemImm(se, mem2, memSize2);

  /* Create the SMT semantic */
  /* RIP = imm */
  expr2 = ap.buildSymbolicMemOperand(mem1, memSize1);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr2, ID_TMP_RIP, REG_SIZE, "RIP");

  /* Apply the taint */
  ap.assignmentSpreadTaintRegImm(se, ID_TMP_RIP);
}


void CallIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


Inst *CallIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "CALL");
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

#endif /* LIGHT_VERSION */

