/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <PushIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


PushIRBuilder::PushIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}



static SymbolicExpression *alignStack(Inst &inst, AnalysisProcessor &ap, uint32 writeSize)
{
  SymbolicExpression    *se;
  smt2lib::smtAstAbstractNode   *expr, *op1, *op2;

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(ID_RSP, writeSize);
  op2 = smt2lib::bv(writeSize, writeSize * REG_SIZE);

  expr = smt2lib::bvsub(op1, op2);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, ID_RSP, REG_SIZE, "Aligns stack");

  /* Apply the taint */
  se->isTainted = ap.isRegTainted(ID_RSP);

  return se;
}


void PushIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1;
  auto reg = this->operands[0].getReg().getTritonRegId(); // Reg pushed
  auto mem = this->operands[1].getMem().getAddress(); // The dst memory writing
  auto regSize = this->operands[0].getReg().getSize();
  auto memSize = this->operands[1].getMem().getSize();

  /* Create the SMT semantic side effect */
  alignStack(inst, ap, memSize);

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg, regSize);

  /* Finale expr */
  expr = op1;

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, mem, memSize);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemReg(se, mem, reg, memSize);

}


void PushIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1;
  auto imm = this->operands[0].getImm().getValue(); // Imm pushed
  auto mem = this->operands[1].getMem().getAddress(); // The dst memory writing
  auto memSize = this->operands[1].getMem().getSize();

  /* Create the SMT semantic side effect */
  alignStack(inst, ap, memSize);

  /* Create the SMT semantic */
  /* OP_1 */
  op1 = smt2lib::bv(imm, memSize * REG_SIZE);

  /* Finale expr */
  expr = op1;

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, mem, memSize);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemImm(se, mem, memSize);

}


void PushIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1;
  auto memOp = this->operands[0].getMem().getAddress(); // Mem pushed
  auto readSize = this->operands[0].getMem().getSize();
  auto memDst = this->operands[1].getMem().getAddress(); // The dst memory writing
  auto writeSize = this->operands[1].getMem().getSize();

  /* Create the SMT semantic side effect */
  alignStack(inst, ap, writeSize);

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(memOp, readSize);

  /* Finale expr */
  expr = op1;

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, memDst, writeSize);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemMem(se, memDst, memOp, readSize);

}


void PushIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  /* There is no <push none> available in x86 */
  OneOperandTemplate::stop(this->disas);
}


Inst *PushIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "PUSH");
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

