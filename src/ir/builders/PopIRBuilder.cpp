/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <PopIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


PopIRBuilder::PopIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


static SymbolicExpression *alignStack(Inst &inst, AnalysisProcessor &ap, uint32 readSize)
{
  SymbolicExpression    *se;
  smt2lib::smtAstAbstractNode   *expr, *op1, *op2;

  /* Create the SMT semantic. */
  op1 = ap.buildSymbolicRegOperand(ID_RSP, REG_SIZE);
  op2 = smt2lib::bv(readSize, readSize * REG_SIZE);

  expr = smt2lib::bvadd(op1, op2);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, ID_RSP, REG_SIZE, "Aligns stack");

  /* Apply the taint */
  se->isTainted = ap.isRegTainted(ID_RSP);

  return se;
}


void PopIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1;
  uint64 reg       = this->operands[0].getValue(); // Reg poped
  uint64 regSize   = this->operands[0].getSize();  // Reg size poped
  uint64 mem       = this->operands[1].getValue(); // The src memory read
  uint32 readSize  = this->operands[1].getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(mem, readSize);

  /* Finale expr */
  expr = op1;

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemReg(se, mem, reg, readSize);

  /* Create the SMT semantic side effect */
  alignStack(inst, ap, readSize);
}


void PopIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1;
  uint64 memOp     = this->operands[0].getValue(); // Mem poped
  uint32 writeSize = this->operands[0].getSize();
  uint64 memSrc    = this->operands[1].getValue(); // The dst memory read
  uint32 readSize  = this->operands[1].getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(memSrc, readSize);

  /* Finale expr */
  expr = op1;

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, memOp, writeSize);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemMem(se, memOp, memSrc, readSize);

  /* Create the SMT semantic side effect */
  alignStack(inst, ap, writeSize);
}


void PopIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  /* There is no <pop imm> available in x86 */
  OneOperandTemplate::stop(this->disas);
}


void PopIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  /* There is no <pop none> available in x86 */
  OneOperandTemplate::stop(this->disas);
}


Inst *PopIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "POP");
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

