/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

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


static SymbolicExpression *alignStack(Inst &inst, AnalysisProcessor &ap, uint32 memSize)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;

  /* Create the SMT semantic. */
  op1 = ap.buildSymbolicRegOperand(ID_TMP_RSP, REG_SIZE);
  op2 = smt2lib::bv(memSize, memSize * REG_SIZE);

  expr = smt2lib::bvadd(op1, op2);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, ID_TMP_RSP, REG_SIZE, "Aligns stack");

  /* Apply the taint */
  se->isTainted = ap.isRegTainted(ID_TMP_RSP);

  return se;
}


void PopIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1;
  auto reg = this->operands[0].getReg(); // Reg poped
  auto regSize = this->operands[0].getReg().getSize();  // Reg size poped
  auto mem = this->operands[1].getMem(); // The src memory read
  auto memSize = this->operands[1].getMem().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(mem, memSize);

  /* Finale expr */
  expr = op1;

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemReg(se, mem, reg, memSize);

  /* Create the SMT semantic side effect */
  alignStack(inst, ap, memSize);
}


void PopIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1;
  auto mem1 = this->operands[0].getMem(); // Mem poped
  auto memSize1 = this->operands[0].getMem().getSize();
  auto mem2 = this->operands[1].getMem(); // The dst memory read
  auto memSize2 = this->operands[1].getMem().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(mem2, memSize2);

  /* Finale expr */
  expr = op1;

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, mem1, memSize1);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemMem(se, mem1, mem2, memSize2);

  /* Create the SMT semantic side effect */
  alignStack(inst, ap, memSize1);
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

#endif /* LIGHT_VERSION */

