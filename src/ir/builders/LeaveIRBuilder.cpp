/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <LeaveIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


LeaveIRBuilder::LeaveIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


static SymbolicExpression *alignStack(Inst &inst, AnalysisProcessor &ap, uint32 memSize)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(ID_TMP_RSP, REG_SIZE);
  op2 = smt2lib::bv(memSize, memSize * REG_SIZE);

  expr = smt2lib::bvadd(op1, op2);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, ID_TMP_RSP, REG_SIZE, "Aligns stack");

  /* Apply the taint */
  se->isTainted = ap.isRegTainted(ID_TMP_RSP);

  return se;
}

void LeaveIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se1, *se2;
  smt2lib::smtAstAbstractNode *expr1, *expr2;
  auto mem = this->operands[0].getMem(); // The src memory read
  auto memSize = this->operands[0].getMem().getSize();

  // RSP = RBP; -----------------------------
  expr1 = ap.buildSymbolicRegOperand(ID_TMP_RBP, REG_SIZE);

  /* Create the symbolic expression */
  se1 = ap.createRegSE(inst, expr1, ID_TMP_RSP, REG_SIZE);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegReg(se1, ID_TMP_RSP, ID_TMP_RBP);
  // RSP = RBP; -----------------------------

  // RBP = Pop(); ---------------------------
  expr2 = ap.buildSymbolicMemOperand(mem, memSize);

  /* Create the symbolic expression */
  se2 = ap.createRegSE(inst, expr2, ID_TMP_RBP, REG_SIZE);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegMem(se2, ID_TMP_RBP, mem, memSize);
  // RBP = Pop(); ---------------------------

  /* Add the symbolic expression to the current inst */
  alignStack(inst, ap, memSize);
}


Inst *LeaveIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "LEAVE");
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

