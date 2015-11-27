/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <SetnpIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


SetnpIRBuilder::SetnpIRBuilder(__uint address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void SetnpIRBuilder::imm(Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


void SetnpIRBuilder::reg(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *pf;
  auto reg = this->operands[0].getReg();
  auto regSize = this->operands[0].getReg().getSize();

  /* Create the SMT semantic */
  pf = ap.buildSymbolicFlagOperand(ID_TMP_PF);

  /* Finale expr */
  expr = smt2lib::ite(
            smt2lib::equal(
              pf,
              smt2lib::bvfalse()),
            smt2lib::bv(1, BYTE_SIZE_BIT),
            smt2lib::bv(0, BYTE_SIZE_BIT));

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint via the concretization */
  if (ap.getFlagValue(ID_TMP_PF) == 0)
    ap.assignmentSpreadTaintRegReg(se, reg, ID_TMP_PF);

}


void SetnpIRBuilder::mem(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *pf;
  auto mem = this->operands[0].getMem();
  auto memSize = this->operands[0].getMem().getSize();

  /* Create the SMT semantic */
  pf = ap.buildSymbolicFlagOperand(ID_TMP_PF);

  /* Finale expr */
  expr = smt2lib::ite(
            smt2lib::equal(
              pf,
              smt2lib::bvfalse()),
            smt2lib::bv(1, BYTE_SIZE_BIT),
            smt2lib::bv(0, BYTE_SIZE_BIT));

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, mem, memSize);

  /* Apply the taint via the concretization */
  if (ap.getFlagValue(ID_TMP_PF) == 0)
    ap.assignmentSpreadTaintMemReg(se, mem, ID_TMP_PF, memSize);

}


void SetnpIRBuilder::none(Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


Inst *SetnpIRBuilder::process(void) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(*inst, this->operands, "SETNP");
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

