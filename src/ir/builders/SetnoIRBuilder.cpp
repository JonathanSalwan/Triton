/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <SetnoIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


SetnoIRBuilder::SetnoIRBuilder(__uint address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void SetnoIRBuilder::imm(Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


void SetnoIRBuilder::reg(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *of;
  auto reg = this->operands[0].getReg();
  auto regSize = this->operands[0].getReg().getSize();

  /* Create the SMT semantic */
  of = ap.buildSymbolicFlagOperand(ID_TMP_OF);

  /* Finale expr */
  expr = smt2lib::ite(
            smt2lib::equal(
              of,
              smt2lib::bvfalse()),
            smt2lib::bv(1, BYTE_SIZE_BIT),
            smt2lib::bv(0, BYTE_SIZE_BIT));

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint via the concretization */
  if (ap.getFlagValue(ID_TMP_OF) == 0)
    ap.assignmentSpreadTaintRegReg(se, reg, ID_TMP_OF);

}


void SetnoIRBuilder::mem(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *of;
  auto mem = this->operands[0].getMem();
  auto memSize = this->operands[0].getMem().getSize();

  /* Create the SMT semantic */
  of = ap.buildSymbolicFlagOperand(ID_TMP_OF);

  /* Finale expr */
  expr = smt2lib::ite(
            smt2lib::equal(
              of,
              smt2lib::bvfalse()),
            smt2lib::bv(1, BYTE_SIZE_BIT),
            smt2lib::bv(0, BYTE_SIZE_BIT));

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, mem, memSize);

  /* Apply the taint via the concretization */
  if (ap.getFlagValue(ID_TMP_OF) == 0)
    ap.assignmentSpreadTaintMemReg(se, mem, ID_TMP_OF, memSize);

}


void SetnoIRBuilder::none(Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


Inst *SetnoIRBuilder::process(void) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(*inst, this->operands, "SETNO");
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

