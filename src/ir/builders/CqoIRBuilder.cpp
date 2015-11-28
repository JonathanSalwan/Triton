/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <CqoIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


CqoIRBuilder::CqoIRBuilder(__uint address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void CqoIRBuilder::none(Inst &inst) const {
  SymbolicExpression *se1, *se3;
  smt2lib::smtAstAbstractNode *expr1, *expr2, *expr3, *op1;

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(ID_TMP_RAX, (QWORD_SIZE_BIT - 1), 0);

  /* Expression 1: TMP = 128 bitvec (RDX:RAX) */
  expr1 = smt2lib::sx(QWORD_SIZE_BIT, op1);
  se1 = ap.createSE(inst, expr1, "Temporary variable");

  /* Expression 2: RAX = TMP[63...0] */
  expr2 = smt2lib::extract((QWORD_SIZE_BIT - 1), 0, smt2lib::reference(se1->getID()));
  ap.createRegSE(inst, expr2, ID_TMP_RAX, REG_SIZE, "RAX");

  /* Expression 3: RDX = TMP[127...64] */
  expr3 = smt2lib::extract((DQWORD_SIZE_BIT - 1), QWORD_SIZE_BIT, smt2lib::reference(se1->getID()));
  se3 = ap.createRegSE(inst, expr3, ID_TMP_RDX, REG_SIZE, "RDX");

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se3, ID_TMP_RDX, ID_TMP_RAX);
}


Inst *CqoIRBuilder::process(void) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(*inst, this->operands, "CQO");
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

