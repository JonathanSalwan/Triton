/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <CwdeIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


CwdeIRBuilder::CwdeIRBuilder(__uint address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void CwdeIRBuilder::none(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1;

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(ID_TMP_RAX, (WORD_SIZE_BIT - 1), 0);

  /* Finale expr */
  expr = smt2lib::sx(WORD_SIZE_BIT, op1);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, ID_TMP_RAX, DWORD_SIZE);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, ID_TMP_RAX, ID_TMP_RAX);
}


Inst *CwdeIRBuilder::process(void) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(*inst, this->operands, "CWDE");
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

