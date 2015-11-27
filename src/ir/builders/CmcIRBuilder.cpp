/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <CmcIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


CmcIRBuilder::CmcIRBuilder(__uint address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void CmcIRBuilder::none(Inst &inst) const {
  smt2lib::smtAstAbstractNode *expr, *op1;

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicFlagOperand(ID_TMP_CF);

  /* Finale expr */
  expr = smt2lib::bvnot(op1);

  /* Create the symbolic expression */
  ap.createFlagSE(inst, expr, ID_TMP_CF);
}


Inst *CmcIRBuilder::process(void) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(*inst, this->operands, "CMC");
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

