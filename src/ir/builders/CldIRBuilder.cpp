/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <CldIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


CldIRBuilder::CldIRBuilder(__uint address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void CldIRBuilder::none(Inst &inst) const {
  EflagsBuilder::clearFlag(inst, ID_TMP_DF, "Clears direction flag");
}


Inst *CldIRBuilder::process(void) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(*inst, this->operands, "CLD");
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

