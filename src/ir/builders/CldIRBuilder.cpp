#include <iostream>
#include <sstream>
#include <stdexcept>

#include "CldIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


CldIRBuilder::CldIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void CldIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  inst.addElement(EflagsBuilder::clearFlag(ap, ID_DF, "Clear direction flag"));
}


Inst *CldIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "CLD");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    inst->addElement(ControlFlow::rip(ap, this->nextAddress));
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

