#include <iostream>
#include <sstream>
#include <stdexcept>

#include <ClcIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicElement.h>


ClcIRBuilder::ClcIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void ClcIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  EflagsBuilder::clearFlag(inst, ap, ID_CF, "Clears carry flag");
}


Inst *ClcIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "CLC");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

