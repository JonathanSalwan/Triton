#include <iostream>
#include <sstream>
#include <stdexcept>

#include "CmcIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


CmcIRBuilder::CmcIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void CmcIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement     *se;
  std::stringstream   expr, op1;
  uint64_t            symCF = ap.getRegSymbolicID(ID_CF);

  if (symCF != UNSET)
    op1 << "#" + std::to_string(symCF);
  else
    op1 << smt2lib::bv(ap.getCFValue(), 1);

  /* Finale expr */
  expr << smt2lib::bvnot(op1.str());

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_CF);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


Inst *CmcIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "CMC");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

