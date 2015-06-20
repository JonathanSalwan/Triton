#include <iostream>
#include <sstream>
#include <stdexcept>

#include <CmcIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicElement.h>


CmcIRBuilder::CmcIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void CmcIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  std::stringstream   expr, op1;

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicFlagOperand(ID_CF);

  /* Finale expr */
  expr << smt2lib::bvnot(op1.str());

  /* Create the symbolic element */
  ap.createRegSE(inst, expr, ID_CF);
}


Inst *CmcIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "CMC");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

