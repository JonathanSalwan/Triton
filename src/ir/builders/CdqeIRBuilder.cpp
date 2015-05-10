#include <iostream>
#include <sstream>
#include <stdexcept>

#include "CdqeIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


CdqeIRBuilder::CdqeIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void CdqeIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1;
  uint64_t          symReg = ap.getRegSymbolicID(ID_RAX);

  /* Create the SMT semantic */
  /* OP_1 */
  if (symReg != UNSET)
    op1 << smt2lib::extract(31, 0, "#" + std::to_string(symReg));
  else
    op1 << smt2lib::bv(ap.getRegisterValue(ID_RAX), REG_SIZE_BIT);

  /* Finale expr */
  expr << smt2lib::sx(op1.str(), 32);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_RAX);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


Inst *CdqeIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "CDQE");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    inst->addElement(ControlFlow::rip(ap, this->nextAddress));
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

