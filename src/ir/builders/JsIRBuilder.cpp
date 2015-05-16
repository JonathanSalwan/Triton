#include <iostream>
#include <sstream>
#include <stdexcept>

#include "JsIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


JsIRBuilder::JsIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void JsIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, sf;
  uint64_t          imm   = std::get<1>(this->operands[0]);
  uint64_t          symSF = ap.getRegSymbolicID(ID_SF);

  /* Create the SMT semantic */
  if (symSF != UNSET)
    sf << "#" << std::dec << symSF;
  else
    sf << smt2lib::bv(ap.getFlagValue(ID_SF), 1);

  /* Finale expr */
  expr << smt2lib::ite(
            smt2lib::equal(
              sf.str(),
              smt2lib::bvtrue()),
            smt2lib::bv(imm, REG_SIZE_BIT),
            smt2lib::bv(this->nextAddress, REG_SIZE_BIT));

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_RIP, "RIP");

  /* Add the constraint in the PathConstraints list */
  ap.addPathConstraint(se->getID());

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void JsIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


void JsIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


void JsIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


Inst *JsIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "JS");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

