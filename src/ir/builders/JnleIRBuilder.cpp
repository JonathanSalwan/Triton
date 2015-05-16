#include <iostream>
#include <sstream>
#include <stdexcept>

#include "JnleIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


JnleIRBuilder::JnleIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void JnleIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, sf, of, zf;
  uint64_t          imm   = std::get<1>(this->operands[0]);
  uint64_t          symOF = ap.getRegSymbolicID(ID_OF);
  uint64_t          symSF = ap.getRegSymbolicID(ID_SF);
  uint64_t          symZF = ap.getRegSymbolicID(ID_ZF);

  /* Create the SMT semantic */
  if (symSF != UNSET)
    sf << "#" << std::dec << symSF;
  else
    sf << smt2lib::bv(ap.getFlagValue(ID_SF), 1);

  if (symOF != UNSET)
    of << "#" << std::dec << symOF;
  else
    of << smt2lib::bv(ap.getFlagValue(ID_OF), 1);

  if (symZF != UNSET)
    zf << "#" << std::dec << symZF;
  else
    zf << smt2lib::bv(ap.getFlagValue(ID_ZF), 1);

  /* 
   * Finale expr
   * JNLE: Jump if not less or equal ((SF^OF | ZF) == 0).
   * SMT: (= (bvor (bvxor sf of) zf) FALSE)
   */
  expr << smt2lib::ite(
            smt2lib::equal(
                smt2lib::bvor(smt2lib::bvxor(sf.str(), of.str()), zf.str()),
                smt2lib::bvfalse()
            ),
            smt2lib::bv(imm, REG_SIZE_BIT),
            smt2lib::bv(this->nextAddress, REG_SIZE_BIT));

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_RIP, "RIP");

  /* Add the constraint in the PathConstraints list */
  ap.addPathConstraint(se->getID());

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void JnleIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


void JnleIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


void JnleIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


Inst *JnleIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "JNLE");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

