#include <iostream>
#include <sstream>
#include <stdexcept>

#include "SetleIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


SetleIRBuilder::SetleIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void SetleIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


void SetleIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, reg1e, sf, of, zf;
  uint64_t          reg     = this->operands[0].getValue();
  uint64_t          regSize = this->operands[0].getSize();

  /* Create the flag SMT semantic */
  sf << ap.buildSymbolicFlagOperand(ID_SF);
  of << ap.buildSymbolicFlagOperand(ID_OF);
  zf << ap.buildSymbolicFlagOperand(ID_ZF);
  reg1e << ap.buildSymbolicRegOperand(reg, regSize);

  /* Finale expr */
  expr << smt2lib::ite(
            smt2lib::equal(
              smt2lib::bvor(smt2lib::bvxor(sf.str(), of.str()), zf.str()),
              smt2lib::bvtrue()),
            smt2lib::bv(1, 8),
            smt2lib::bv(0, 8));

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg, regSize);

  /* Apply the taint via the concretization */
  if (((ap.getFlagValue(ID_SF) ^ ap.getFlagValue(ID_OF)) | ap.getFlagValue(ID_ZF)) == 1) {
    if (ap.isRegTainted(ID_SF) == TAINTED)
      ap.assignmentSpreadTaintRegReg(se, reg, ID_SF);
    else if (ap.isRegTainted(ID_OF) == TAINTED)
      ap.assignmentSpreadTaintRegReg(se, reg, ID_OF);
    else
      ap.assignmentSpreadTaintRegReg(se, reg, ID_ZF);
  }

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void SetleIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, mem1e, sf, of, zf;
  uint64_t          mem     = this->operands[0].getValue();
  uint64_t          memSize = this->operands[0].getSize();

  /* Create the flag SMT semantic */
  sf << ap.buildSymbolicFlagOperand(ID_SF);
  of << ap.buildSymbolicFlagOperand(ID_OF);
  zf << ap.buildSymbolicFlagOperand(ID_ZF);
  mem1e << ap.buildSymbolicMemOperand(mem, memSize);

  /* Finale expr */
  expr << smt2lib::ite(
            smt2lib::equal(
              smt2lib::bvor(smt2lib::bvxor(sf.str(), of.str()), zf.str()),
              smt2lib::bvtrue()),
            smt2lib::bv(1, 8),
            smt2lib::bv(0, 8));

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem, memSize);

  /* Apply the taint via the concretization */
  if (((ap.getFlagValue(ID_SF) ^ ap.getFlagValue(ID_OF)) | ap.getFlagValue(ID_ZF)) == 1) {
    if (ap.isRegTainted(ID_SF) == TAINTED)
      ap.assignmentSpreadTaintMemReg(se, mem, ID_SF, memSize);
    else if (ap.isRegTainted(ID_OF) == TAINTED)
      ap.assignmentSpreadTaintMemReg(se, mem, ID_OF, memSize);
    else
      ap.assignmentSpreadTaintMemReg(se, mem, ID_ZF, memSize);
  }

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void SetleIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


Inst *SetleIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "SETLE");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    inst->addElement(ControlFlow::rip(ap, this->nextAddress));
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

