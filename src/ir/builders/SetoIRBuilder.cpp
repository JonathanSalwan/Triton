#include <iostream>
#include <sstream>
#include <stdexcept>

#include "SetoIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


SetoIRBuilder::SetoIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void SetoIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


void SetoIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, reg1e, of;
  uint64_t          reg     = this->operands[0].getValue();
  uint64_t          regSize = this->operands[0].getSize();

  /* Create the SMT semantic */
  of << ap.buildSymbolicFlagOperand(ID_OF);
  reg1e << ap.buildSymbolicRegOperand(reg, regSize);

  /* Finale expr */
  expr << smt2lib::ite(
            smt2lib::equal(
              of.str(),
              smt2lib::bvtrue()),
            smt2lib::bv(1, 8),
            smt2lib::bv(0, 8));

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg, regSize);

  /* Apply the taint via the concretization */
  if (ap.getFlagValue(ID_OF) == 1)
    ap.assignmentSpreadTaintRegReg(se, reg, ID_OF);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void SetoIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, mem1e, of;
  uint64_t          mem     = this->operands[0].getValue();
  uint64_t          memSize = this->operands[0].getSize();

  /* Create the SMT semantic */
  of << ap.buildSymbolicFlagOperand(ID_OF);
  mem1e << ap.buildSymbolicRegOperand(mem, memSize);

  /* Finale expr */
  expr << smt2lib::ite(
            smt2lib::equal(
              of.str(),
              smt2lib::bvtrue()),
            smt2lib::bv(1, 8),
            smt2lib::bv(0, 8));

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem);

  /* Apply the taint via the concretization */
  if (ap.getFlagValue(ID_OF) == 1)
    ap.assignmentSpreadTaintMemReg(se, mem, ID_OF, memSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void SetoIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


Inst *SetoIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "SETO");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    inst->addElement(ControlFlow::rip(ap, this->nextAddress));
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

