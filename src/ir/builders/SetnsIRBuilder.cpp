#include <iostream>
#include <sstream>
#include <stdexcept>

#include "SetnsIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


SetnsIRBuilder::SetnsIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void SetnsIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


void SetnsIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, reg1e, sf;
  uint64_t          reg     = this->operands[0].getValue();
  uint64_t          regSize = this->operands[0].getSize();

  /* Create the SMT semantic */
  sf << ap.buildSymbolicFlagOperand(ID_SF);
  reg1e << ap.buildSymbolicRegOperand(reg, regSize);

  /* Finale expr */
  expr << smt2lib::ite(
            smt2lib::equal(
              sf.str(),
              smt2lib::bvfalse()),
            smt2lib::bv(1, 8),
            smt2lib::bv(0, 8));

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg, regSize);

  /* Apply the taint via the concretization */
  if (ap.getFlagValue(ID_SF) == 0)
    ap.assignmentSpreadTaintRegReg(se, reg, ID_SF);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void SetnsIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, mem1e, sf;
  uint64_t          mem     = this->operands[0].getValue();
  uint64_t          memSize = this->operands[0].getSize();

  /* Create the SMT semantic */
  sf << ap.buildSymbolicFlagOperand(ID_SF);
  mem1e << ap.buildSymbolicRegOperand(mem, memSize);

  /* Finale expr */
  expr << smt2lib::ite(
            smt2lib::equal(
              sf.str(),
              smt2lib::bvfalse()),
            smt2lib::bv(1, 8),
            smt2lib::bv(0, 8));

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem);

  /* Apply the taint via the concretization */
  if (ap.getFlagValue(ID_SF) == 0)
    ap.assignmentSpreadTaintMemReg(se, mem, ID_SF, memSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void SetnsIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


Inst *SetnsIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "SETNS");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    inst->addElement(ControlFlow::rip(ap, this->nextAddress));
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

