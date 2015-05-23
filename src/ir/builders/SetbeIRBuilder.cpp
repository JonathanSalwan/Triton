#include <iostream>
#include <sstream>
#include <stdexcept>

#include "SetbeIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


SetbeIRBuilder::SetbeIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void SetbeIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


void SetbeIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, reg1e, cf, zf;
  uint64_t          reg     = this->operands[0].getValue();
  uint64_t          regSize = this->operands[0].getSize();

  /* Create the SMT semantic */
  cf << ap.buildSymbolicFlagOperand(ID_CF);
  zf << ap.buildSymbolicFlagOperand(ID_ZF);
  reg1e << ap.buildSymbolicRegOperand(reg, regSize);

  /* Finale expr */
  expr << smt2lib::ite(
            smt2lib::equal(
              smt2lib::bvor(
                cf.str(),
                zf.str()
              ),
              smt2lib::bvtrue()),
            smt2lib::bv(1, 8),
            smt2lib::bv(0, 8));

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg, regSize);

  /* Apply the taint via the concretization */
  if (ap.getFlagValue(ID_CF) | ap.getFlagValue(ID_ZF)) {
    if (ap.isRegTainted(ID_CF) == TAINTED)
      ap.assignmentSpreadTaintRegReg(se, reg, ID_CF);
    else
      ap.assignmentSpreadTaintRegReg(se, reg, ID_ZF);
  }

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void SetbeIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, mem1e, cf, zf;
  uint64_t          mem     = this->operands[0].getValue();
  uint64_t          memSize = this->operands[0].getSize();

  /* Create the SMT semantic */
  cf << ap.buildSymbolicFlagOperand(ID_CF);
  zf << ap.buildSymbolicFlagOperand(ID_ZF);
  mem1e << ap.buildSymbolicRegOperand(mem, memSize);

  /* Finale expr */
  expr << smt2lib::ite(
            smt2lib::equal(
              smt2lib::bvor(
                cf.str(),
                zf.str()
              ),
              smt2lib::bvtrue()),
            smt2lib::bv(1, 8),
            smt2lib::bv(0, 8));

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem);

  /* Apply the taint via the concretization */
  if (ap.getFlagValue(ID_CF) | ap.getFlagValue(ID_ZF)) {
    if (ap.isRegTainted(ID_CF) == TAINTED)
      ap.assignmentSpreadTaintMemReg(se, mem, ID_CF, memSize);
    else
      ap.assignmentSpreadTaintMemReg(se, mem, ID_ZF, memSize);
  }

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void SetbeIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


Inst *SetbeIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "SETBE");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    inst->addElement(ControlFlow::rip(ap, this->nextAddress));
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

