#include <iostream>
#include <sstream>
#include <stdexcept>

#include "DecIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


DecIRBuilder::DecIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void DecIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint64_t          reg       = this->operands[0].getValue();
  uint32_t          regSize   = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(reg, regSize);
  op2 << smt2lib::bv(1, regSize * REG_SIZE);

  /* Finale expr */
  expr << smt2lib::bvsub(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, reg, reg);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);

  /* Add the symbolic flags element to the current inst */
  inst.addElement(EflagsBuilder::af(se, ap, regSize, op1, op2));
  inst.addElement(EflagsBuilder::ofSub(se, ap, regSize, op1, op2));
  inst.addElement(EflagsBuilder::pf(se, ap));
  inst.addElement(EflagsBuilder::sf(se, ap, regSize));
  inst.addElement(EflagsBuilder::zf(se, ap, regSize));
}


void DecIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint64_t          mem       = this->operands[0].getValue();
  uint32_t          memSize   = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicMemOperand(mem, memSize);
  op2 << smt2lib::bv(1, memSize * REG_SIZE);

  /* Finale expr */
  expr << smt2lib::bvsub(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem);

  /* Apply the taint */
  ap.aluSpreadTaintMemMem(se, mem, mem);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);

  /* Add the symbolic flags element to the current inst */
  inst.addElement(EflagsBuilder::af(se, ap, memSize, op1, op2));
  inst.addElement(EflagsBuilder::ofSub(se, ap, memSize, op1, op2));
  inst.addElement(EflagsBuilder::pf(se, ap));
  inst.addElement(EflagsBuilder::sf(se, ap, memSize));
  inst.addElement(EflagsBuilder::zf(se, ap, memSize));
}


void DecIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  /* There is no <dec imm> available in x86 */
  OneOperandTemplate::stop(this->disas);
}


void DecIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  /* There is no <dec none> available in x86 */
  OneOperandTemplate::stop(this->disas);
}


Inst *DecIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "DEC");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    inst->addElement(ControlFlow::rip(ap, this->nextAddress));
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

