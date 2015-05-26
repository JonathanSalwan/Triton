#include <iostream>
#include <sstream>
#include <stdexcept>

#include "AdcIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


AdcIRBuilder::AdcIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void AdcIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2, op3;
  uint64_t          reg     = this->operands[0].getValue();
  uint64_t          imm     = this->operands[1].getValue();
  uint32_t          regSize = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(reg, regSize);
  op2 << smt2lib::bv(imm, regSize * REG_SIZE);
  op3 << ap.buildSymbolicFlagOperand(ID_CF, regSize);

  /* Finale expr */
  expr << smt2lib::bvadd(smt2lib::bvadd(op1.str(), op2.str()), op3.str());

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegImm(se, reg);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);

  /* Add the symbolic flags element to the current inst */
  inst.addElement(EflagsBuilder::af(se, ap, regSize, op1, op2));
  inst.addElement(EflagsBuilder::cfAdd(se, ap, op1));
  inst.addElement(EflagsBuilder::ofAdd(se, ap, regSize, op1, op2));
  inst.addElement(EflagsBuilder::pf(se, ap));
  inst.addElement(EflagsBuilder::sf(se, ap, regSize));
  inst.addElement(EflagsBuilder::zf(se, ap, regSize));
}


void AdcIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2, op3;
  uint64_t          reg1     = this->operands[0].getValue();
  uint64_t          reg2     = this->operands[1].getValue();
  uint32_t          regSize1 = this->operands[0].getSize();
  uint32_t          regSize2 = this->operands[1].getSize();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(reg1, regSize1);
  op2 << ap.buildSymbolicRegOperand(reg2, regSize2);
  op3 << ap.buildSymbolicFlagOperand(ID_CF, regSize1);

  // Final expr
  expr << smt2lib::bvadd(smt2lib::bvadd(op1.str(), op2.str()), op3.str());

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg1, regSize1);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, reg1, reg2);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);

  /* Add the symbolic flags element to the current inst */
  inst.addElement(EflagsBuilder::af(se, ap, regSize1, op1, op2));
  inst.addElement(EflagsBuilder::cfAdd(se, ap, op1));
  inst.addElement(EflagsBuilder::ofAdd(se, ap, regSize1, op1, op2));
  inst.addElement(EflagsBuilder::pf(se, ap));
  inst.addElement(EflagsBuilder::sf(se, ap, regSize1));
  inst.addElement(EflagsBuilder::zf(se, ap, regSize1));
}


void AdcIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2, op3;
  uint32_t          readSize = this->operands[1].getSize();
  uint64_t          mem      = this->operands[1].getValue();
  uint64_t          reg      = this->operands[0].getValue();
  uint32_t          regSize  = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(reg, regSize);
  op2 << ap.buildSymbolicMemOperand(mem, readSize);
  op3 << ap.buildSymbolicFlagOperand(ID_CF, regSize);

  // Final expr
  expr << smt2lib::bvadd(smt2lib::bvadd(op1.str(), op2.str()), op3.str());

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegMem(se, reg, mem, readSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);

  /* Add the symbolic flags element to the current inst */
  inst.addElement(EflagsBuilder::af(se, ap, regSize, op1, op2));
  inst.addElement(EflagsBuilder::cfAdd(se, ap, op1));
  inst.addElement(EflagsBuilder::ofAdd(se, ap, regSize, op1, op2));
  inst.addElement(EflagsBuilder::pf(se, ap));
  inst.addElement(EflagsBuilder::sf(se, ap, regSize));
  inst.addElement(EflagsBuilder::zf(se, ap, regSize));
}


void AdcIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2, op3;
  uint32_t          writeSize = this->operands[0].getSize();
  uint64_t          mem       = this->operands[0].getValue();
  uint64_t          imm       = this->operands[1].getValue();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicMemOperand(mem, writeSize);
  op2 << smt2lib::bv(imm, writeSize * REG_SIZE);
  op3 << ap.buildSymbolicFlagOperand(ID_CF, writeSize);

  /* Final expr */
  expr << smt2lib::bvadd(smt2lib::bvadd(op1.str(), op2.str()), op3.str());

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem, writeSize);

  /* Apply the taint */
  ap.aluSpreadTaintMemImm(se, mem, writeSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);

  /* Add the symbolic flags element to the current inst */
  inst.addElement(EflagsBuilder::af(se, ap, writeSize, op1, op2));
  inst.addElement(EflagsBuilder::cfAdd(se, ap, op1));
  inst.addElement(EflagsBuilder::ofAdd(se, ap, writeSize, op1, op2));
  inst.addElement(EflagsBuilder::pf(se, ap));
  inst.addElement(EflagsBuilder::sf(se, ap, writeSize));
  inst.addElement(EflagsBuilder::zf(se, ap, writeSize));
}


void AdcIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2, op3;
  uint32_t          writeSize = this->operands[0].getSize();
  uint64_t          mem       = this->operands[0].getValue();
  uint64_t          reg       = this->operands[1].getValue();
  uint32_t          regSize   = this->operands[1].getSize();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicMemOperand(mem, writeSize);
  op2 << ap.buildSymbolicRegOperand(reg, regSize);
  op3 << ap.buildSymbolicFlagOperand(ID_CF, regSize);

  // Final expr
  expr << smt2lib::bvadd(smt2lib::bvadd(op1.str(), op2.str()), op3.str());

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem, writeSize);

  /* Apply the taint */
  ap.aluSpreadTaintMemReg(se, mem, reg, writeSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);

  /* Add the symbolic flags element to the current inst */
  inst.addElement(EflagsBuilder::af(se, ap, writeSize, op1, op2));
  inst.addElement(EflagsBuilder::cfAdd(se, ap, op1));
  inst.addElement(EflagsBuilder::ofAdd(se, ap, writeSize, op1, op2));
  inst.addElement(EflagsBuilder::pf(se, ap));
  inst.addElement(EflagsBuilder::sf(se, ap, writeSize));
  inst.addElement(EflagsBuilder::zf(se, ap, writeSize));
}


Inst *AdcIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "ADC");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    inst->addElement(ControlFlow::rip(ap, this->nextAddress));
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

