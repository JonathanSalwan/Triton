#include <iostream>
#include <sstream>
#include <stdexcept>

#include "AndpsIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


AndpsIRBuilder::AndpsIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void AndpsIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void AndpsIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint64_t          reg1     = this->operands[0].getValue();
  uint64_t          reg2     = this->operands[1].getValue();
  uint32_t          regSize1 = this->operands[0].getSize();
  uint32_t          regSize2 = this->operands[1].getSize();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(reg1, regSize1);
  op2 << ap.buildSymbolicRegOperand(reg2, regSize2);

  // Final expr
  expr << smt2lib::bvand(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg1, regSize1);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, reg1, reg2);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void AndpsIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint32_t          readSize = this->operands[1].getSize();
  uint64_t          mem      = this->operands[1].getValue();
  uint64_t          reg      = this->operands[0].getValue();
  uint32_t          regSize  = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(reg, regSize);
  op2 << ap.buildSymbolicMemOperand(mem, readSize);

  // Final expr
  expr << smt2lib::bvand(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegMem(se, reg, mem, readSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void AndpsIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void AndpsIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


Inst *AndpsIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "ANDPS");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    inst->addElement(ControlFlow::rip(ap, this->nextAddress));
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

