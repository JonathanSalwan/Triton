#include <algorithm>
#include <sstream>
#include <stdexcept>

#include "MovapsIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


MovapsIRBuilder::MovapsIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void MovapsIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void MovapsIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint64_t          reg1      = this->operands[0].getValue();
  uint64_t          reg1Size  = this->operands[0].getSize();
  uint64_t          reg2      = this->operands[1].getValue();
  uint64_t          reg2Size  = this->operands[1].getSize();

  /* Create the SMT semantic */
  expr << ap.buildSymbolicRegOperand(reg2, reg2Size);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg1, reg1Size);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegReg(se, reg1, reg2);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void MovapsIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint32_t          readSize = this->operands[1].getSize();
  uint64_t          mem      = this->operands[1].getValue();
  uint64_t          reg      = this->operands[0].getValue();
  uint64_t          regSize  = this->operands[0].getSize();

  /* Create the SMT semantic */
  expr << ap.buildSymbolicMemOperand(mem, readSize);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg, regSize);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegMem(se, reg, mem, readSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void MovapsIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void MovapsIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint32_t          writeSize = this->operands[0].getSize();
  uint64_t          mem       = this->operands[0].getValue();
  uint64_t          reg       = this->operands[1].getValue();
  uint64_t          regSize   = this->operands[1].getSize();

  /* Create the SMT semantic */
  expr << ap.buildSymbolicRegOperand(reg, regSize);

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem, writeSize);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemReg(se, mem, reg, writeSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


Inst *MovapsIRBuilder::process(AnalysisProcessor &ap) const {
  checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "MOVAPS");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    inst->addElement(ControlFlow::rip(ap, this->nextAddress));
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

