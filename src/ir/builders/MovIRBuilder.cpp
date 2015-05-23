#include <algorithm>
#include <sstream>
#include <stdexcept>

#include "MovIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"



MovIRBuilder::MovIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void MovIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint64_t          reg  = this->operands[0].getValue();
  uint64_t          imm  = this->operands[1].getValue();
  uint64_t          size = this->operands[0].getSize();

  /* Create the SMT semantic */
  expr << smt2lib::bv(imm, size * REG_SIZE);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg, size);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegImm(se, reg);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void MovIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint64_t          reg1  = this->operands[0].getValue();
  uint64_t          reg2  = this->operands[1].getValue();
  uint64_t          size1 = this->operands[0].getSize();
  uint64_t          size2 = this->operands[1].getSize();

  /* Create the SMT semantic */
  expr << ap.buildSymbolicRegOperand(reg2, size2);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg1, size1);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegReg(se, reg1, reg2);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void MovIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
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


void MovIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint32_t          writeSize = this->operands[0].getSize();
  uint64_t          mem       = this->operands[0].getValue();
  uint64_t          imm       = this->operands[1].getValue();

  /* Create the SMT semantic */
  expr << smt2lib::bv(imm, writeSize * REG_SIZE);

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemImm(se, mem, writeSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void MovIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint32_t          writeSize = this->operands[0].getSize();
  uint64_t          mem       = this->operands[0].getValue();
  uint64_t          reg       = this->operands[1].getValue();
  uint64_t          regSize   = this->operands[1].getSize();

  /* Create the SMT semantic */
  expr << ap.buildSymbolicRegOperand(reg, regSize);

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemReg(se, mem, reg, writeSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


Inst *MovIRBuilder::process(AnalysisProcessor &ap) const {
  checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "MOV");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    inst->addElement(ControlFlow::rip(ap, this->nextAddress));
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

