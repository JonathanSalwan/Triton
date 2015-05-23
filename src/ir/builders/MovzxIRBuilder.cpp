#include <algorithm>
#include <sstream>
#include <stdexcept>

#include "MovzxIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"



MovzxIRBuilder::MovzxIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void MovzxIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void MovzxIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1;
  uint64_t          reg1  = this->operands[0].getValue();
  uint64_t          reg2  = this->operands[1].getValue();
  uint64_t          size1 = this->operands[0].getSize();
  uint64_t          size2 = this->operands[1].getSize();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(reg2, size2);

  /* Final expr */
  expr << smt2lib::zx(op1.str(), (size1 * REG_SIZE) - (size2 * REG_SIZE));

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg1, size1);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegReg(se, reg1, reg2);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void MovzxIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1;
  uint32_t          readSize = this->operands[1].getSize();
  uint64_t          mem      = this->operands[1].getValue();
  uint64_t          reg      = this->operands[0].getValue();
  uint64_t          regSize  = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicMemOperand(mem, readSize);

  /* Final expr */
  expr << smt2lib::zx(op1.str(), (regSize * REG_SIZE) - (readSize * REG_SIZE));

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg, regSize);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegMem(se, reg, mem, readSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void MovzxIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void MovzxIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


Inst *MovzxIRBuilder::process(AnalysisProcessor &ap) const {
  checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "MOVZX");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    inst->addElement(ControlFlow::rip(ap, this->nextAddress));
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

