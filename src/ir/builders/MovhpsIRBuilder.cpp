#include <algorithm>
#include <sstream>
#include <stdexcept>

#include "MovhpsIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


MovhpsIRBuilder::MovhpsIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void MovhpsIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void MovhpsIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void MovhpsIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint32_t          readSize = this->operands[1].getSize();
  uint64_t          mem      = this->operands[1].getValue();
  uint64_t          reg      = this->operands[0].getValue();
  uint64_t          regSize  = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(reg, regSize);
  op2 << ap.buildSymbolicMemOperand(mem, readSize);

  expr << smt2lib::concat(
            smt2lib::extract(63, 0, op2.str()), /* Destination[64..127] = Source */
            smt2lib::extract(63, 0, op1.str())  /* Destination[0..63] unchanged */
          );

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg, regSize);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegMem(se, reg, mem, readSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void MovhpsIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void MovhpsIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint32_t          writeSize = this->operands[0].getSize();
  uint64_t          mem       = this->operands[0].getValue();
  uint64_t          reg       = this->operands[1].getValue();
  uint64_t          regSize   = this->operands[1].getSize();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicMemOperand(mem, writeSize);
  op2 << ap.buildSymbolicRegOperand(reg, regSize);

  expr << smt2lib::extract(127, 64, op2.str());

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem, writeSize);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemReg(se, mem, reg, writeSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


Inst *MovhpsIRBuilder::process(AnalysisProcessor &ap) const {
  checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "MOVHPS");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    inst->addElement(ControlFlow::rip(ap, this->nextAddress));
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

