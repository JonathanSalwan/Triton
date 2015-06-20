#include <iostream>
#include <sstream>
#include <stdexcept>

#include <JmpIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicElement.h>


JmpIRBuilder::JmpIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void JmpIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  std::stringstream expr;
  uint64            imm = this->operands[0].getValue();

  /* Finale expr */
  expr << smt2lib::bv(imm, REG_SIZE_BIT);

  /* Create the symbolic element */
  ap.createRegSE(inst, expr, ID_RIP, REG_SIZE, "RIP");
}


void JmpIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  std::stringstream expr, op1;
  uint64            reg     = this->operands[0].getValue();
  uint32            regSize = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(reg, regSize);

  /* Finale expr */
  expr << op1.str();

  /* Create the symbolic element */
  ap.createRegSE(inst, expr, ID_RIP, REG_SIZE, "RIP");
}


void JmpIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  std::stringstream expr, op1;
  uint64            mem     = this->operands[0].getValue();
  uint32            memSize = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicMemOperand(mem, memSize);

  /* Finale expr */
  expr << op1.str();

  /* Create the symbolic element */
  ap.createRegSE(inst, expr, ID_RIP, REG_SIZE, "RIP");
}


void JmpIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


Inst *JmpIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "JMP");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

