#include <iostream>
#include <sstream>
#include <stdexcept>
#include <list>

#include <BswapIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicElement.h>


BswapIRBuilder::BswapIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void BswapIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1;
  uint64            reg       = this->operands[0].getValue();
  uint32            regSize   = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(reg, regSize);

  std::list<std::string> bytes;
  switch (regSize) {
    case QWORD_SIZE:
      bytes.push_front(smt2lib::extract(63, 56, op1.str()));
      bytes.push_front(smt2lib::extract(55, 48, op1.str()));
      bytes.push_front(smt2lib::extract(47, 40, op1.str()));
      bytes.push_front(smt2lib::extract(39, 32, op1.str()));
    case DWORD_SIZE:
      bytes.push_front(smt2lib::extract(31, 24, op1.str()));
      bytes.push_front(smt2lib::extract(23, 16, op1.str()));
      bytes.push_front(smt2lib::extract(15, 8, op1.str()));
      bytes.push_front(smt2lib::extract(7,  0, op1.str()));
      break;
    default:
      throw std::runtime_error("Error: BswapIRBuilder::reg() - Invalid register size");
  }

  /* Finale expr */
  expr << smt2lib::concat(bytes);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, reg, reg);
}


void BswapIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


void BswapIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


void BswapIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


Inst *BswapIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "BSWAP");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

