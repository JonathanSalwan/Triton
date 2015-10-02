/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <sstream>
#include <stdexcept>
#include <list>

#include <BswapIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


BswapIRBuilder::BswapIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void BswapIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1;
  auto reg = this->operands[0].getReg();
  auto regSize = this->operands[0].getReg().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg, regSize);

  std::list<smt2lib::smtAstAbstractNode *> bytes;
  switch (regSize) {
    case QWORD_SIZE:
      bytes.push_front(smt2lib::extract(63, 56, op1));
      bytes.push_front(smt2lib::extract(55, 48, op1));
      bytes.push_front(smt2lib::extract(47, 40, op1));
      bytes.push_front(smt2lib::extract(39, 32, op1));
    case DWORD_SIZE:
      bytes.push_front(smt2lib::extract(31, 24, op1));
      bytes.push_front(smt2lib::extract(23, 16, op1));
      bytes.push_front(smt2lib::extract(15, 8, op1));
      bytes.push_front(smt2lib::extract(7,  0, op1));
      break;
    default:
      throw std::runtime_error("Error: BswapIRBuilder::reg() - Invalid register size");
  }

  /* Finale expr */
  expr = smt2lib::concat(bytes);

  /* Create the symbolic expression */
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
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

#endif /* LIGHT_VERSION */

