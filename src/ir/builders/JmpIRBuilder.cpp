/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <JmpIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


JmpIRBuilder::JmpIRBuilder(reg_size address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void JmpIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  smt2lib::smtAstAbstractNode *expr;
  auto imm = this->operands[0].getImm().getValue();

  /* Finale expr */
  expr = smt2lib::bv(imm, REG_SIZE_BIT);

  /* Create the symbolic expression */
  ap.createRegSE(inst, expr, ID_TMP_RIP, REG_SIZE, "RIP");
}


void JmpIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  smt2lib::smtAstAbstractNode *expr, *op1;
  auto reg = this->operands[0].getReg();
  auto regSize = this->operands[0].getReg().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg, regSize);

  /* Finale expr */
  expr = op1;

  /* Create the symbolic expression */
  ap.createRegSE(inst, expr, ID_TMP_RIP, REG_SIZE, "RIP");
}


void JmpIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  smt2lib::smtAstAbstractNode *expr, *op1;
  auto mem = this->operands[0].getMem();
  auto memSize = this->operands[0].getMem().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(mem, memSize);

  /* Finale expr */
  expr = op1;

  /* Create the symbolic expression */
  ap.createRegSE(inst, expr, ID_TMP_RIP, REG_SIZE, "RIP");
}


void JmpIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


Inst *JmpIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "JMP");
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

#endif /* LIGHT_VERSION */

