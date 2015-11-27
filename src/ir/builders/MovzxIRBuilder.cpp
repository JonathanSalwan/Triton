/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <algorithm>
#include <sstream>
#include <stdexcept>

#include <MovzxIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>



MovzxIRBuilder::MovzxIRBuilder(__uint address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void MovzxIRBuilder::regImm(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void MovzxIRBuilder::regReg(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1;
  auto reg1 = this->operands[0].getReg();
  auto reg2 = this->operands[1].getReg();
  auto regSize1 = this->operands[0].getReg().getSize();
  auto regSize2 = this->operands[1].getReg().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg2, regSize2);

  /* Final expr */
  expr = smt2lib::zx((regSize1 * BYTE_SIZE_BIT) - (regSize2 * BYTE_SIZE_BIT), op1);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg1, regSize1);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegReg(se, reg1, reg2);
}


void MovzxIRBuilder::regMem(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1;
  auto memSize = this->operands[1].getMem().getSize();
  auto mem = this->operands[1].getMem();
  auto reg = this->operands[0].getReg();
  auto regSize = this->operands[0].getReg().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(mem, memSize);

  /* Final expr */
  expr = smt2lib::zx((regSize * BYTE_SIZE_BIT) - (memSize * BYTE_SIZE_BIT), op1);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegMem(se, reg, mem, memSize);
}


void MovzxIRBuilder::memImm(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void MovzxIRBuilder::memReg(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


Inst *MovzxIRBuilder::process(void) const {
  checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(*inst, this->operands, "MOVZX");
    ControlFlow::rip(*inst, this->nextAddress);
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

#endif /* LIGHT_VERSION */

