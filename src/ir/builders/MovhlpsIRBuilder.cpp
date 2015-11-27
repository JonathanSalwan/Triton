/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <algorithm>
#include <sstream>
#include <stdexcept>

#include <MovhlpsIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


MovhlpsIRBuilder::MovhlpsIRBuilder(__uint address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void MovhlpsIRBuilder::regImm(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void MovhlpsIRBuilder::regReg(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  auto reg1 = this->operands[0].getReg();
  auto regSize1 = this->operands[0].getReg().getSize();
  auto reg2 = this->operands[1].getReg();
  auto regSize2 = this->operands[1].getReg().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg1, regSize1);
  op2 = ap.buildSymbolicRegOperand(reg2, regSize2);

  /* Destination[63..0] = Source[127..64] */
  expr = smt2lib::concat(
            smt2lib::extract((DQWORD_SIZE_BIT - 1), QWORD_SIZE_BIT, op1), /* Destination[127..64] unchanged */
            smt2lib::extract((DQWORD_SIZE_BIT - 1), QWORD_SIZE_BIT, op2)  /* Destination[63..0] = Source[127..64]; */
          );

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg1, regSize1);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegReg(se, reg1, reg2);
}


void MovhlpsIRBuilder::regMem(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void MovhlpsIRBuilder::memImm(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void MovhlpsIRBuilder::memReg(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


Inst *MovhlpsIRBuilder::process(void) const {
  checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(*inst, this->operands, "MOVHLPS");
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

