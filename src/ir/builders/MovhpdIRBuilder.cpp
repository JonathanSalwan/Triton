/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <algorithm>
#include <sstream>
#include <stdexcept>

#include <MovhpdIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


MovhpdIRBuilder::MovhpdIRBuilder(__uint address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void MovhpdIRBuilder::regImm(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void MovhpdIRBuilder::regReg(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void MovhpdIRBuilder::regMem(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  auto memSize = this->operands[1].getMem().getSize();
  auto mem = this->operands[1].getMem();
  auto reg = this->operands[0].getReg();
  auto regSize = this->operands[0].getReg().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg, regSize);
  op2 = ap.buildSymbolicMemOperand(mem, memSize);

  expr = smt2lib::concat(
            smt2lib::extract((QWORD_SIZE_BIT - 1), 0, op2), /* Destination[127..64] = Source */
            smt2lib::extract((QWORD_SIZE_BIT - 1), 0, op1)  /* Destination[63..0] unchanged */
          );

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.assignmentSpreadTaintRegMem(se, reg, mem, memSize);
}


void MovhpdIRBuilder::memImm(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void MovhpdIRBuilder::memReg(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op2;
  auto memSize = this->operands[0].getMem().getSize();
  auto mem = this->operands[0].getMem();
  auto reg = this->operands[1].getReg();
  auto regSize = this->operands[1].getReg().getSize();

  /* Create the SMT semantic */
  op2 = ap.buildSymbolicRegOperand(reg, regSize);

  expr = smt2lib::extract((DQWORD_SIZE_BIT - 1), QWORD_SIZE_BIT, op2);

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, mem, memSize);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemReg(se, mem, reg, memSize);
}


Inst *MovhpdIRBuilder::process(void) const {
  checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(*inst, this->operands, "MOVHPD");
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

