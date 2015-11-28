/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <XaddIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


XaddIRBuilder::XaddIRBuilder(__uint address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void XaddIRBuilder::regImm(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void XaddIRBuilder::regReg(Inst &inst) const {
  SymbolicExpression *se, *se1, *se2;
  smt2lib::smtAstAbstractNode *expr, *expr1, *expr2, *op1, *op2;
  auto reg1 = this->operands[0].getReg();
  auto reg2 = this->operands[1].getReg();
  auto regSize1 = this->operands[0].getReg().getSize();
  auto regSize2 = this->operands[1].getReg().getSize();
  auto tmpReg1Taint = ap.isRegTainted(reg1);
  auto tmpReg2Taint = ap.isRegTainted(reg2);

  /* Part 1 - xchg expr */
  op1 = ap.buildSymbolicRegOperand(reg1, regSize1);
  op2 = ap.buildSymbolicRegOperand(reg2, regSize2);

  expr1 = op2;
  expr2 = op1;

  /* Create the symbolic expression */
  se1 = ap.createRegSE(inst, expr1, reg1, regSize1);
  se2 = ap.createRegSE(inst, expr2, reg2, regSize2);

  /* Apply the taint */
  ap.setTaintReg(se1, reg1, tmpReg2Taint);
  ap.setTaintReg(se2, reg2, tmpReg1Taint);

  /* == == */

  /* Part 2 - add expr */
  op1 = ap.buildSymbolicRegOperand(reg1, regSize1);
  op2 = ap.buildSymbolicRegOperand(reg2, regSize2);

  expr = smt2lib::bvadd(op1, op2);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg1, regSize1);

  /* Apply the taint */
  ap.aluSpreadTaintRegImm(se, reg1);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::af(inst, se, reg2, op1, op2);
  EflagsBuilder::cfAdd(inst, se, reg2, op1);
  EflagsBuilder::ofAdd(inst, se, reg2, op1, op2);
  EflagsBuilder::pf(inst, se, reg2);
  EflagsBuilder::sf(inst, se, reg2);
  EflagsBuilder::zf(inst, se, reg2);
}


void XaddIRBuilder::regMem(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void XaddIRBuilder::memImm(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void XaddIRBuilder::memReg(Inst &inst) const {
  SymbolicExpression *se, *se1, *se2;
  smt2lib::smtAstAbstractNode *expr, *expr1, *expr2, *op1, *op2;
  auto mem1 = this->operands[0].getMem();
  auto reg2 = this->operands[1].getReg();
  auto memSize1 = this->operands[0].getMem().getSize();
  auto regSize2 = this->operands[1].getReg().getSize();
  auto tmpMem1Taint = ap.isMemTainted(mem1);
  auto tmpReg2Taint = ap.isRegTainted(reg2);

  /* Part 1 - xchg expr */
  op1 = ap.buildSymbolicMemOperand(mem1, memSize1);
  op2 = ap.buildSymbolicRegOperand(reg2, regSize2);

  expr1 = op2;
  expr2 = op1;

  /* Create the symbolic expression */
  se1 = ap.createMemSE(inst, expr1, mem1, memSize1);
  se2 = ap.createRegSE(inst, expr2, reg2, regSize2);

  /* Apply the taint */
  ap.setTaintMem(se1, mem1, tmpReg2Taint);
  ap.setTaintReg(se2, reg2, tmpMem1Taint);

  /* == == */

  /* Part 2 - add expr */
  op1 = ap.buildSymbolicMemOperand(mem1, memSize1);
  op2 = ap.buildSymbolicRegOperand(reg2, regSize2);

  expr = smt2lib::bvadd(op1, op2);

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, mem1, memSize1);

  /* Apply the taint */
  ap.aluSpreadTaintRegMem(se, reg2, mem1, memSize1);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::af(inst, se, mem1, op1, op2);
  EflagsBuilder::cfAdd(inst, se, mem1, op1);
  EflagsBuilder::ofAdd(inst, se, mem1, op1, op2);
  EflagsBuilder::pf(inst, se, mem1);
  EflagsBuilder::sf(inst, se, mem1);
  EflagsBuilder::zf(inst, se, mem1);
}


Inst *XaddIRBuilder::process(void) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(*inst, this->operands, "XADD");
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

