/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <SbbIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


SbbIRBuilder::SbbIRBuilder(__uint address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void SbbIRBuilder::regImm(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2, *op3;
  auto reg = this->operands[0].getReg();
  auto imm = this->operands[1].getImm().getValue();
  auto regSize = this->operands[0].getReg().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg, regSize);
  op2 = smt2lib::bv(imm, regSize * BYTE_SIZE_BIT);
  op3 = ap.buildSymbolicFlagOperand(ID_TMP_CF, regSize);

  /* Finale expr */
  expr = smt2lib::bvsub(op1, smt2lib::bvadd(op2, op3));

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegImm(se, reg);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::af(inst, se, reg, op1, op2);
  EflagsBuilder::cfSub(inst, se, reg, op1, op2);
  EflagsBuilder::ofSub(inst, se, reg, op1, op2);
  EflagsBuilder::pf(inst, se, reg);
  EflagsBuilder::sf(inst, se, reg);
  EflagsBuilder::zf(inst, se, reg);
}


void SbbIRBuilder::regReg(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2, *op3;
  auto reg1 = this->operands[0].getReg();
  auto reg2 = this->operands[1].getReg();
  auto regSize1 = this->operands[0].getReg().getSize();
  auto regSize2 = this->operands[1].getReg().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg1, regSize1);
  op2 = ap.buildSymbolicRegOperand(reg2, regSize2);
  op3 = ap.buildSymbolicFlagOperand(ID_TMP_CF, regSize1);

  /* Final expr */
  expr = smt2lib::bvsub(op1, smt2lib::bvadd(op2, op3));

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg1, regSize1);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, reg1, reg2);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::af(inst, se, reg1, op1, op2);
  EflagsBuilder::cfSub(inst, se, reg1, op1, op2);
  EflagsBuilder::ofSub(inst, se, reg1, op1, op2);
  EflagsBuilder::pf(inst, se, reg1);
  EflagsBuilder::sf(inst, se, reg1);
  EflagsBuilder::zf(inst, se, reg1);
}


void SbbIRBuilder::regMem(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2, *op3;
  auto memSize = this->operands[1].getMem().getSize();
  auto mem = this->operands[1].getMem();
  auto reg = this->operands[0].getReg();
  auto regSize = this->operands[0].getReg().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg, regSize);
  op2 = ap.buildSymbolicMemOperand(mem, memSize);
  op3 = ap.buildSymbolicFlagOperand(ID_TMP_CF, regSize);

  /* Final expr */
  expr = smt2lib::bvsub(op1, smt2lib::bvadd(op2, op3));

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegMem(se, reg, mem, memSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::af(inst, se, reg, op1, op2);
  EflagsBuilder::cfSub(inst, se, reg, op1, op2);
  EflagsBuilder::ofSub(inst, se, reg, op1, op2);
  EflagsBuilder::pf(inst, se, reg);
  EflagsBuilder::sf(inst, se, reg);
  EflagsBuilder::zf(inst, se, reg);
}


void SbbIRBuilder::memImm(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2, *op3;
  auto memSize = this->operands[0].getMem().getSize();
  auto mem = this->operands[0].getMem();
  auto imm = this->operands[1].getImm().getValue();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(mem, memSize);
  op2 = smt2lib::bv(imm, memSize * BYTE_SIZE_BIT);
  op3 = ap.buildSymbolicFlagOperand(ID_TMP_CF, memSize);

  /* Final expr */
  expr = smt2lib::bvsub(op1, smt2lib::bvadd(op2, op3));

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, mem, memSize);

  /* Apply the taint */
  ap.aluSpreadTaintMemImm(se, mem, memSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::af(inst, se, mem, op1, op2);
  EflagsBuilder::cfSub(inst, se, mem, op1, op2);
  EflagsBuilder::ofSub(inst, se, mem, op1, op2);
  EflagsBuilder::pf(inst, se, mem);
  EflagsBuilder::sf(inst, se, mem);
  EflagsBuilder::zf(inst, se, mem);
}


void SbbIRBuilder::memReg(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2, *op3;
  auto memSize = this->operands[0].getMem().getSize();
  auto mem = this->operands[0].getMem();
  auto reg = this->operands[1].getReg();
  auto regSize = this->operands[1].getReg().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(mem, memSize);
  op2 = ap.buildSymbolicRegOperand(reg, regSize);
  op3 = ap.buildSymbolicFlagOperand(ID_TMP_CF, regSize);

  /* Final expr */
  expr = smt2lib::bvsub(op1, smt2lib::bvadd(op2, op3));

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, mem, memSize);

  /* Apply the taint */
  ap.aluSpreadTaintMemReg(se, mem, reg, memSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::af(inst, se, mem, op1, op2);
  EflagsBuilder::cfSub(inst, se, mem, op1, op2);
  EflagsBuilder::ofSub(inst, se, mem, op1, op2);
  EflagsBuilder::pf(inst, se, mem);
  EflagsBuilder::sf(inst, se, mem);
  EflagsBuilder::zf(inst, se, mem);
}


Inst *SbbIRBuilder::process(void) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(*inst, this->operands, "SBB");
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

