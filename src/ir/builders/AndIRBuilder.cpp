/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <AndIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


AndIRBuilder::AndIRBuilder(__uint address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void AndIRBuilder::regImm(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  auto reg = this->operands[0].getReg();
  auto imm = this->operands[1].getImm().getValue();
  auto regSize = this->operands[0].getReg().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg, regSize);
  op2 = smt2lib::bv(imm, regSize * BYTE_SIZE_BIT);

  /* Finale expr */
  expr = smt2lib::bvand(op1, op2);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegImm(se, reg);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::clearFlag(inst, ID_TMP_CF, "Clears carry flag");
  EflagsBuilder::clearFlag(inst, ID_TMP_OF, "Clears overflow flag");
  EflagsBuilder::pf(inst, se, reg);
  EflagsBuilder::sf(inst, se, reg);
  EflagsBuilder::zf(inst, se, reg);
}


void AndIRBuilder::regReg(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  auto reg1 = this->operands[0].getReg();
  auto reg2 = this->operands[1].getReg();
  auto regSize1 = this->operands[0].getReg().getSize();
  auto regSize2 = this->operands[1].getReg().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg1, regSize1);
  op2 = ap.buildSymbolicRegOperand(reg2, regSize2);

  // Final expr
  expr = smt2lib::bvand(op1, op2);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg1, regSize1);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, reg1, reg2);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::clearFlag(inst, ID_TMP_CF, "Clears carry flag");
  EflagsBuilder::clearFlag(inst, ID_TMP_OF, "Clears overflow flag");
  EflagsBuilder::pf(inst, se, reg1);
  EflagsBuilder::sf(inst, se, reg1);
  EflagsBuilder::zf(inst, se, reg1);
}


void AndIRBuilder::regMem(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  auto memSize = this->operands[1].getMem().getSize();
  auto mem = this->operands[1].getMem();
  auto reg = this->operands[0].getReg();
  auto regSize = this->operands[0].getReg().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg, regSize);
  op2 = ap.buildSymbolicMemOperand(mem, memSize);

  // Final expr
  expr = smt2lib::bvand(op1, op2);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegMem(se, reg, mem, memSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::clearFlag(inst, ID_TMP_CF, "Clears carry flag");
  EflagsBuilder::clearFlag(inst, ID_TMP_OF, "Clears overflow flag");
  EflagsBuilder::pf(inst, se, reg);
  EflagsBuilder::sf(inst, se, reg);
  EflagsBuilder::zf(inst, se, reg);
}


void AndIRBuilder::memImm(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  auto memSize = this->operands[0].getMem().getSize();
  auto mem = this->operands[0].getMem();
  auto imm = this->operands[1].getImm().getValue();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(mem, memSize);
  op2 = smt2lib::bv(imm, memSize * BYTE_SIZE_BIT);

  /* Final expr */
  expr = smt2lib::bvand(op1, op2);

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, mem, memSize);

  /* Apply the taint */
  ap.aluSpreadTaintMemImm(se, mem, memSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::clearFlag(inst, ID_TMP_CF, "Clears carry flag");
  EflagsBuilder::clearFlag(inst, ID_TMP_OF, "Clears overflow flag");
  EflagsBuilder::pf(inst, se, mem);
  EflagsBuilder::sf(inst, se, mem);
  EflagsBuilder::zf(inst, se, mem);
}


void AndIRBuilder::memReg(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  auto memSize = this->operands[0].getMem().getSize();
  auto mem = this->operands[0].getMem();
  auto reg = this->operands[1].getReg();
  auto regSize = this->operands[1].getReg().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(mem, memSize);
  op2 = ap.buildSymbolicRegOperand(reg, regSize);

  // Final expr
  expr = smt2lib::bvand(op1, op2);

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, mem, memSize);

  /* Apply the taint */
  ap.aluSpreadTaintMemReg(se, mem, reg, memSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::clearFlag(inst, ID_TMP_CF, "Clears carry flag");
  EflagsBuilder::clearFlag(inst, ID_TMP_OF, "Clears overflow flag");
  EflagsBuilder::pf(inst, se, mem);
  EflagsBuilder::sf(inst, se, mem);
  EflagsBuilder::zf(inst, se, mem);
}


Inst *AndIRBuilder::process(void) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(*inst, this->operands, "AND");
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

