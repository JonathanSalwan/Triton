/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <TestIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


TestIRBuilder::TestIRBuilder(__uint address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void TestIRBuilder::regImm(Inst &inst) const {
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
  se = ap.createSE(inst, expr);

  /* Apply the taint */
  ap.assignmentSpreadTaintExprReg(se, reg);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::clearFlag(inst, ID_TMP_CF, "Clears carry flag");
  EflagsBuilder::clearFlag(inst, ID_TMP_OF, "Clears overflow flag");
  EflagsBuilder::pf(inst, se, reg);
  EflagsBuilder::sf(inst, se, reg);
  EflagsBuilder::zf(inst, se, reg);
}


void TestIRBuilder::regReg(Inst &inst) const {
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
  se = ap.createSE(inst, expr);

  /* Apply the taint */
  ap.assignmentSpreadTaintExprRegReg(se, reg1, reg2);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::clearFlag(inst, ID_TMP_CF, "Clears carry flag");
  EflagsBuilder::clearFlag(inst, ID_TMP_OF, "Clears overflow flag");
  EflagsBuilder::pf(inst, se, reg1);
  EflagsBuilder::sf(inst, se, reg1);
  EflagsBuilder::zf(inst, se, reg1);
}


void TestIRBuilder::regMem(Inst &inst) const {
  /* There is no test reg, mem available in x86 */
  TwoOperandsTemplate::stop(this->disas);
}


void TestIRBuilder::memImm(Inst &inst) const {
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
  se = ap.createSE(inst, expr);

  /* Apply the taint */
  ap.assignmentSpreadTaintExprMem(se, mem, memSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::clearFlag(inst, ID_TMP_CF, "Clears carry flag");
  EflagsBuilder::clearFlag(inst, ID_TMP_OF, "Clears overflow flag");
  EflagsBuilder::pf(inst, se, mem);
  EflagsBuilder::sf(inst, se, mem);
  EflagsBuilder::zf(inst, se, mem);
}


void TestIRBuilder::memReg(Inst &inst) const {
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
  se = ap.createSE(inst, expr);

  /* Apply the taint */
  ap.assignmentSpreadTaintExprRegMem(se, reg, mem, memSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::clearFlag(inst, ID_TMP_CF, "Clears carry flag");
  EflagsBuilder::clearFlag(inst, ID_TMP_OF, "Clears overflow flag");
  EflagsBuilder::pf(inst, se, mem);
  EflagsBuilder::sf(inst, se, mem);
  EflagsBuilder::zf(inst, se, mem);
}


Inst *TestIRBuilder::process(void) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(*inst, this->operands, "TEST");
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

