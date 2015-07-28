/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <TestIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


TestIRBuilder::TestIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void TestIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  uint64 reg     = this->operands[0].getValue();
  uint64 imm     = this->operands[1].getValue();
  uint32 regSize = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg, regSize);
  op2 = smt2lib::bv(imm, regSize * REG_SIZE);

  /* Finale expr */
  expr = smt2lib::bvand(op1, op2);

  /* Create the symbolic expression */
  se = ap.createSE(inst, expr);

  /* Apply the taint */
  ap.assignmentSpreadTaintExprReg(se, reg);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::clearFlag(inst, ap, ID_CF, "Clears carry flag");
  EflagsBuilder::clearFlag(inst, ap, ID_OF, "Clears overflow flag");
  EflagsBuilder::pf(inst, se, ap, regSize);
  EflagsBuilder::sf(inst, se, ap, regSize);
  EflagsBuilder::zf(inst, se, ap, regSize);
}


void TestIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  uint64 reg1     = this->operands[0].getValue();
  uint64 reg2     = this->operands[1].getValue();
  uint32 regSize1 = this->operands[0].getSize();
  uint32 regSize2 = this->operands[1].getSize();

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
  EflagsBuilder::clearFlag(inst, ap, ID_CF, "Clears carry flag");
  EflagsBuilder::clearFlag(inst, ap, ID_OF, "Clears overflow flag");
  EflagsBuilder::pf(inst, se, ap, regSize1);
  EflagsBuilder::sf(inst, se, ap, regSize1);
  EflagsBuilder::zf(inst, se, ap, regSize1);
}


void TestIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  /* There is no test reg, mem available in x86 */
  TwoOperandsTemplate::stop(this->disas);
}


void TestIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  uint32 readSize  = this->operands[0].getSize();
  uint64 mem       = this->operands[0].getValue();
  uint64 imm       = this->operands[1].getValue();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(mem, readSize);
  op2 = smt2lib::bv(imm, readSize * REG_SIZE);

  /* Final expr */
  expr = smt2lib::bvand(op1, op2);

  /* Create the symbolic expression */
  se = ap.createSE(inst, expr);

  /* Apply the taint */
  ap.assignmentSpreadTaintExprMem(se, mem, readSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::clearFlag(inst, ap, ID_CF, "Clears carry flag");
  EflagsBuilder::clearFlag(inst, ap, ID_OF, "Clears overflow flag");
  EflagsBuilder::pf(inst, se, ap, readSize);
  EflagsBuilder::sf(inst, se, ap, readSize);
  EflagsBuilder::zf(inst, se, ap, readSize);
}


void TestIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  uint32 readSize  = this->operands[0].getSize();
  uint64 mem       = this->operands[0].getValue();
  uint64 reg       = this->operands[1].getValue();
  uint32 regSize   = this->operands[1].getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(mem, readSize);
  op2 = ap.buildSymbolicRegOperand(reg, regSize);

  // Final expr
  expr = smt2lib::bvand(op1, op2);

  /* Create the symbolic expression */
  se = ap.createSE(inst, expr);

  /* Apply the taint */
  ap.assignmentSpreadTaintExprRegMem(se, reg, mem, readSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::clearFlag(inst, ap, ID_CF, "Clears carry flag");
  EflagsBuilder::clearFlag(inst, ap, ID_OF, "Clears overflow flag");
  EflagsBuilder::pf(inst, se, ap, readSize);
  EflagsBuilder::sf(inst, se, ap, readSize);
  EflagsBuilder::zf(inst, se, ap, readSize);
}


Inst *TestIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "TEST");
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

