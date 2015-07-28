/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <XorIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


XorIRBuilder::XorIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void XorIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  uint64 reg     = this->operands[0].getValue();
  uint64 imm     = this->operands[1].getValue();
  uint32 regSize = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg, regSize);
  op2 = smt2lib::bv(imm, regSize * REG_SIZE);

  /* Finale expr */
  expr = smt2lib::bvxor(op1, op2);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegImm(se, reg);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::clearFlag(inst, ap, ID_CF, "Clears carry flag");
  EflagsBuilder::clearFlag(inst, ap, ID_OF, "Clears overflow flag");
  EflagsBuilder::pf(inst, se, ap, regSize);
  EflagsBuilder::sf(inst, se, ap, regSize);
  EflagsBuilder::zf(inst, se, ap, regSize);
}


void XorIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
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
  expr = smt2lib::bvxor(op1, op2);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg1, regSize1);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, reg1, reg2);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::clearFlag(inst, ap, ID_CF, "Clears carry flag");
  EflagsBuilder::clearFlag(inst, ap, ID_OF, "Clears overflow flag");
  EflagsBuilder::pf(inst, se, ap, regSize1);
  EflagsBuilder::sf(inst, se, ap, regSize1);
  EflagsBuilder::zf(inst, se, ap, regSize1);
}


void XorIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  uint32 readSize = this->operands[1].getSize();
  uint64 mem      = this->operands[1].getValue();
  uint64 reg      = this->operands[0].getValue();
  uint32 regSize  = this->operands[1].getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg, regSize);
  op2 = ap.buildSymbolicMemOperand(mem, readSize);

  // Final expr
  expr = smt2lib::bvxor(op1, op2);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegMem(se, reg, mem, readSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::clearFlag(inst, ap, ID_CF, "Clears carry flag");
  EflagsBuilder::clearFlag(inst, ap, ID_OF, "Clears overflow flag");
  EflagsBuilder::pf(inst, se, ap, regSize);
  EflagsBuilder::sf(inst, se, ap, regSize);
  EflagsBuilder::zf(inst, se, ap, regSize);
}


void XorIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  uint32 writeSize = this->operands[0].getSize();
  uint64 mem       = this->operands[0].getValue();
  uint64 imm       = this->operands[1].getValue();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(mem, writeSize);
  op2 = smt2lib::bv(imm, writeSize * REG_SIZE);

  /* Final expr */
  expr = smt2lib::bvxor(op1, op2);

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, mem, writeSize);

  /* Apply the taint */
  ap.aluSpreadTaintMemImm(se, mem, writeSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::clearFlag(inst, ap, ID_CF, "Clears carry flag");
  EflagsBuilder::clearFlag(inst, ap, ID_OF, "Clears overflow flag");
  EflagsBuilder::pf(inst, se, ap, writeSize);
  EflagsBuilder::sf(inst, se, ap, writeSize);
  EflagsBuilder::zf(inst, se, ap, writeSize);
}


void XorIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  uint32 writeSize = this->operands[0].getSize();
  uint64 mem       = this->operands[0].getValue();
  uint64 reg       = this->operands[1].getValue();
  uint32 regSize   = this->operands[1].getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(mem, writeSize);
  op2 = ap.buildSymbolicRegOperand(reg, regSize);

  // Final expr
  expr = smt2lib::bvxor(op1, op2);

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, mem, writeSize);

  /* Apply the taint */
  ap.aluSpreadTaintMemReg(se, mem, reg, writeSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::clearFlag(inst, ap, ID_CF, "Clears carry flag");
  EflagsBuilder::clearFlag(inst, ap, ID_OF, "Clears overflow flag");
  EflagsBuilder::pf(inst, se, ap, writeSize);
  EflagsBuilder::sf(inst, se, ap, writeSize);
  EflagsBuilder::zf(inst, se, ap, writeSize);
}


Inst *XorIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "XOR");
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

