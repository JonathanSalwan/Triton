/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <RclIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


RclIRBuilder::RclIRBuilder(reg_size address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void RclIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se1, *se2;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2, *cf, *res;
  auto reg = this->operands[0].getReg();
  auto imm = this->operands[1].getImm().getValue();
  auto regSize = this->operands[0].getReg().getSize();

  /* Create the SMT semantic */
  cf = ap.buildSymbolicFlagOperand(ID_TMP_CF);
  op1 = ap.buildSymbolicRegOperand(reg, regSize);
  /*
   * Note that SMT2-LIB doesn't support expression as rotate's value.
   * The op2 must be the concretization's value.
   */
  op2 = smt2lib::decimal(imm);

  /* Rcl expression */
  expr = smt2lib::bvrol(
            op2,
            smt2lib::concat(cf, op1)
          );

  /* Temporary extended expression */
  se1 = ap.createSE(inst, expr, "Temporary Extended Expression");

  /* Apply the taint */
  ap.assignmentSpreadTaintExprReg(se1, reg);

  /* Result expression */
  res = smt2lib::extract((regSize * REG_SIZE) - 1, 0, expr);

  /* Create the symbolic expression for the result */
  se2 = ap.createRegSE(inst, res, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se2, reg, reg);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::cfRcl(inst, se1, ap, regSize, op2);
  EflagsBuilder::ofRol(inst, se2, ap, regSize, op2); /* Same as ROL */
}


void RclIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se1, *se2;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2, *cf, *res;
  auto reg1 = this->operands[0].getReg();
  auto regSize1 = this->operands[0].getReg().getSize();

  /* Create the SMT semantic */
  cf = ap.buildSymbolicFlagOperand(ID_TMP_CF);
  op1 = ap.buildSymbolicRegOperand(reg1, regSize1);
  /*
   * Note that SMT2-LIB doesn't support expression as rotate's value.
   * The op2 must be the concretization's value.
   */
  op2 = smt2lib::decimal(ap.getRegisterValue(ID_TMP_RCX) & 0xff); /* 0xff -> There is only CL available */

  /* Rcl expression */
  expr = smt2lib::bvrol(
            op2,
            smt2lib::concat(cf, op1)
          );

  /* Temporary extended expression */
  se1 = ap.createSE(inst, expr, "Temporary Extended Expression");

  /* Apply the taint */
  ap.assignmentSpreadTaintExprReg(se1, reg1);

  /* Result expression */
  res = smt2lib::extract((regSize1 * REG_SIZE) - 1, 0, expr);

  /* Create the symbolic expression */
  se2 = ap.createRegSE(inst, res, reg1, regSize1);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se2, reg1, reg1);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::cfRcl(inst, se1, ap, regSize1, op2);
  EflagsBuilder::ofRol(inst, se2, ap, regSize1, op2); /* Same as ROL */
}


void RclIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void RclIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se1, *se2;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2, *cf, *res;
  auto memSize = this->operands[0].getMem().getSize();
  auto mem = this->operands[0].getMem();
  auto imm = this->operands[1].getImm().getValue();

  /* Create the SMT semantic */
  cf = ap.buildSymbolicFlagOperand(ID_TMP_CF);
  op1 = ap.buildSymbolicMemOperand(mem, memSize);
  /*
   * Note that SMT2-LIB doesn't support expression as rotate's value.
   * The op2 must be the concretization's value.
   */
  op2 = smt2lib::decimal(imm);

  /* Rcl expression */
  expr = smt2lib::bvrol(
            op2,
            smt2lib::concat(cf, op1)
          );

  /* Temporary extended expression */
  se1 = ap.createSE(inst, expr, "Temporary Extended Expression");

  /* Apply the taint */
  ap.assignmentSpreadTaintExprMem(se1, mem, memSize);

  /* Result expression */
  res = smt2lib::extract((memSize * REG_SIZE) - 1, 0, expr);

  /* Create the symbolic expression */
  se2 = ap.createMemSE(inst, res, mem, memSize);

  /* Apply the taint */
  ap.aluSpreadTaintMemMem(se2, mem, mem, memSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::cfRcl(inst, se1, ap, memSize, op2);
  EflagsBuilder::ofRol(inst, se2, ap, memSize, op2); /* Same as ROL */
}


void RclIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se1, *se2;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2, *cf, *res;
  auto memSize = this->operands[0].getMem().getSize();
  auto mem = this->operands[0].getMem();

  /* Create the SMT semantic */
  cf = ap.buildSymbolicFlagOperand(ID_TMP_CF);
  op1 = ap.buildSymbolicMemOperand(mem, memSize);
  /*
   * Note that SMT2-LIB doesn't support expression as rotate's value.
   * The op2 must be the concretization's value.
   */
  op2 = smt2lib::decimal(ap.getRegisterValue(ID_TMP_RCX) & 0xff); /* 0xff -> There is only CL available */

  /* Rcl expression */
  expr = smt2lib::bvrol(
            op2,
            smt2lib::concat(cf, op1)
          );

  /* Temporary extended expression */
  se1 = ap.createSE(inst, expr, "Temporary Extended Expression");

  /* Apply the taint */
  ap.assignmentSpreadTaintExprMem(se1, mem, memSize);

  /* Result expression */
  res = smt2lib::extract((memSize * REG_SIZE) - 1, 0, expr);

  /* Create the symbolic expression */
  se2 = ap.createMemSE(inst, res, mem, memSize);

  /* Apply the taint */
  ap.aluSpreadTaintMemMem(se2, mem, mem, memSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::cfRcl(inst, se1, ap, memSize, op2);
  EflagsBuilder::ofRol(inst, se2, ap, memSize, op2); /* Same as ROL */
}


Inst *RclIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "RCL");
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

#endif /* LIGHT_VERSION */

