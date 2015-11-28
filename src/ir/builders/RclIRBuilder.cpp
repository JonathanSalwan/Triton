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


RclIRBuilder::RclIRBuilder(__uint address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void RclIRBuilder::regImm(Inst &inst) const {
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
  res = smt2lib::extract((regSize * BYTE_SIZE_BIT) - 1, 0, expr);

  /* Create the symbolic expression for the result */
  se2 = ap.createRegSE(inst, res, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se2, reg, reg);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::cfRcl(inst, se1, reg, op2);
  EflagsBuilder::ofRol(inst, se2, reg, op2); /* Same as ROL */
}


void RclIRBuilder::regReg(Inst &inst) const {
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
  res = smt2lib::extract((regSize1 * BYTE_SIZE_BIT) - 1, 0, expr);

  /* Create the symbolic expression */
  se2 = ap.createRegSE(inst, res, reg1, regSize1);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se2, reg1, reg1);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::cfRcl(inst, se1, reg1, op2);
  EflagsBuilder::ofRol(inst, se2, reg1, op2); /* Same as ROL */
}


void RclIRBuilder::regMem(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void RclIRBuilder::memImm(Inst &inst) const {
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
  res = smt2lib::extract((memSize * BYTE_SIZE_BIT) - 1, 0, expr);

  /* Create the symbolic expression */
  se2 = ap.createMemSE(inst, res, mem, memSize);

  /* Apply the taint */
  ap.aluSpreadTaintMemMem(se2, mem, mem, memSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::cfRcl(inst, se1, mem, op2);
  EflagsBuilder::ofRol(inst, se2, mem, op2); /* Same as ROL */
}


void RclIRBuilder::memReg(Inst &inst) const {
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
  res = smt2lib::extract((memSize * BYTE_SIZE_BIT) - 1, 0, expr);

  /* Create the symbolic expression */
  se2 = ap.createMemSE(inst, res, mem, memSize);

  /* Apply the taint */
  ap.aluSpreadTaintMemMem(se2, mem, mem, memSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::cfRcl(inst, se1, mem, op2);
  EflagsBuilder::ofRol(inst, se2, mem, op2); /* Same as ROL */
}


Inst *RclIRBuilder::process(void) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(*inst, this->operands, "RCL");
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

