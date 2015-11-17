/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <SarIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


SarIRBuilder::SarIRBuilder(reg_size address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void SarIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  auto reg = this->operands[0].getReg();
  auto imm = this->operands[1].getImm().getValue();
  auto regSize = this->operands[0].getReg().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg, regSize);
  op2 = smt2lib::bv(imm, regSize * REG_SIZE);

  /* Finale expr */
  expr = smt2lib::bvashr(op1, op2);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, reg, reg);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::cfSar(inst, se, ap, regSize, op1, op2);
  EflagsBuilder::ofSar(inst, se, ap, regSize, op2);
  EflagsBuilder::pfShl(inst, se, ap, regSize, op2); /* Same that shl */
  EflagsBuilder::sfShl(inst, se, ap, regSize, op2); /* Same that shl */
  EflagsBuilder::zfShl(inst, se, ap, regSize, op2); /* Same that shl */
}


void SarIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  auto reg = this->operands[0].getReg();
  auto regSize = this->operands[0].getReg().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg, regSize);
  /* op2 = 8 bits register (CL) */
  op2 = smt2lib::zx((regSize - BYTE_SIZE) * REG_SIZE, ap.buildSymbolicRegOperand(ID_TMP_RCX, 1));

  /* Finale expr */
  expr = smt2lib::bvashr(op1, op2);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, reg, reg);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::cfSar(inst, se, ap, regSize, op1, op2);
  EflagsBuilder::ofSar(inst, se, ap, regSize, op2);
  EflagsBuilder::pfShl(inst, se, ap, regSize, op2); /* Same that shl */
  EflagsBuilder::sfShl(inst, se, ap, regSize, op2); /* Same that shl */
  EflagsBuilder::zfShl(inst, se, ap, regSize, op2); /* Same that shl */
}


void SarIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void SarIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  auto memSize = this->operands[0].getMem().getSize();
  auto mem = this->operands[0].getMem();
  auto imm = this->operands[1].getImm().getValue();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(mem, memSize);
  op2 = smt2lib::bv(imm, memSize * REG_SIZE);

  /* Final expr */
  expr = smt2lib::bvashr(op1, op2);

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, mem, memSize);

  /* Apply the taint */
  ap.aluSpreadTaintMemMem(se, mem, mem, memSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::cfSar(inst, se, ap, memSize, op1, op2);
  EflagsBuilder::ofSar(inst, se, ap, memSize, op2);
  EflagsBuilder::pfShl(inst, se, ap, memSize, op2); /* Same that shl */
  EflagsBuilder::sfShl(inst, se, ap, memSize, op2); /* Same that shl */
  EflagsBuilder::zfShl(inst, se, ap, memSize, op2); /* Same that shl */
}


void SarIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


Inst *SarIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "SAR");
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

