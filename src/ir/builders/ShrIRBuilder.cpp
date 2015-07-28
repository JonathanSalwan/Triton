/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <ShrIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


ShrIRBuilder::ShrIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void ShrIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  uint64 reg     = this->operands[0].getValue();
  uint64 imm     = this->operands[1].getValue();
  uint32 regSize = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg, regSize);
  op2 = smt2lib::bv(imm, regSize * REG_SIZE);

  /* Finale expr */
  expr = smt2lib::bvlshr(op1, op2);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, reg, reg);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::cfShr(inst, se, ap, regSize, op1, op2);
  EflagsBuilder::ofShr(inst, se, ap, regSize, op1, op2);
  EflagsBuilder::pfShl(inst, se, ap, regSize, op2); /* Same that shl */
  EflagsBuilder::sfShl(inst, se, ap, regSize, op2); /* Same that shl */
  EflagsBuilder::zfShl(inst, se, ap, regSize, op2); /* Same that shl */
}


void ShrIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  uint64 reg     = this->operands[0].getValue();
  uint32 regSize = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg, regSize);
  /* op2 = 8 bits register (CL) */
  op2 = smt2lib::zx((regSize - BYTE_SIZE) * REG_SIZE, ap.buildSymbolicRegOperand(ID_RCX, 1));

  /* Finale expr */
  expr = smt2lib::bvlshr(op1, op2);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, reg, reg);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::cfShr(inst, se, ap, regSize, op1, op2);
  EflagsBuilder::ofShr(inst, se, ap, regSize, op1, op2);
  EflagsBuilder::pfShl(inst, se, ap, regSize, op2); /* Same that shl */
  EflagsBuilder::sfShl(inst, se, ap, regSize, op2); /* Same that shl */
  EflagsBuilder::zfShl(inst, se, ap, regSize, op2); /* Same that shl */
}


void ShrIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void ShrIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  uint32 writeSize = this->operands[0].getSize();
  uint64 mem       = this->operands[0].getValue();
  uint64 imm       = this->operands[1].getValue();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(mem, writeSize);
  op2 = smt2lib::bv(imm, writeSize * REG_SIZE);

  /* Final expr */
  expr = smt2lib::bvlshr(op1, op2);

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, mem, writeSize);

  /* Apply the taint */
  ap.aluSpreadTaintMemMem(se, mem, mem, writeSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::cfShr(inst, se, ap, writeSize, op1, op2);
  EflagsBuilder::ofShr(inst, se, ap, writeSize, op1, op2);
  EflagsBuilder::pfShl(inst, se, ap, writeSize, op2) /* Same that shl */;
  EflagsBuilder::sfShl(inst, se, ap, writeSize, op2) /* Same that shl */;
  EflagsBuilder::zfShl(inst, se, ap, writeSize, op2) /* Same that shl */;
}


void ShrIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


Inst *ShrIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "SHR");
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

