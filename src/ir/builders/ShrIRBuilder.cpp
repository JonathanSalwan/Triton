/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <ShrIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


ShrIRBuilder::ShrIRBuilder(__uint address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void ShrIRBuilder::regImm(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  auto reg = this->operands[0].getReg();
  auto imm = this->operands[1].getImm().getValue();
  auto regSize = this->operands[0].getReg().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg, regSize);
  op2 = smt2lib::bv(imm, regSize * BYTE_SIZE_BIT);

  /* Finale expr */
  expr = smt2lib::bvlshr(op1, op2);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, reg, reg);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::cfShr(inst, se, reg, op1, op2);
  EflagsBuilder::ofShr(inst, se, reg, op1, op2);
  EflagsBuilder::pfShl(inst, se, reg, op2); /* Same that shl */
  EflagsBuilder::sfShl(inst, se, reg, op2); /* Same that shl */
  EflagsBuilder::zfShl(inst, se, reg, op2); /* Same that shl */
}


void ShrIRBuilder::regReg(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  auto reg = this->operands[0].getReg();
  auto regSize = this->operands[0].getReg().getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg, regSize);
  /* op2 = 8 bits register (CL) */
  op2 = smt2lib::zx((regSize - BYTE_SIZE) * BYTE_SIZE_BIT, ap.buildSymbolicRegOperand(ID_TMP_RCX, 1));

  /* Finale expr */
  expr = smt2lib::bvlshr(op1, op2);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, reg, reg);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::cfShr(inst, se, reg, op1, op2);
  EflagsBuilder::ofShr(inst, se, reg, op1, op2);
  EflagsBuilder::pfShl(inst, se, reg, op2); /* Same that shl */
  EflagsBuilder::sfShl(inst, se, reg, op2); /* Same that shl */
  EflagsBuilder::zfShl(inst, se, reg, op2); /* Same that shl */
}


void ShrIRBuilder::regMem(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void ShrIRBuilder::memImm(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  auto mem = this->operands[0].getMem();
  auto memSize = this->operands[0].getMem().getSize();
  auto imm = this->operands[1].getImm().getValue();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(mem, memSize);
  op2 = smt2lib::bv(imm, memSize * BYTE_SIZE_BIT);

  /* Final expr */
  expr = smt2lib::bvlshr(op1, op2);

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, mem, memSize);

  /* Apply the taint */
  ap.aluSpreadTaintMemMem(se, mem, mem, memSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::cfShr(inst, se, mem, op1, op2);
  EflagsBuilder::ofShr(inst, se, mem, op1, op2);
  EflagsBuilder::pfShl(inst, se, mem, op2) /* Same that shl */;
  EflagsBuilder::sfShl(inst, se, mem, op2) /* Same that shl */;
  EflagsBuilder::zfShl(inst, se, mem, op2) /* Same that shl */;
}


void ShrIRBuilder::memReg(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


Inst *ShrIRBuilder::process(void) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(*inst, this->operands, "SHR");
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

