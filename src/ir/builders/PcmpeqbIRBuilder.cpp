/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <algorithm>
#include <sstream>
#include <stdexcept>
#include <list>

#include <PcmpeqbIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


PcmpeqbIRBuilder::PcmpeqbIRBuilder(__uint address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void PcmpeqbIRBuilder::regImm(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void PcmpeqbIRBuilder::regReg(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  std::list<smt2lib::smtAstAbstractNode *> pck;
  auto reg1 = this->operands[0].getReg();
  auto regSize1 = this->operands[0].getReg().getSize();
  auto reg2 = this->operands[1].getReg();
  auto regSize2 = this->operands[1].getReg().getSize();

  /* PIN_GetContextReg doesn't supports MMX registers. */
  /* In this case, we skip the IR processing. */
  if (!reg1.isValid() || !reg2.isValid())
    return;

  op1 = ap.buildSymbolicRegOperand(reg1, regSize1);
  op2 = ap.buildSymbolicRegOperand(reg2, regSize2);

  for (uint32 index = 0; index < SSE_REG_SIZE; index++) {
    uint32 high = (SSE_REG_SIZE_BIT - 1) - (index * BYTE_SIZE_BIT);
    uint32 low  = (SSE_REG_SIZE_BIT - BYTE_SIZE_BIT) - (index * BYTE_SIZE_BIT);
    pck.push_back(smt2lib::ite(
                    smt2lib::equal(
                      smt2lib::extract(high, low, op1),
                      smt2lib::extract(high, low, op2)),
                    smt2lib::bv(0xff, BYTE_SIZE_BIT),
                    smt2lib::bv(0x00, BYTE_SIZE_BIT))
                 );
  }

  /* Create the SMT semantic */
  expr = smt2lib::concat(pck);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg1, regSize1);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, reg1, reg2);
}


void PcmpeqbIRBuilder::regMem(Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1, *op2;
  std::list<smt2lib::smtAstAbstractNode *> pck;
  auto reg = this->operands[0].getReg();
  auto regSize = this->operands[0].getReg().getSize();
  auto mem = this->operands[1].getMem();
  auto memSize = this->operands[1].getMem().getSize();

  /* PIN_GetContextReg doesn't supports MMX registers. */
  /* In this case, we skip the IR processing. */
  if (!reg.isValid())
    return;

  op1 = ap.buildSymbolicRegOperand(reg, regSize);
  op2 = ap.buildSymbolicMemOperand(mem, memSize);

  for (uint32 index = 0; index < SSE_REG_SIZE; index++) {
    uint32 high = (SSE_REG_SIZE_BIT - 1) - (index * BYTE_SIZE_BIT);
    uint32 low  = (SSE_REG_SIZE_BIT - BYTE_SIZE_BIT) - (index * BYTE_SIZE_BIT);
    pck.push_back(smt2lib::ite(
                    smt2lib::equal(
                      smt2lib::extract(high, low, op1),
                      smt2lib::extract(high, low, op2)),
                    smt2lib::bv(0xff, BYTE_SIZE_BIT),
                    smt2lib::bv(0x00, BYTE_SIZE_BIT))
                 );
  }

  /* Create the SMT semantic */
  expr = smt2lib::concat(pck);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegMem(se, reg, mem, memSize);
}


void PcmpeqbIRBuilder::memImm(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void PcmpeqbIRBuilder::memReg(Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


Inst *PcmpeqbIRBuilder::process(void) const {
  checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(*inst, this->operands, "PCMPEQB");
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

