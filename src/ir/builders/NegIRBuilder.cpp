/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <NegIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


NegIRBuilder::NegIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void NegIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1;
  uint64 reg       = this->operands[0].getValue();
  uint32 regSize   = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicRegOperand(reg, regSize);

  /* Finale expr */
  expr = smt2lib::bvneg(op1);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, reg, reg);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::afNeg(inst, se, ap, regSize, op1);
  EflagsBuilder::cfNeg(inst, se, ap, regSize, op1);
  EflagsBuilder::ofNeg(inst, se, ap, regSize, op1);
  EflagsBuilder::pf(inst, se, ap, regSize);
  EflagsBuilder::sf(inst, se, ap, regSize);
  EflagsBuilder::zf(inst, se, ap, regSize);
}


void NegIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *op1;
  uint64 mem       = this->operands[0].getValue();
  uint32 memSize   = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 = ap.buildSymbolicMemOperand(mem, memSize);

  /* Finale expr */
  expr = smt2lib::bvneg(op1);

  /* Create the symbolic expression */
  se = ap.createMemSE(inst, expr, mem, memSize);

  /* Apply the taint */
  ap.aluSpreadTaintMemMem(se, mem, mem, memSize);

  /* Add the symbolic flags expression to the current inst */
  EflagsBuilder::afNeg(inst, se, ap, memSize, op1);
  EflagsBuilder::cfNeg(inst, se, ap, memSize, op1);
  EflagsBuilder::ofNeg(inst, se, ap, memSize, op1);
  EflagsBuilder::pf(inst, se, ap, memSize);
  EflagsBuilder::sf(inst, se, ap, memSize);
  EflagsBuilder::zf(inst, se, ap, memSize);
}


void NegIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  /* There is no <inc imm> available in x86 */
  OneOperandTemplate::stop(this->disas);
}


void NegIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  /* There is no <inc none> available in x86 */
  OneOperandTemplate::stop(this->disas);
}


Inst *NegIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "NEG");
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

