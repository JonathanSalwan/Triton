/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <algorithm>
#include <sstream>
#include <stdexcept>

#include <CmovbeIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


CmovbeIRBuilder::CmovbeIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly){
}


void CmovbeIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void CmovbeIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *reg1e, *reg2e, *cf, *zf;
  uint64 reg1    = this->operands[0].getValue();
  uint64 reg2    = this->operands[1].getValue();
  uint64 size1   = this->operands[0].getSize();
  uint64 size2   = this->operands[1].getSize();

  /* Create the SMT semantic */
  cf = ap.buildSymbolicFlagOperand(ID_CF);
  zf = ap.buildSymbolicFlagOperand(ID_ZF);
  reg1e = ap.buildSymbolicRegOperand(reg1, size1);
  reg2e = ap.buildSymbolicRegOperand(reg2, size2);

  expr = smt2lib::ite(
            smt2lib::equal(
              smt2lib::bvor(
                cf,
                zf
              ),
              smt2lib::bvtrue()
            ),
            reg2e,
            reg1e);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg1, size1);

  /* Apply the taint via the concretization */
  if (ap.getFlagValue(ID_CF) | ap.getFlagValue(ID_ZF))
    ap.assignmentSpreadTaintRegReg(se, reg1, reg2);

}


void CmovbeIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *reg1e, *mem1e, *cf, *zf;
  uint32 readSize = this->operands[1].getSize();
  uint64 mem      = this->operands[1].getValue();
  uint64 reg      = this->operands[0].getValue();
  uint64 regSize  = this->operands[0].getSize();

  /* Create the SMT semantic */
  cf = ap.buildSymbolicFlagOperand(ID_CF);
  zf = ap.buildSymbolicFlagOperand(ID_ZF);
  reg1e = ap.buildSymbolicRegOperand(reg, regSize);
  mem1e = ap.buildSymbolicMemOperand(mem, readSize);

  expr = smt2lib::ite(
            smt2lib::equal(
              smt2lib::bvor(
                cf,
                zf
              ),
              smt2lib::bvtrue()
            ),
            mem1e,
            reg1e);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint via the concretization */
  if (ap.getFlagValue(ID_CF) | ap.getFlagValue(ID_ZF))
    ap.assignmentSpreadTaintRegMem(se, reg, mem, readSize);

}


void CmovbeIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void CmovbeIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


Inst *CmovbeIRBuilder::process(AnalysisProcessor &ap) const {
  checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "CMOVBE");
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

