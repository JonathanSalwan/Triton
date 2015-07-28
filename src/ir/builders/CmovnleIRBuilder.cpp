/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <algorithm>
#include <sstream>
#include <stdexcept>

#include <CmovnleIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


CmovnleIRBuilder::CmovnleIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly){
}


void CmovnleIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void CmovnleIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *reg1e, *reg2e, *sf, *of, *zf;
  uint64 reg1    = this->operands[0].getValue();
  uint64 reg2    = this->operands[1].getValue();
  uint64 size1   = this->operands[0].getSize();
  uint64 size2   = this->operands[1].getSize();

  /* Create the flag SMT semantic */
  sf = ap.buildSymbolicFlagOperand(ID_SF);
  of = ap.buildSymbolicFlagOperand(ID_OF);
  zf = ap.buildSymbolicFlagOperand(ID_ZF);
  reg1e = ap.buildSymbolicRegOperand(reg1, size1);
  reg2e = ap.buildSymbolicRegOperand(reg2, size2);

  expr = smt2lib::ite(
            smt2lib::equal(
              smt2lib::bvor(smt2lib::bvxor(sf, of), zf),
              smt2lib::bvfalse()
            ),
            reg2e,
            reg1e);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg1, size1);

  /* Apply the taint via the concretization */
  if (((ap.getFlagValue(ID_SF) ^ ap.getFlagValue(ID_OF)) | ap.getFlagValue(ID_ZF)) == 0)
    ap.assignmentSpreadTaintRegReg(se, reg1, reg2);

}


void CmovnleIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *reg1e, *mem1e, *sf, *of, *zf;
  uint32 readSize = this->operands[1].getSize();
  uint64 mem      = this->operands[1].getValue();
  uint64 reg      = this->operands[0].getValue();
  uint64 regSize  = this->operands[0].getSize();

  /* Create the flag SMT semantic */
  sf = ap.buildSymbolicFlagOperand(ID_SF);
  of = ap.buildSymbolicFlagOperand(ID_OF);
  zf = ap.buildSymbolicFlagOperand(ID_ZF);
  reg1e = ap.buildSymbolicRegOperand(reg, regSize);
  mem1e = ap.buildSymbolicMemOperand(mem, readSize);

  expr = smt2lib::ite(
            smt2lib::equal(
              smt2lib::bvor(smt2lib::bvxor(sf, of), zf),
              smt2lib::bvfalse()
            ),
            mem1e,
            reg1e);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint via the concretization */
  if (((ap.getFlagValue(ID_SF) ^ ap.getFlagValue(ID_OF)) | ap.getFlagValue(ID_ZF)) == 0)
    ap.assignmentSpreadTaintRegMem(se, reg, mem, readSize);

}


void CmovnleIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void CmovnleIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


Inst *CmovnleIRBuilder::process(AnalysisProcessor &ap) const {
  checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "CMOVNLE");
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

