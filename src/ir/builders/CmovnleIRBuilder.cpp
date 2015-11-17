/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <algorithm>
#include <sstream>
#include <stdexcept>

#include <CmovnleIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


CmovnleIRBuilder::CmovnleIRBuilder(reg_size address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly){
}


void CmovnleIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void CmovnleIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *reg1e, *reg2e, *sf, *of, *zf;
  auto reg1 = this->operands[0].getReg();
  auto reg2 = this->operands[1].getReg();
  auto regSize1 = this->operands[0].getReg().getSize();
  auto regSize2 = this->operands[1].getReg().getSize();

  /* Create the flag SMT semantic */
  sf = ap.buildSymbolicFlagOperand(ID_TMP_SF);
  of = ap.buildSymbolicFlagOperand(ID_TMP_OF);
  zf = ap.buildSymbolicFlagOperand(ID_TMP_ZF);
  reg1e = ap.buildSymbolicRegOperand(reg1, regSize1);
  reg2e = ap.buildSymbolicRegOperand(reg2, regSize2);

  expr = smt2lib::ite(
            smt2lib::equal(
              smt2lib::bvor(smt2lib::bvxor(sf, of), zf),
              smt2lib::bvfalse()
            ),
            reg2e,
            reg1e);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, reg1, regSize1);

  /* Apply the taint via the concretization */
  if (((ap.getFlagValue(ID_TMP_SF) ^ ap.getFlagValue(ID_TMP_OF)) | ap.getFlagValue(ID_TMP_ZF)) == 0)
    ap.assignmentSpreadTaintRegReg(se, reg1, reg2);

}


void CmovnleIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *reg1e, *mem1e, *sf, *of, *zf;
  auto mem = this->operands[1].getMem();
  auto memSize = this->operands[1].getMem().getSize();
  auto reg = this->operands[0].getReg();
  auto regSize = this->operands[0].getReg().getSize();

  /* Create the flag SMT semantic */
  sf = ap.buildSymbolicFlagOperand(ID_TMP_SF);
  of = ap.buildSymbolicFlagOperand(ID_TMP_OF);
  zf = ap.buildSymbolicFlagOperand(ID_TMP_ZF);
  reg1e = ap.buildSymbolicRegOperand(reg, regSize);
  mem1e = ap.buildSymbolicMemOperand(mem, memSize);

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
  if (((ap.getFlagValue(ID_TMP_SF) ^ ap.getFlagValue(ID_TMP_OF)) | ap.getFlagValue(ID_TMP_ZF)) == 0)
    ap.assignmentSpreadTaintRegMem(se, reg, mem, memSize);

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

#endif /* LIGHT_VERSION */

