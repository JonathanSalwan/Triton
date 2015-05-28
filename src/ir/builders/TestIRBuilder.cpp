#include <iostream>
#include <sstream>
#include <stdexcept>

#include "TestIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


TestIRBuilder::TestIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void TestIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint64_t          reg     = this->operands[0].getValue();
  uint64_t          imm     = this->operands[1].getValue();
  uint32_t          regSize = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(reg, regSize);
  op2 << smt2lib::bv(imm, regSize * REG_SIZE);

  /* Finale expr */
  expr << smt2lib::bvand(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createSE(inst, expr);

  /* Add the symbolic flags element to the current inst */
  EflagsBuilder::clearFlag(inst, ap, ID_CF, "Clears carry flag");
  EflagsBuilder::clearFlag(inst, ap, ID_OF, "Clears overflow flag");
  EflagsBuilder::pf(inst, se, ap);
  EflagsBuilder::sf(inst, se, ap, regSize);
  EflagsBuilder::zf(inst, se, ap, regSize);
}


void TestIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint64_t          reg1     = this->operands[0].getValue();
  uint64_t          reg2     = this->operands[1].getValue();
  uint32_t          regSize1 = this->operands[0].getSize();
  uint32_t          regSize2 = this->operands[1].getSize();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(reg1, regSize1);
  op2 << ap.buildSymbolicRegOperand(reg2, regSize2);

  // Final expr
  expr << smt2lib::bvand(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createSE(inst, expr);

  /* Add the symbolic flags element to the current inst */
  EflagsBuilder::clearFlag(inst, ap, ID_CF, "Clears carry flag");
  EflagsBuilder::clearFlag(inst, ap, ID_OF, "Clears overflow flag");
  EflagsBuilder::pf(inst, se, ap);
  EflagsBuilder::sf(inst, se, ap, regSize1);
  EflagsBuilder::zf(inst, se, ap, regSize1);
}


void TestIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  /* There is no test reg, mem available in x86 */
  TwoOperandsTemplate::stop(this->disas);
}


void TestIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint32_t          writeSize = this->operands[0].getSize();
  uint64_t          mem       = this->operands[0].getValue();
  uint64_t          imm       = this->operands[1].getValue();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicMemOperand(mem, writeSize);
  op2 << smt2lib::bv(imm, writeSize * REG_SIZE);

  /* Final expr */
  expr << smt2lib::bvand(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createSE(inst, expr);

  /* Add the symbolic flags element to the current inst */
  EflagsBuilder::clearFlag(inst, ap, ID_CF, "Clears carry flag");
  EflagsBuilder::clearFlag(inst, ap, ID_OF, "Clears overflow flag");
  EflagsBuilder::pf(inst, se, ap);
  EflagsBuilder::sf(inst, se, ap, writeSize);
  EflagsBuilder::zf(inst, se, ap, writeSize);
}


void TestIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint32_t          writeSize = this->operands[0].getSize();
  uint64_t          mem       = this->operands[0].getValue();
  uint64_t          reg       = this->operands[1].getValue();
  uint32_t          regSize   = this->operands[1].getSize();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicMemOperand(mem, writeSize);
  op2 << ap.buildSymbolicRegOperand(reg, regSize);

  // Final expr
  expr << smt2lib::bvand(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createSE(inst, expr);

  /* Add the symbolic flags element to the current inst */
  EflagsBuilder::clearFlag(inst, ap, ID_CF, "Clears carry flag");
  EflagsBuilder::clearFlag(inst, ap, ID_OF, "Clears overflow flag");
  EflagsBuilder::pf(inst, se, ap);
  EflagsBuilder::sf(inst, se, ap, writeSize);
  EflagsBuilder::zf(inst, se, ap, writeSize);
}


Inst *TestIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "TEST");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

