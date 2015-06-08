#include <iostream>
#include <sstream>
#include <stdexcept>

#include <ImulIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicElement.h>


ImulIRBuilder::ImulIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void ImulIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint64_t          reg     = this->operands[0].getValue();
  uint64_t          imm     = this->operands[1].getValue();
  uint32_t          regSize = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(reg, regSize);
  op2 << smt2lib::bv(imm, regSize * REG_SIZE);

  /* Finale expr */
  expr << smt2lib::bvmul(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegImm(se, reg);

  /* Add the symbolic flags element to the current inst */
  EflagsBuilder::cfMul(inst, se, ap, regSize, op1);
  EflagsBuilder::ofMul(inst, se, ap, regSize, op1);
  EflagsBuilder::sf(inst, se, ap, regSize);
}


void ImulIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2, op3;
  uint64_t          reg1     = this->operands[0].getValue();
  uint32_t          regSize1 = this->operands[0].getSize();
  uint64_t          reg2     = this->operands[1].getValue();
  uint32_t          regSize2 = this->operands[1].getSize();
  uint64_t          imm      = 0;

  if (this->operands[2].getType() == IRBuilderOperand::IMM)
    imm = this->operands[2].getValue();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(reg1, regSize1);
  op2 << ap.buildSymbolicRegOperand(reg2, regSize2);
  op3 << smt2lib::bv(imm, regSize1 * REG_SIZE);

  /* Finale expr */
  if (imm == 0)
    expr << smt2lib::bvmul(op1.str(), op2.str());
  else
    expr << smt2lib::bvmul(op2.str(), op3.str());

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, reg1, regSize1);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, reg1, reg2);

  /* Add the symbolic flags element to the current inst */
  EflagsBuilder::cfMul(inst, se, ap, regSize1, op1);
  EflagsBuilder::ofMul(inst, se, ap, regSize1, op1);
  EflagsBuilder::sf(inst, se, ap, regSize1);
}


void ImulIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2, op3;
  uint64_t          reg     = this->operands[0].getValue();
  uint32_t          regSize = this->operands[0].getSize();
  uint64_t          mem     = this->operands[1].getValue();
  uint32_t          memSize = this->operands[1].getSize();
  uint64_t          imm     = 0;

  if (this->operands[2].getType() == IRBuilderOperand::IMM)
    imm = this->operands[2].getValue();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(reg, regSize);
  op2 << ap.buildSymbolicMemOperand(mem, memSize);
  op3 << smt2lib::bv(imm, regSize * REG_SIZE);

  /* Finale expr */
  if (imm == 0)
    expr << smt2lib::bvmul(op1.str(), op2.str());
  else
    expr << smt2lib::bvmul(op2.str(), op3.str());

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegMem(se, reg, mem, memSize);

  /* Add the symbolic flags element to the current inst */
  EflagsBuilder::cfMul(inst, se, ap, regSize, op1);
  EflagsBuilder::ofMul(inst, se, ap, regSize, op1);
  EflagsBuilder::sf(inst, se, ap, regSize);
}


void ImulIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void ImulIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


Inst *ImulIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "IMUL");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

