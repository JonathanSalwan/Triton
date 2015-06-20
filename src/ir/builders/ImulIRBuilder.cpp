#include <iostream>
#include <sstream>
#include <stdexcept>

#include <ImulIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicElement.h>


ImulIRBuilder::ImulIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void ImulIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint64            reg     = this->operands[0].getValue();
  uint64            imm     = this->operands[1].getValue();
  uint32            regSize = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(reg, regSize);
  op2 << smt2lib::bv(imm, regSize * REG_SIZE);

  /* Finale expr */
  expr << smt2lib::extract(regSize,
            smt2lib::bvmul(
              smt2lib::sx(op1.str(), regSize * REG_SIZE),
              smt2lib::sx(op2.str(), regSize * REG_SIZE)
            )
          );

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegImm(se, reg);

  /* Add the symbolic flags element to the current inst */
  EflagsBuilder::cfImul(inst, se, ap, regSize, op1);
  EflagsBuilder::ofImul(inst, se, ap, regSize, op1);
  EflagsBuilder::sf(inst, se, ap, regSize);
}


void ImulIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2, op3;
  uint64            reg1     = this->operands[0].getValue();
  uint32            regSize1 = this->operands[0].getSize();
  uint64            reg2     = this->operands[1].getValue();
  uint32            regSize2 = this->operands[1].getSize();
  uint64            imm      = 0;

  if (this->operands[2].getType() == IRBuilderOperand::IMM)
    imm = this->operands[2].getValue();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(reg1, regSize1);
  op2 << ap.buildSymbolicRegOperand(reg2, regSize2);
  op3 << smt2lib::bv(imm, regSize2 * REG_SIZE);

  /* Finale expr */
  if (imm == 0)
    expr << smt2lib::extract(regSize1,
              smt2lib::bvmul(
                smt2lib::sx(op1.str(), regSize1 * REG_SIZE),
                smt2lib::sx(op2.str(), regSize2 * REG_SIZE)
              )
            );
  else
    expr << smt2lib::extract(regSize1,
              smt2lib::bvmul(
                smt2lib::sx(op2.str(), regSize1 * REG_SIZE),
                smt2lib::sx(op3.str(), regSize2 * REG_SIZE)
              )
            );

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, reg1, regSize1);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, reg1, reg2);

  /* Add the symbolic flags element to the current inst */
  EflagsBuilder::cfImul(inst, se, ap, regSize1, op1);
  EflagsBuilder::ofImul(inst, se, ap, regSize1, op1);
  EflagsBuilder::sf(inst, se, ap, regSize1);
}


void ImulIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2, op3;
  uint64            reg     = this->operands[0].getValue();
  uint32            regSize = this->operands[0].getSize();
  uint64            mem     = this->operands[1].getValue();
  uint32            memSize = this->operands[1].getSize();
  uint64            imm     = 0;

  if (this->operands[2].getType() == IRBuilderOperand::IMM)
    imm = this->operands[2].getValue();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(reg, regSize);
  op2 << ap.buildSymbolicMemOperand(mem, memSize);
  op3 << smt2lib::bv(imm, memSize * REG_SIZE);

  /* Finale expr */
  if (imm == 0)
    expr << smt2lib::extract(regSize,
              smt2lib::bvmul(
                smt2lib::sx(op1.str(), regSize * REG_SIZE),
                smt2lib::sx(op2.str(), regSize * REG_SIZE)
              )
            );
  else
    expr << smt2lib::extract(regSize,
              smt2lib::bvmul(
                smt2lib::sx(op2.str(), regSize * REG_SIZE),
                smt2lib::sx(op3.str(), memSize * REG_SIZE)
              )
            );

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegMem(se, reg, mem, memSize);

  /* Add the symbolic flags element to the current inst */
  EflagsBuilder::cfImul(inst, se, ap, regSize, op1);
  EflagsBuilder::ofImul(inst, se, ap, regSize, op1);
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

