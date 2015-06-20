#include <iostream>
#include <sstream>
#include <stdexcept>

#include <SarIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicElement.h>


SarIRBuilder::SarIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void SarIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint64            reg     = this->operands[0].getValue();
  uint64            imm     = this->operands[1].getValue();
  uint32            regSize = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(reg, regSize);
  op2 << smt2lib::bv(imm, regSize * REG_SIZE);

  /* Finale expr */
  expr << smt2lib::bvashr(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, reg, reg);

  /* Add the symbolic flags element to the current inst */
  EflagsBuilder::cfSar(inst, se, ap, regSize, op1, op2);
  EflagsBuilder::ofSar(inst, se, ap, regSize, op2);
  EflagsBuilder::pfShl(inst, se, ap, regSize, op2); /* Same that shl */
  EflagsBuilder::sfShl(inst, se, ap, regSize, op2); /* Same that shl */
  EflagsBuilder::zfShl(inst, se, ap, regSize, op2); /* Same that shl */
}


void SarIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint64            reg     = this->operands[0].getValue();
  uint32            regSize = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(reg, regSize);
  op2 << smt2lib::zx(ap.buildSymbolicRegOperand(ID_RCX, 1), (regSize - 1) * REG_SIZE);

  /* Finale expr */
  expr << smt2lib::bvashr(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, reg, regSize);

  /* Apply the taint */
  ap.aluSpreadTaintRegReg(se, reg, reg);

  /* Add the symbolic flags element to the current inst */
  EflagsBuilder::cfSar(inst, se, ap, regSize, op1, op2);
  EflagsBuilder::ofSar(inst, se, ap, regSize, op2);
  EflagsBuilder::pfShl(inst, se, ap, regSize, op2); /* Same that shl */
  EflagsBuilder::sfShl(inst, se, ap, regSize, op2); /* Same that shl */
  EflagsBuilder::zfShl(inst, se, ap, regSize, op2); /* Same that shl */
}


void SarIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void SarIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint32            writeSize = this->operands[0].getSize();
  uint64            mem       = this->operands[0].getValue();
  uint64            imm       = this->operands[1].getValue();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicMemOperand(mem, writeSize);
  op2 << smt2lib::bv(imm, writeSize * REG_SIZE);

  /* Final expr */
  expr << smt2lib::bvashr(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createMemSE(inst, expr, mem, writeSize);

  /* Apply the taint */
  ap.aluSpreadTaintMemMem(se, mem, mem, writeSize);

  /* Add the symbolic flags element to the current inst */
  EflagsBuilder::cfSar(inst, se, ap, writeSize, op1, op2);
  EflagsBuilder::ofSar(inst, se, ap, writeSize, op2);
  EflagsBuilder::pfShl(inst, se, ap, writeSize, op2); /* Same that shl */
  EflagsBuilder::sfShl(inst, se, ap, writeSize, op2); /* Same that shl */
  EflagsBuilder::zfShl(inst, se, ap, writeSize, op2); /* Same that shl */
}


void SarIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


Inst *SarIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "SAR");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

