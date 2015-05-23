#include <iostream>
#include <sstream>
#include <stdexcept>

#include "PushIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


PushIRBuilder::PushIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}



static SymbolicElement *alignStack(AnalysisProcessor &ap, uint32_t writeSize)
{
  SymbolicElement     *se;
  std::stringstream   expr, op1, op2;

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(ID_RSP, writeSize);
  op2 << smt2lib::bv(writeSize, writeSize * REG_SIZE);

  expr << smt2lib::bvsub(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_RSP, REG_SIZE, "Aligns stack");

  /* Apply the taint */
  se->isTainted = ap.isRegTainted(ID_RSP);

  return se;
}


void PushIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1;
  uint64_t          reg       = this->operands[0].getValue(); // Reg pushed
  uint64_t          mem       = this->operands[1].getValue(); // The dst memory writing
  uint32_t          writeSize = this->operands[1].getSize();
  uint32_t          regSize   = this->operands[0].getSize();

  /* Create the SMT semantic side effect */
  inst.addElement(alignStack(ap, writeSize));

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(reg, regSize);

  /* Finale expr */
  expr << op1.str();

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemReg(se, mem, reg, writeSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void PushIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1;
  uint64_t          imm       = this->operands[0].getValue(); // Imm pushed
  uint64_t          mem       = this->operands[1].getValue(); // The dst memory writing
  uint32_t          writeSize = this->operands[1].getSize();

  /* Create the SMT semantic side effect */
  inst.addElement(alignStack(ap, writeSize));

  /* Create the SMT semantic */
  /* OP_1 */
  op1 << smt2lib::bv(imm, writeSize * REG_SIZE);

  /* Finale expr */
  expr << op1.str();

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemImm(se, mem, writeSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void PushIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1;
  uint64_t          memOp     = this->operands[0].getValue(); // Mem pushed
  uint32_t          readSize  = this->operands[0].getSize();
  uint64_t          memDst    = this->operands[1].getValue(); // The dst memory writing
  uint32_t          writeSize = this->operands[1].getSize();

  /* Create the SMT semantic side effect */
  inst.addElement(alignStack(ap, writeSize));

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicMemOperand(memOp, readSize);

  /* Finale expr */
  expr << op1.str();

  /* Create the symbolic element */
  se = ap.createMemSE(expr, memDst);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemMem(se, memDst, memOp, readSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void PushIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  /* There is no <push none> available in x86 */
  OneOperandTemplate::stop(this->disas);
}


Inst *PushIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "PUSH");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    inst->addElement(ControlFlow::rip(ap, this->nextAddress));
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

