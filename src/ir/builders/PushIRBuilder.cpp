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
  uint64_t            symReg = ap.getRegSymbolicID(ID_RSP);

  /*
   * Create the SMT semantic.
   */
  if (symReg != UNSET)
    op1 << "#" << std::dec << symReg;
  else
    op1 << smt2lib::bv(ap.getRegisterValue(REG_RSP), writeSize * REG_SIZE);

  op2 << smt2lib::bv(writeSize, writeSize * REG_SIZE);

  expr << smt2lib::bvsub(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_RSP);

  /* Apply the taint */
  se->isTainted = ap.isRegTainted(ID_RSP);

  return se;
}


void PushIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1;
  uint64_t          reg       = std::get<1>(this->operands[0]); // Reg pushed
  uint64_t          mem       = std::get<1>(this->operands[1]); // The dst memory writing
  uint32_t          writeSize = std::get<2>(this->operands[1]);

  uint64_t          symReg    = ap.getRegSymbolicID(ap.translateRegID(reg));
  uint32_t          regSize   = ap.getRegisterSize(reg);

  /* Create the SMT semantic side effect */
  inst.addElement(alignStack(ap, writeSize));

  /* Create the SMT semantic */
  /* OP_1 */
  if (symReg != UNSET)
    op1 << "#" << std::dec << symReg;
  else
    op1 << smt2lib::bv(ap.getRegisterValue(reg), regSize * REG_SIZE);

  /* Finale expr */
  expr << op1.str();

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemReg(se, mem, ap.translateRegID(reg), writeSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void PushIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1;
  uint64_t          imm       = std::get<1>(this->operands[0]); // Imm pushed
  uint64_t          mem       = std::get<1>(this->operands[1]); // The dst memory writing
  uint32_t          writeSize = std::get<2>(this->operands[1]);

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
  uint64_t          memOp     = std::get<1>(this->operands[0]); // Mem pushed
  uint32_t          readSize  = std::get<2>(this->operands[0]);
  uint64_t          memDst    = std::get<1>(this->operands[1]); // The dst memory writing
  uint32_t          writeSize = std::get<2>(this->operands[1]);
  uint64_t          symMem    = ap.getMemSymbolicID(memOp);

  /* Create the SMT semantic side effect */
  inst.addElement(alignStack(ap, writeSize));

  /* Create the SMT semantic */
  /* OP_1 */
  if (symMem != UNSET)
    op1 << "#" << std::dec << symMem;
  else
    op1 << smt2lib::bv(ap.getMemoryValue(memOp, readSize), readSize * REG_SIZE);

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

  Inst *inst = new Inst(ap.getThreadId(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "PUSH");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

