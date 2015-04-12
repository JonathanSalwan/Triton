#include <iostream>
#include <sstream>
#include <stdexcept>

#include "PopIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


PopIRBuilder::PopIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


static SymbolicElement *alignStack(AnalysisProcessor &ap, uint32_t readSize)
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
    op1 << smt2lib::bv(ap.getRegisterValue(ID_RSP), readSize * REG_SIZE);

  op2 << smt2lib::bv(readSize, readSize * REG_SIZE);

  expr << smt2lib::bvadd(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_RSP);

  /* Apply the taint */
  se->isTainted = ap.isRegTainted(ID_RSP);

  return se;
}


void PopIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1;
  uint64_t          reg       = std::get<1>(this->operands[0]); // Reg poped
  uint64_t          mem       = std::get<1>(this->operands[1]); // The src memory read
  uint32_t          readSize  = std::get<2>(this->operands[1]);
  uint64_t          symMem    = ap.getMemSymbolicID(mem);

  /* Create the SMT semantic */
  /* OP_1 */
  if (symMem != UNSET)
    op1 << "#" << std::dec << symMem;
  else
    op1 << smt2lib::bv(ap.getMemValue(mem, readSize), readSize * REG_SIZE);

  /* Finale expr */
  expr << op1.str();

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemReg(se, mem, reg, readSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);

  /* Create the SMT semantic side effect */
  inst.addElement(alignStack(ap, readSize));
}


void PopIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1;
  uint64_t          memOp     = std::get<1>(this->operands[0]); // Mem poped
  uint32_t          writeSize = std::get<2>(this->operands[0]);
  uint64_t          memSrc    = std::get<1>(this->operands[1]); // The dst memory read
  uint32_t          readSize  = std::get<2>(this->operands[1]);
  uint64_t          symMem    = ap.getMemSymbolicID(memSrc);

  /* Create the SMT semantic */
  /* OP_1 */
  if (symMem != UNSET)
    op1 << "#" << std::dec << symMem;
  else
    op1 << smt2lib::bv(ap.getMemValue(memSrc, readSize), readSize * REG_SIZE);

  /* Finale expr */
  expr << op1.str();

  /* Create the symbolic element */
  se = ap.createMemSE(expr, memOp);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemMem(se, memOp, memSrc, readSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);

  /* Create the SMT semantic side effect */
  inst.addElement(alignStack(ap, writeSize));
}


void PopIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  /* There is no <pop imm> available in x86 */
  OneOperandTemplate::stop(this->disas);
}


void PopIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  /* There is no <pop none> available in x86 */
  OneOperandTemplate::stop(this->disas);
}


Inst *PopIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "POP");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

