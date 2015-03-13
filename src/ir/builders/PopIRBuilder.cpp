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


static void stop(std::string disass)
{
  throw std::runtime_error("Error:"
                         + disass
                         + "is an invalid instruction. Wrong kind of operands.");
}


static SymbolicElement *alignStack(AnalysisProcessor &ap, const ContextHandler &ctxH, uint32_t readSize)
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
    op1 << smt2lib::bv(ctxH.getRegisterValue(REG_RSP), readSize * REG_SIZE);

  op2 << smt2lib::bv(readSize, readSize * REG_SIZE);

  expr << smt2lib::bvadd(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_RSP);

  /* Apply the taint */
  se->isTainted = ap.isRegTainted(ID_RSP);

  return se;
}


void PopIRBuilder::reg(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1;
  uint64_t          reg       = std::get<1>(this->operands[0]); // Reg poped
  uint64_t          mem       = std::get<1>(this->operands[1]); // The src memory read
  uint32_t          readSize  = std::get<2>(this->operands[1]);
  uint64_t          symMem    = ap.getMemorySymbolicID(mem);

  /* Create the SMT semantic side effect */
  inst.addElement(alignStack(ap, ctxH, readSize));

  /* Create the SMT semantic */
  /* OP_1 */
  if (symMem != UNSET)
    op1 << "#" << std::dec << symMem;
  else
    op1 << smt2lib::bv(ctxH.getMemoryValue(mem, readSize), readSize * REG_SIZE);

  /* Finale expr */
  expr << op1.str();

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ctxH.translateRegID(reg));

  /* Apply the taint */
  ap.assignmentSpreadTaintMemReg(se, mem, ctxH.translateRegID(reg), readSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void PopIRBuilder::mem(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1;
  uint64_t          memOp     = std::get<1>(this->operands[0]); // Mem poped
  uint32_t          writeSize = std::get<2>(this->operands[0]);
  uint64_t          memSrc    = std::get<1>(this->operands[1]); // The dst memory read
  uint32_t          readSize  = std::get<2>(this->operands[1]);
  uint64_t          symMem    = ap.getMemorySymbolicID(memSrc);

  /* Create the SMT semantic side effect */
  inst.addElement(alignStack(ap, ctxH, writeSize));

  /* Create the SMT semantic */
  /* OP_1 */
  if (symMem != UNSET)
    op1 << "#" << std::dec << symMem;
  else
    op1 << smt2lib::bv(ctxH.getMemoryValue(memSrc, readSize), readSize * REG_SIZE);

  /* Finale expr */
  expr << op1.str();

  /* Create the symbolic element */
  se = ap.createMemSE(expr, memOp);

  /* Apply the taint */
  ap.assignmentSpreadTaintMemMem(se, memOp, memSrc, readSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void PopIRBuilder::imm(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const {
  /* There is no <pop imm> available in x86 */
  stop(this->disas);
}


Inst *PopIRBuilder::process(const ContextHandler &ctxH, AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ctxH.getThreadId(), this->address, this->disas);

  try {
    this->templateMethod(ctxH, ap, *inst, this->operands, "POP");
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

