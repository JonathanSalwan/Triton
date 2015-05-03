#include <iostream>
#include <sstream>
#include <stdexcept>

#include "RetIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


RetIRBuilder::RetIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


static SymbolicElement *alignStack(AnalysisProcessor &ap)
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
    op1 << smt2lib::bv(ap.getRegisterValue(ID_RSP), 8 * REG_SIZE);

  op2 << smt2lib::bv(REG_SIZE, 8 * REG_SIZE);

  expr << smt2lib::bvadd(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_RSP, "Aligns stack");

  /* Apply the taint */
  se->isTainted = ap.isRegTainted(ID_RSP);

  return se;
}


static SymbolicElement *alignStack(AnalysisProcessor &ap, uint64_t imm)
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
    op1 << smt2lib::bv(ap.getRegisterValue(ID_RSP), 8 * REG_SIZE);

  op2 << smt2lib::bv(imm, 8 * REG_SIZE);

  expr << smt2lib::bvadd(op1.str(), op2.str());

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_RSP, "Aligns stack");

  /* Apply the taint */
  se->isTainted = ap.isRegTainted(ID_RSP);

  return se;
}


void RetIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  /* There is no 'ret reg' in x86 */
  OneOperandTemplate::stop(this->disas);
}


void RetIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1;
  uint64_t          imm       = std::get<1>(this->operands[0]);
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
  se = ap.createRegSE(expr, ID_RIP, "RIP");

  /* Apply the taint */
  ap.assignmentSpreadTaintRegMem(se, ID_RIP, memSrc, readSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);

  /* Create the SMT semantic side effect */
  inst.addElement(alignStack(ap, imm));
}


void RetIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1;
  uint64_t          memSrc    = std::get<1>(this->operands[0]); // The dst memory read
  uint32_t          readSize  = std::get<2>(this->operands[0]);
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
  se = ap.createRegSE(expr, ID_RIP, "RIP");

  /* Apply the taint */
  ap.assignmentSpreadTaintRegMem(se, ID_RIP, memSrc, readSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);

  /* Create the SMT semantic side effect */
  inst.addElement(alignStack(ap));
}


void RetIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  /* The ret instruction without argument is in the RetIRBuilder::mem function. */
  /* As ret has an implicit read memory (saved EIP), it contains at least one memory argument. */
  OneOperandTemplate::stop(this->disas);
}


Inst *RetIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "RET");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

