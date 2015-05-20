#include <iostream>
#include <sstream>
#include <stdexcept>

#include "JmpIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


JmpIRBuilder::JmpIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void JmpIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr;
  uint64_t          imm = this->operands[0].getValue();

  /* Finale expr */
  expr << smt2lib::bv(imm, REG_SIZE_BIT);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_RIP, "RIP");

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void JmpIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1;
  uint64_t          reg     = this->operands[0].getValue();
  uint64_t          symReg  = ap.getRegSymbolicID(reg);
  uint32_t          regSize = this->operands[0].getSize();

  /* Create the SMT semantic */
  /* OP_1 */
  if (symReg != UNSET)
    op1 << smt2lib::extract(regSize, "#" + std::to_string(symReg));
  else
    op1 << smt2lib::bv(ap.getRegisterValue(reg), regSize * REG_SIZE);

  /* Finale expr */
  expr << op1.str();

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_RIP, "RIP");

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void JmpIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1;
  uint64_t          mem     = this->operands[0].getValue();
  uint64_t          symMem  = ap.getMemSymbolicID(mem);
  uint32_t          memSize = this->operands[0].getSize();

  /* Create the SMT semantic */
  /* OP_1 */
  if (symMem != UNSET)
    op1 << "#" << std::dec << symMem;
  else
    op1 << smt2lib::bv(ap.getMemValue(mem, memSize), memSize * REG_SIZE);

  /* Finale expr */
  expr << op1.str();

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_RIP, "RIP");

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void JmpIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


Inst *JmpIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "JMP");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

