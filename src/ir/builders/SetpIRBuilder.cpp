#include <iostream>
#include <sstream>
#include <stdexcept>

#include "SetpIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


SetpIRBuilder::SetpIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void SetpIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


void SetpIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, reg1e, pf;
  uint64_t          reg     = std::get<1>(this->operands[0]);
  uint64_t          regSize = std::get<2>(this->operands[0]);
  uint64_t          symReg  = ap.getRegSymbolicID(reg);
  uint64_t          symPF   = ap.getRegSymbolicID(ID_PF);

  /* Create the SMT semantic */
  if (symPF != UNSET)
    pf << "#" << std::dec << symPF;
  else
    pf << smt2lib::bv(ap.getFlagValue(ID_PF), 1);

  /* Create the reg1 SMT semantic */
  if (symReg != UNSET)
    reg1e << smt2lib::extract(regSize, "#" + std::to_string(symReg));
  else
    reg1e << smt2lib::bv(ap.getRegisterValue(reg), regSize * REG_SIZE);

  /* Finale expr */
  expr << smt2lib::ite(
            smt2lib::equal(
              pf.str(),
              smt2lib::bvtrue()),
            smt2lib::bv(1, 8),
            smt2lib::bv(0, 8));

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void SetpIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, mem1e, pf;
  uint64_t          mem     = std::get<1>(this->operands[0]);
  uint64_t          memSize = std::get<2>(this->operands[0]);
  uint64_t          symMem  = ap.getMemSymbolicID(mem);
  uint64_t          symPF   = ap.getRegSymbolicID(ID_PF);

  /* Create the SMT semantic */
  if (symPF != UNSET)
    pf << "#" << std::dec << symPF;
  else
    pf << smt2lib::bv(ap.getFlagValue(ID_PF), 1);

  /* Create the reg1 SMT semantic */
  if (symMem != UNSET)
    mem1e << smt2lib::extract(memSize, "#" + std::to_string(symMem));
  else
    mem1e << smt2lib::bv(ap.getMemValue(mem, memSize), memSize * REG_SIZE);

  /* Finale expr */
  expr << smt2lib::ite(
            smt2lib::equal(
              pf.str(),
              smt2lib::bvtrue()),
            smt2lib::bv(1, 8),
            smt2lib::bv(0, 8));

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void SetpIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


Inst *SetpIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "SETP");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

