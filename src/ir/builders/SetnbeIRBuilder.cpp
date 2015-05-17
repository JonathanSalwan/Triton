#include <iostream>
#include <sstream>
#include <stdexcept>

#include "SetnbeIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


SetnbeIRBuilder::SetnbeIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void SetnbeIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


void SetnbeIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, reg1e, cf, zf;
  uint64_t          reg     = std::get<1>(this->operands[0]);
  uint64_t          regSize = std::get<2>(this->operands[0]);
  uint64_t          symReg  = ap.getRegSymbolicID(reg);
  uint64_t          symCF   = ap.getRegSymbolicID(ID_CF);
  uint64_t          symZF   = ap.getRegSymbolicID(ID_ZF);

  /* Create the SMT semantic */
  if (symCF != UNSET)
    cf << "#" << std::dec << symCF;
  else
    cf << smt2lib::bv(ap.getFlagValue(ID_CF), 1);

  /* Create the SMT semantic */
  if (symZF != UNSET)
    zf << "#" << std::dec << symZF;
  else
    zf << smt2lib::bv(ap.getFlagValue(ID_ZF), 1);

  /* Create the reg1 SMT semantic */
  if (symReg != UNSET)
    reg1e << smt2lib::extract(regSize, "#" + std::to_string(symReg));
  else
    reg1e << smt2lib::bv(ap.getRegisterValue(reg), regSize * REG_SIZE);

  /* Finale expr */
  expr << smt2lib::ite(
            smt2lib::equal(
              smt2lib::bvand(
                smt2lib::bvnot(cf.str()),
                smt2lib::bvnot(zf.str())
              ),
              smt2lib::bvtrue()),
            smt2lib::bv(1, 8),
            smt2lib::bv(0, 8));

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg);

  /* Apply the taint via the concretization */
  if (ap.getFlagValue(ID_CF) == 0 && ap.getFlagValue(ID_ZF) == 0) {
    if (ap.isRegTainted(ID_CF) == TAINTED)
      ap.assignmentSpreadTaintRegReg(se, reg, ID_CF);
    else
      ap.assignmentSpreadTaintRegReg(se, reg, ID_ZF);
  }

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void SetnbeIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, mem1e, cf, zf;
  uint64_t          mem     = std::get<1>(this->operands[0]);
  uint64_t          memSize = std::get<2>(this->operands[0]);
  uint64_t          symMem  = ap.getMemSymbolicID(mem);
  uint64_t          symCF   = ap.getRegSymbolicID(ID_CF);
  uint64_t          symZF   = ap.getRegSymbolicID(ID_ZF);

  /* Create the SMT semantic */
  if (symCF != UNSET)
    cf << "#" << std::dec << symCF;
  else
    cf << smt2lib::bv(ap.getFlagValue(ID_CF), 1);

  /* Create the SMT semantic */
  if (symZF != UNSET)
    zf << "#" << std::dec << symZF;
  else
    zf << smt2lib::bv(ap.getFlagValue(ID_ZF), 1);

  /* Create the reg1 SMT semantic */
  if (symMem != UNSET)
    mem1e << smt2lib::extract(memSize, "#" + std::to_string(symMem));
  else
    mem1e << smt2lib::bv(ap.getMemValue(mem, memSize), memSize * REG_SIZE);

  /* Finale expr */
  expr << smt2lib::ite(
            smt2lib::equal(
              smt2lib::bvand(
                smt2lib::bvnot(cf.str()),
                smt2lib::bvnot(zf.str())
              ),
              smt2lib::bvtrue()),
            smt2lib::bv(1, 8),
            smt2lib::bv(0, 8));

  /* Create the symbolic element */
  se = ap.createMemSE(expr, mem);

  /* Apply the taint via the concretization */
  if (ap.getFlagValue(ID_CF) == 0 && ap.getFlagValue(ID_ZF) == 0) {
    if (ap.isRegTainted(ID_CF) == TAINTED)
      ap.assignmentSpreadTaintMemReg(se, mem, ID_CF, memSize);
    else
      ap.assignmentSpreadTaintMemReg(se, mem, ID_ZF, memSize);
  }

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void SetnbeIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


Inst *SetnbeIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "SETNBE");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

