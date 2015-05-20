#include <algorithm>
#include <sstream>
#include <stdexcept>

#include "CmovsIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


CmovsIRBuilder::CmovsIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly){
}


void CmovsIRBuilder::regImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void CmovsIRBuilder::regReg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, reg1e, reg2e, sf;
  uint64_t          reg1    = this->operands[0].getValue();
  uint64_t          reg2    = this->operands[1].getValue();
  uint64_t          size1   = this->operands[0].getSize();
  uint64_t          size2   = this->operands[1].getSize();
  uint64_t          symReg1 = ap.getRegSymbolicID(reg1);
  uint64_t          symReg2 = ap.getRegSymbolicID(reg2);
  uint64_t          symSF   = ap.getRegSymbolicID(ID_SF);

  /* Create the SMT semantic */
  if (symSF != UNSET)
    sf << "#" << std::dec << symSF;
  else
    sf << smt2lib::bv(ap.getFlagValue(ID_SF), 1);

  /* Create the reg1 SMT semantic */
  if (symReg1 != UNSET)
    reg1e << smt2lib::extract(size1, "#" + std::to_string(symReg1));
  else
    reg1e << smt2lib::bv(ap.getRegisterValue(reg1), size1 * REG_SIZE);

  /* Create the reg2 SMT semantic */
  if (symReg2 != UNSET)
    reg2e << smt2lib::extract(size2, "#" + std::to_string(symReg2));
  else
    reg2e << smt2lib::bv(ap.getRegisterValue(reg2), size2 * REG_SIZE);

  expr << smt2lib::ite(
            smt2lib::equal(
              sf.str(),
              smt2lib::bvtrue()),
            reg2e.str(),
            reg1e.str());

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg1);

  /* Apply the taint via the concretization */
  if (ap.getFlagValue(ID_SF) == 1)
    ap.assignmentSpreadTaintRegReg(se, reg1, reg2);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void CmovsIRBuilder::regMem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, reg1e, mem1e, sf;
  uint32_t          readSize = this->operands[1].getSize();
  uint64_t          mem      = this->operands[1].getValue();
  uint64_t          reg      = this->operands[0].getValue();
  uint64_t          regSize  = this->operands[0].getSize();
  uint64_t          symReg   = ap.getRegSymbolicID(reg);
  uint64_t          symMem   = ap.getMemSymbolicID(mem);
  uint64_t          symSF    = ap.getRegSymbolicID(ID_SF);

  /* Create the SMT semantic */
  if (symSF != UNSET)
    sf << "#" << std::dec << symSF;
  else
    sf << smt2lib::bv(ap.getFlagValue(ID_SF), 1);

  /* Create the reg SMT semantic */
  if (symReg != UNSET)
    reg1e << smt2lib::extract(regSize, "#" + std::to_string(symReg));
  else
    reg1e << smt2lib::bv(ap.getRegisterValue(reg), regSize * REG_SIZE);

  /* Create the memory SMT semantic */
  if (symMem != UNSET)
    mem1e << smt2lib::extract(readSize, "#" + std::to_string(symMem));
  else
    mem1e << smt2lib::bv(ap.getMemValue(mem, readSize), readSize * REG_SIZE);

  expr << smt2lib::ite(
            smt2lib::equal(
              sf.str(),
              smt2lib::bvtrue()),
            mem1e.str(),
            reg1e.str());

  /* Create the symbolic element */
  se = ap.createRegSE(expr, reg);

  /* Apply the taint via the concretization */
  if (ap.getFlagValue(ID_SF) == 1)
    ap.assignmentSpreadTaintRegMem(se, reg, mem, readSize);

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void CmovsIRBuilder::memImm(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


void CmovsIRBuilder::memReg(AnalysisProcessor &ap, Inst &inst) const {
  TwoOperandsTemplate::stop(this->disas);
}


Inst *CmovsIRBuilder::process(AnalysisProcessor &ap) const {
  checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "CMOVS");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    inst->addElement(ControlFlow::rip(ap, this->nextAddress));
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

