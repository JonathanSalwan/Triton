#include <iostream>
#include <sstream>
#include <stdexcept>

#include "JbeIRBuilder.h"
#include "Registers.h"
#include "SMT2Lib.h"
#include "SymbolicElement.h"


JbeIRBuilder::JbeIRBuilder(uint64_t address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void JbeIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2;
  uint64_t          imm   = std::get<1>(this->operands[0]);
  uint64_t          symCF = ap.getRegSymbolicID(ID_CF);
  uint64_t          symZF = ap.getRegSymbolicID(ID_ZF);

  /* Create the SMT semantic */
  if (symCF != UNSET)
    op1 << "#" << std::dec << symCF;
  else
    op1 << smt2lib::bv(ap.getRegisterValue(ID_CF), 1);

  if (symZF != UNSET)
    op2 << "#" << std::dec << symZF;
  else
    op2 << smt2lib::bv(ap.getRegisterValue(ID_ZF), 1);

  /* 
   * Finale expr
   * JNBE: Jump if below or equal (CF=1 and ZF=1).
   * SMT: (= (bvand zf cf) (_ bv1 1))
   */
  expr << smt2lib::ite(
            smt2lib::equal(
              smt2lib::bvand(
                op1.str(),
                op2.str()
              ),
              smt2lib::bvtrue()
            ),
            smt2lib::bv(imm, REG_SIZE_BIT),
            smt2lib::bv(this->nextAddress, REG_SIZE_BIT));

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_RIP, "RIP");

  /* Add the constraint in the PathConstraints list */
  ap.addPathConstraint(se->getID());

  /* Add the symbolic element to the current inst */
  inst.addElement(se);
}


void JbeIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


void JbeIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


void JbeIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  OneOperandTemplate::stop(this->disas);
}


Inst *JbeIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "JBE");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

