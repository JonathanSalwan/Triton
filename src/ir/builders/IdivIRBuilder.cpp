/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <iostream>
#include <sstream>
#include <stdexcept>

#include <IdivIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicExpression.h>


IdivIRBuilder::IdivIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void IdivIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *result, *dividend, *divisor, *mod;
  auto reg = this->operands[0].getReg();
  auto regSize = this->operands[0].getReg().getSize();

  /* Create the SMT semantic */
  divisor = ap.buildSymbolicRegOperand(reg, regSize);

  switch (regSize) {

    case BYTE_SIZE:
      /* AX */
      dividend = ap.buildSymbolicRegOperand(ID_TMP_RAX, WORD_SIZE);
      /* res = AX / Source */
      result = smt2lib::bvsdiv(dividend, smt2lib::sx(BYTE_SIZE_BIT, divisor));
      /* mod = AX % Source */
      mod = smt2lib::bvsrem(dividend, smt2lib::sx(BYTE_SIZE_BIT, divisor));
      /* AH = mod */
      /* AL = res */
      expr = smt2lib::concat(
                smt2lib::extract(7, 0, mod),   /* AH = mod */
                smt2lib::extract(7, 0, result) /* AL = res */
              );
      /* Create the symbolic expression */
      se = ap.createRegSE(inst, expr, ID_TMP_RAX, WORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegReg(se, ID_TMP_RAX, reg);
      break;

    case WORD_SIZE:
      /* DX:AX */
      dividend = smt2lib::concat(ap.buildSymbolicRegOperand(ID_TMP_RDX, WORD_SIZE), ap.buildSymbolicRegOperand(ID_TMP_RAX, WORD_SIZE));
      /* res = DX:AX / Source */
      result = smt2lib::extract(15, 0, smt2lib::bvsdiv(dividend, smt2lib::sx(WORD_SIZE_BIT, divisor)));
      /* mod = DX:AX % Source */
      mod = smt2lib::extract(15, 0, smt2lib::bvsrem(dividend, smt2lib::sx(WORD_SIZE_BIT, divisor)));
      /* Create the symbolic expression for AX */
      se = ap.createRegSE(inst, result, ID_TMP_RAX, WORD_SIZE);
      /* Apply the taint for AX */
      ap.aluSpreadTaintRegReg(se, ID_TMP_RAX, reg);
      /* Create the symbolic expression for DX */
      se = ap.createRegSE(inst, mod, ID_TMP_RDX, WORD_SIZE);
      /* Apply the taint for DX */
      ap.aluSpreadTaintRegReg(se, ID_TMP_RDX, reg);
      break;

    case DWORD_SIZE:
      /* EDX:EAX */
      dividend = smt2lib::concat(ap.buildSymbolicRegOperand(ID_TMP_RDX, DWORD_SIZE), ap.buildSymbolicRegOperand(ID_TMP_RAX, DWORD_SIZE));
      /* res = EDX:EAX / Source */
      result = smt2lib::extract(31, 0, smt2lib::bvsdiv(dividend, smt2lib::sx(DWORD_SIZE_BIT, divisor)));
      /* mod = EDX:EAX % Source */
      mod = smt2lib::extract(31, 0, smt2lib::bvsrem(dividend, smt2lib::sx(DWORD_SIZE_BIT, divisor)));
      /* Create the symbolic expression for EAX */
      se = ap.createRegSE(inst, result, ID_TMP_RAX, DWORD_SIZE);
      /* Apply the taint for EAX */
      ap.aluSpreadTaintRegReg(se, ID_TMP_RAX, reg);
      /* Create the symbolic expression for EDX */
      se = ap.createRegSE(inst, mod, ID_TMP_RDX, DWORD_SIZE);
      /* Apply the taint for EDX */
      ap.aluSpreadTaintRegReg(se, ID_TMP_RDX, reg);
      break;

    case QWORD_SIZE:
      /* RDX:RAX */
      dividend = smt2lib::concat(ap.buildSymbolicRegOperand(ID_TMP_RDX, QWORD_SIZE), ap.buildSymbolicRegOperand(ID_TMP_RAX, QWORD_SIZE));
      /* res = RDX:RAX / Source */
      result = smt2lib::extract(63, 0, smt2lib::bvsdiv(dividend, smt2lib::sx(QWORD_SIZE_BIT, divisor)));
      /* mod = RDX:RAX % Source */
      mod = smt2lib::extract(63, 0, smt2lib::bvsrem(dividend, smt2lib::sx(QWORD_SIZE_BIT, divisor)));
      /* Create the symbolic expression for RAX */
      se = ap.createRegSE(inst, result, ID_TMP_RAX, QWORD_SIZE);
      /* Apply the taint for RAX */
      ap.aluSpreadTaintRegReg(se, ID_TMP_RAX, reg);
      /* Create the symbolic expression for RDX */
      se = ap.createRegSE(inst, mod, ID_TMP_RDX, QWORD_SIZE);
      /* Apply the taint for RDX */
      ap.aluSpreadTaintRegReg(se, ID_TMP_RDX, reg);
      break;
  }
}


void IdivIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr, *result, *dividend, *divisor, *mod;
  auto mem = this->operands[0].getMem();
  auto memSize = this->operands[0].getMem().getSize();

  /* Create the SMT semantic */
  divisor = ap.buildSymbolicMemOperand(mem, memSize);

  switch (memSize) {

    case BYTE_SIZE:
      /* AX */
      dividend = ap.buildSymbolicRegOperand(ID_TMP_RAX, WORD_SIZE);
      /* res = AX / Source */
      result = smt2lib::bvsdiv(dividend, smt2lib::sx(BYTE_SIZE_BIT, divisor));
      /* mod = AX % Source */
      mod = smt2lib::bvsrem(dividend, smt2lib::sx(BYTE_SIZE_BIT, divisor));
      /* AH = mod */
      /* AL = res */
      expr = smt2lib::concat(
                smt2lib::extract(7, 0, mod),   /* AH = mod */
                smt2lib::extract(7, 0, result) /* AL = res */
              );
      /* Create the symbolic expression */
      se = ap.createRegSE(inst, expr, ID_TMP_RAX, WORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegMem(se, ID_TMP_RAX, mem, memSize);
      break;

    case WORD_SIZE:
      /* DX:AX */
      dividend = smt2lib::concat(ap.buildSymbolicRegOperand(ID_TMP_RDX, WORD_SIZE), ap.buildSymbolicRegOperand(ID_TMP_RAX, WORD_SIZE));
      /* res = DX:AX / Source */
      result = smt2lib::extract(15, 0, smt2lib::bvsdiv(dividend, smt2lib::sx(WORD_SIZE_BIT, divisor)));
      /* mod = DX:AX % Source */
      mod = smt2lib::extract(15, 0, smt2lib::bvsrem(dividend, smt2lib::sx(WORD_SIZE_BIT, divisor)));
      /* Create the symbolic expression for AX */
      se = ap.createRegSE(inst, result, ID_TMP_RAX, WORD_SIZE);
      /* Apply the taint for AX */
      ap.aluSpreadTaintRegMem(se, ID_TMP_RAX, mem, memSize);
      /* Create the symbolic expression for DX */
      se = ap.createRegSE(inst, mod, ID_TMP_RDX, WORD_SIZE);
      /* Apply the taint for DX */
      ap.aluSpreadTaintRegMem(se, ID_TMP_RDX, mem, memSize);
      break;

    case DWORD_SIZE:
      /* EDX:EAX */
      dividend = smt2lib::concat(ap.buildSymbolicRegOperand(ID_TMP_RDX, DWORD_SIZE), ap.buildSymbolicRegOperand(ID_TMP_RAX, DWORD_SIZE));
      /* res = EDX:EAX / Source */
      result = smt2lib::extract(31, 0, smt2lib::bvsdiv(dividend, smt2lib::sx(DWORD_SIZE_BIT, divisor)));
      /* mod = EDX:EAX % Source */
      mod = smt2lib::extract(31, 0, smt2lib::bvsrem(dividend, smt2lib::sx(DWORD_SIZE_BIT, divisor)));
      /* Create the symbolic expression for EAX */
      se = ap.createRegSE(inst, result, ID_TMP_RAX, DWORD_SIZE);
      /* Apply the taint for EAX */
      ap.aluSpreadTaintRegMem(se, ID_TMP_RAX, mem, memSize);
      /* Create the symbolic expression for EDX */
      se = ap.createRegSE(inst, mod, ID_TMP_RDX, DWORD_SIZE);
      /* Apply the taint for EDX */
      ap.aluSpreadTaintRegMem(se, ID_TMP_RDX, mem, memSize);
      break;

    case QWORD_SIZE:
      /* RDX:RAX */
      dividend = smt2lib::concat(ap.buildSymbolicRegOperand(ID_TMP_RDX, QWORD_SIZE), ap.buildSymbolicRegOperand(ID_TMP_RAX, QWORD_SIZE));
      /* res = RDX:RAX / Source */
      result = smt2lib::extract(63, 0, smt2lib::bvsdiv(dividend, smt2lib::sx(QWORD_SIZE_BIT, divisor)));
      /* mod = RDX:RAX % Source */
      mod = smt2lib::extract(63, 0, smt2lib::bvsrem(dividend, smt2lib::sx(QWORD_SIZE_BIT, divisor)));
      /* Create the symbolic expression for RAX */
      se = ap.createRegSE(inst, result, ID_TMP_RAX, QWORD_SIZE);
      /* Apply the taint for RAX */
      ap.aluSpreadTaintRegMem(se, ID_TMP_RAX, mem, memSize);
      /* Create the symbolic expression for RDX */
      se = ap.createRegSE(inst, mod, ID_TMP_RDX, QWORD_SIZE);
      /* Apply the taint for RDX */
      ap.aluSpreadTaintRegMem(se, ID_TMP_RDX, mem, memSize);
      break;
  }
}


void IdivIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  /* There is no <inc imm> available in x86 */
  OneOperandTemplate::stop(this->disas);
}


void IdivIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  /* There is no <inc none> available in x86 */
  OneOperandTemplate::stop(this->disas);
}


Inst *IdivIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "IDIV");
    ap.incNumberOfExpressions(inst->numberOfExpressions()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

#endif /* LIGHT_VERSION */

