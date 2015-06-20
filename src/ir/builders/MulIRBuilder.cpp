#include <iostream>
#include <sstream>
#include <stdexcept>

#include <MulIRBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>
#include <SymbolicElement.h>


MulIRBuilder::MulIRBuilder(uint64 address, const std::string &disassembly):
  BaseIRBuilder(address, disassembly) {
}


void MulIRBuilder::reg(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2, rax, rdx;
  uint64            reg       = this->operands[0].getValue();
  uint32            regSize   = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(ID_RAX, regSize);
  op2 << ap.buildSymbolicRegOperand(reg, regSize);

  switch (regSize) {

    /* AX = AL * r/m8 */
    case BYTE_SIZE:
      /* Final expr */
      expr << smt2lib::bvmul(
                smt2lib::zx(op1.str(), BYTE_SIZE_BIT),
                smt2lib::zx(op2.str(), BYTE_SIZE_BIT)
              );
      /* Create the symbolic element */
      se = ap.createRegSE(inst, expr, ID_RAX, WORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegReg(se, ID_RAX, reg);
      /* Add the symbolic flags element to the current inst */
      rax << smt2lib::extract(15, 8, expr.str());
      EflagsBuilder::cfMul(inst, se, ap, regSize, rax);
      EflagsBuilder::ofMul(inst, se, ap, regSize, rax);
      break;

    /* DX:AX = AX * r/m16 */
    case WORD_SIZE:
      /* Final expr */
      expr << smt2lib::bvmul(
                smt2lib::zx(op1.str(), WORD_SIZE_BIT),
                smt2lib::zx(op2.str(), WORD_SIZE_BIT)
              );
      rax << smt2lib::extract(15, 0, expr.str());
      rdx << smt2lib::extract(31, 16, expr.str());
      /* Create the symbolic element for AX */
      se = ap.createRegSE(inst, rax, ID_RAX, WORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegReg(se, ID_RAX, reg);
      /* Create the symbolic element for DX */
      se = ap.createRegSE(inst, rdx, ID_RDX, WORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegReg(se, ID_RDX, reg);
      /* Add the symbolic flags element to the current inst */
      EflagsBuilder::cfMul(inst, se, ap, regSize, rdx);
      EflagsBuilder::ofMul(inst, se, ap, regSize, rdx);
      break;

    /* EDX:EAX = EAX * r/m32 */
    case DWORD_SIZE:
      /* Final expr */
      expr << smt2lib::bvmul(
                smt2lib::zx(op1.str(), DWORD_SIZE_BIT),
                smt2lib::zx(op2.str(), DWORD_SIZE_BIT)
              );
      rax << smt2lib::extract(31, 0, expr.str());
      rdx << smt2lib::extract(63, 32, expr.str());
      /* Create the symbolic element for EAX */
      se = ap.createRegSE(inst, rax, ID_RAX, DWORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegReg(se, ID_RAX, reg);
      /* Create the symbolic element for EDX */
      se = ap.createRegSE(inst, rdx, ID_RDX, DWORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegReg(se, ID_RDX, reg);
      /* Add the symbolic flags element to the current inst */
      EflagsBuilder::cfMul(inst, se, ap, regSize, rdx);
      EflagsBuilder::ofMul(inst, se, ap, regSize, rdx);
      break;

    /* RDX:RAX = RAX * r/m64 */
    case QWORD_SIZE:
      /* Final expr */
      expr << smt2lib::bvmul(
                smt2lib::zx(op1.str(), QWORD_SIZE_BIT),
                smt2lib::zx(op2.str(), QWORD_SIZE_BIT)
              );
      rax << smt2lib::extract(63, 0, expr.str());
      rdx << smt2lib::extract(127, 64, expr.str());
      /* Create the symbolic element for RAX */
      se = ap.createRegSE(inst, rax, ID_RAX, QWORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegReg(se, ID_RAX, reg);
      /* Create the symbolic element for RDX */
      se = ap.createRegSE(inst, rdx, ID_RDX, QWORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegReg(se, ID_RDX, reg);
      /* Add the symbolic flags element to the current inst */
      EflagsBuilder::cfMul(inst, se, ap, regSize, rdx);
      EflagsBuilder::ofMul(inst, se, ap, regSize, rdx);
      break;

  }

}


void MulIRBuilder::mem(AnalysisProcessor &ap, Inst &inst) const {
  SymbolicElement   *se;
  std::stringstream expr, op1, op2, rax, rdx;
  uint64            mem       = this->operands[0].getValue();
  uint32            memSize   = this->operands[0].getSize();

  /* Create the SMT semantic */
  op1 << ap.buildSymbolicRegOperand(ID_RAX, memSize);
  op2 << ap.buildSymbolicMemOperand(mem, memSize);

  switch (memSize) {

    /* AX = AL * r/m8 */
    case BYTE_SIZE:
      /* Final expr */
      expr << smt2lib::bvmul(
                smt2lib::zx(op1.str(), BYTE_SIZE_BIT),
                smt2lib::zx(op2.str(), BYTE_SIZE_BIT)
              );
      /* Create the symbolic element */
      se = ap.createRegSE(inst, expr, ID_RAX, WORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegMem(se, ID_RAX, mem, memSize);
      /* Add the symbolic flags element to the current inst */
      rax << smt2lib::extract(15, 8, expr.str());
      EflagsBuilder::cfMul(inst, se, ap, memSize, rax);
      EflagsBuilder::ofMul(inst, se, ap, memSize, rax);
      break;

    /* DX:AX = AX * r/m16 */
    case WORD_SIZE:
      /* Final expr */
      expr << smt2lib::bvmul(
                smt2lib::zx(op1.str(), WORD_SIZE_BIT),
                smt2lib::zx(op2.str(), WORD_SIZE_BIT)
              );
      rax << smt2lib::extract(15, 0, expr.str());
      rdx << smt2lib::extract(31, 16, expr.str());
      /* Create the symbolic element for AX */
      se = ap.createRegSE(inst, rax, ID_RAX, WORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegMem(se, ID_RAX, mem, memSize);
      /* Create the symbolic element for DX */
      se = ap.createRegSE(inst, rdx, ID_RDX, WORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegMem(se, ID_RDX, mem, memSize);
      /* Add the symbolic flags element to the current inst */
      EflagsBuilder::cfMul(inst, se, ap, memSize, rdx);
      EflagsBuilder::ofMul(inst, se, ap, memSize, rdx);
      break;

    /* EDX:EAX = EAX * r/m32 */
    case DWORD_SIZE:
      /* Final expr */
      expr << smt2lib::bvmul(
                smt2lib::zx(op1.str(), DWORD_SIZE_BIT),
                smt2lib::zx(op2.str(), DWORD_SIZE_BIT)
              );
      rax << smt2lib::extract(31, 0, expr.str());
      rdx << smt2lib::extract(63, 32, expr.str());
      /* Create the symbolic element for EAX */
      se = ap.createRegSE(inst, rax, ID_RAX, DWORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegMem(se, ID_RAX, mem, memSize);
      /* Create the symbolic element for EDX */
      se = ap.createRegSE(inst, rdx, ID_RDX, DWORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegMem(se, ID_RDX, mem, memSize);
      /* Add the symbolic flags element to the current inst */
      EflagsBuilder::cfMul(inst, se, ap, memSize, rdx);
      EflagsBuilder::ofMul(inst, se, ap, memSize, rdx);
      break;

    /* RDX:RAX = RAX * r/m64 */
    case QWORD_SIZE:
      /* Final expr */
      expr << smt2lib::bvmul(
                smt2lib::zx(op1.str(), QWORD_SIZE_BIT),
                smt2lib::zx(op2.str(), QWORD_SIZE_BIT)
              );
      rax << smt2lib::extract(63, 0, expr.str());
      rdx << smt2lib::extract(127, 64, expr.str());
      /* Create the symbolic element for RAX */
      se = ap.createRegSE(inst, rax, ID_RAX, QWORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegMem(se, ID_RAX, mem, memSize);
      /* Create the symbolic element for RDX */
      se = ap.createRegSE(inst, rdx, ID_RDX, QWORD_SIZE);
      /* Apply the taint */
      ap.aluSpreadTaintRegMem(se, ID_RDX, mem, memSize);
      /* Add the symbolic flags element to the current inst */
      EflagsBuilder::cfMul(inst, se, ap, memSize, rdx);
      EflagsBuilder::ofMul(inst, se, ap, memSize, rdx);
      break;

  }

}


void MulIRBuilder::imm(AnalysisProcessor &ap, Inst &inst) const {
  /* There is no <inc imm> available in x86 */
  OneOperandTemplate::stop(this->disas);
}


void MulIRBuilder::none(AnalysisProcessor &ap, Inst &inst) const {
  /* There is no <inc none> available in x86 */
  OneOperandTemplate::stop(this->disas);
}


Inst *MulIRBuilder::process(AnalysisProcessor &ap) const {
  this->checkSetup();

  Inst *inst = new Inst(ap.getThreadID(), this->address, this->disas);

  try {
    this->templateMethod(ap, *inst, this->operands, "MUL");
    ap.incNumberOfExpressions(inst->numberOfElements()); /* Used for statistics */
    ControlFlow::rip(*inst, ap, this->nextAddress);
  }
  catch (std::exception &e) {
    delete inst;
    throw;
  }

  return inst;
}

