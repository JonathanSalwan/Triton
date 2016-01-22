/*
** Copyright (C) - Triton
**
** This program is under the terms of the LGPLv3 License.
**
** Output
**
** 400017: xor rax, rax
**         SymExpr 0: (_ bv1 1) ; XOR operation
**         SymExpr 1: (_ bv1 1) ; Clears carry flag
**         SymExpr 2: (_ bv1 1) ; Clears overflow flag
**         SymExpr 3: (_ bv1 1) ; Parity flag
**         SymExpr 4: (_ bv1 1) ; Sign flag
**         SymExpr 5: (_ bv1 1) ; Zero flag
*/


#include <iostream>
#include <triton/api.hpp>
#include <triton/x86Specifications.hpp>

using namespace triton;
using namespace triton::arch;


struct op {
  unsigned int    addr;
  unsigned char*  inst;
  unsigned int    size;
};

struct op trace[] = {
  {0x400017, (unsigned char *)"\x48\x31\xc0", 3}, /* xor rax, rax */
  {0x0,      nullptr,                         0}
};


/* if (bvxor x x) -> (_ bv0 x_size) */
smt2lib::smtAstAbstractNode* xor_simplification(smt2lib::smtAstAbstractNode* node) {

  if (node->getKind() == smt2lib::BVXOR_NODE) {
    if (*(node->getChilds()[0]) == *(node->getChilds()[1]))
      return smt2lib::bv(0, node->getBitvectorSize());
  }

  return node;
}


int main(int ac, const char **av) {

  /* Set the arch */
  api.setArchitecture(ARCH_X86_64);

  /* Record a simplification callback */
  api.recordSimplificationCallback(xor_simplification);

  for (unsigned int i = 0; trace[i].inst; i++) {
    /* Build an instruction */
    Instruction inst;

    /* Setup opcodes */
    inst.setOpcodes(trace[i].inst, trace[i].size);

    /* optional - Setup address */
    inst.setAddress(trace[i].addr);

    /* optional - Update register state */
    inst.updateContext(RegisterOperand(x86::ID_REG_RAX, 12345));

    /* Process everything */
    api.processing(inst);

    /* Display all symbolic expression of the instruction */
    std::cout << inst << std::endl;
    for (unsigned int exp_index = 0; exp_index != inst.symbolicExpressions.size(); exp_index++) {
      auto expr = inst.symbolicExpressions[exp_index];
      std::cout << "\tSymExpr " << exp_index << ": " << expr << std::endl;
    }

  }

  return 0;
}

