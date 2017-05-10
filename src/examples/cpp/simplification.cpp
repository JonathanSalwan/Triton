/*
** Output
**
**  400017: xor rax, rax
**          SymExpr 0: ref!0 = (_ bv0 64) ; XOR operation
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
ast::AbstractNode* xor_simplification(ast::AbstractNode* node) {

  if (node->getKind() == ast::ZX_NODE) {
    node = node->getChilds()[1];
  }

  if (node->getKind() == ast::BVXOR_NODE) {
    if (node->getChilds()[0]->equalTo(node->getChilds()[1]))
      return ast::bv(0, node->getBitvectorSize());
  }

  return node;
}


int main(int ac, const char **av) {

  /* Set the arch */
  api.setArchitecture(ARCH_X86_64);

  /* Record a simplification callback */
  api.addCallback(xor_simplification);

  for (unsigned int i = 0; trace[i].inst; i++) {
    /* Build an instruction */
    Instruction inst;

    /* Setup opcodes */
    inst.setOpcodes(trace[i].inst, trace[i].size);

    /* optional - Setup address */
    inst.setAddress(trace[i].addr);

    /* optional - Update register state */
    inst.updateContext(Register(x86::ID_REG_RAX, 12345));

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

