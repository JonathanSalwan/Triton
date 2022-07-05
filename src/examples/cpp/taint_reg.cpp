/*
** Output:
**
**  $ ./taint_reg
**  0
**  1
**  0
*/

#include <iostream>
#include <triton/context.hpp>
#include <triton/x86Specifications.hpp>

using namespace triton;
using namespace triton::arch;
using namespace triton::arch::x86;


int main(int ac, const char **av) {
  triton::Context ctx;

  /* Set the arch */
  ctx.setArchitecture(ARCH_X86_64);

  /* Taint the RAX */
  ctx.taintRegister(ctx.registers.x86_ah);

  /* Is RDX tainted ? */
  std::cout << ctx.isRegisterTainted(ctx.registers.x86_rdx) << std::endl;

  /* Spread RAX into RDX */
  ctx.taintAssignment(ctx.registers.x86_rdx, ctx.registers.x86_rax);

  /* Is RDX tainted ? */
  std::cout << ctx.isRegisterTainted(ctx.registers.x86_rdx) << std::endl;

  /* Untaint RDX */
  ctx.untaintRegister(ctx.registers.x86_rdx);

  /* Is RDX tainted ? */
  std::cout << ctx.isRegisterTainted(ctx.registers.x86_rdx) << std::endl;

  return 0;
}

