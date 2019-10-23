/*
** Output:
**
**  $ ./taint_reg
**  0
**  1
**  0
*/

#include <iostream>
#include <triton/api.hpp>
#include <triton/x86Specifications.hpp>

using namespace triton;
using namespace triton::arch;
using namespace triton::arch::x86;


int main(int ac, const char **av) {

  triton::API api;
  /* Set the arch */
  api.setArchitecture(ARCH_X86_64);

  /* Taint the RAX */
  api.taintRegister(api.registers.x86_ah);

  /* Is RDX tainted ? */
  std::cout << api.isRegisterTainted(api.registers.x86_rdx) << std::endl;

  /* Spread RAX into RDX */
  api.taintAssignment(api.registers.x86_rdx, api.registers.x86_rax);

  /* Is RDX tainted ? */
  std::cout << api.isRegisterTainted(api.registers.x86_rdx) << std::endl;

  /* Untaint RDX */
  api.untaintRegister(api.registers.x86_rdx);

  /* Is RDX tainted ? */
  std::cout << api.isRegisterTainted(api.registers.x86_rdx) << std::endl;

  return 0;
}

