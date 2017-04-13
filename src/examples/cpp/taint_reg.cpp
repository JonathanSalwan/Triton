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
  api.taintRegister(api.getRegister(ID_REG_AH));

  /* Is RDX tainted ? */
  std::cout << api.isRegisterTainted(api.getRegister(ID_REG_RDX)) << std::endl;

  /* Spread RAX into RDX */
  api.taintAssignmentRegisterRegister(api.getRegister(ID_REG_RDX), api.getRegister(ID_REG_RAX));

  /* Is RDX tainted ? */
  std::cout << api.isRegisterTainted(api.getRegister(ID_REG_RDX)) << std::endl;

  /* Untaint RDX */
  api.untaintRegister(api.getRegister(ID_REG_RDX));

  /* Is RDX tainted ? */
  std::cout << api.isRegisterTainted(api.getRegister(ID_REG_RDX)) << std::endl;

  return 0;
}

