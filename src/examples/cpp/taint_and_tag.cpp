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
#include <triton/covTag.hpp>

using namespace triton;
using namespace triton::arch;
using namespace triton::arch::x86;

triton::API api;

void printRegInfo(std::string regName, triton::arch::Register reg) {
  std::cout << regName<< " tainted? "<< api.isRegisterTainted(reg) << std::endl;
  std::cout<< regName<< " tags: ";
  auto tags = api.getTags(reg);
  for (auto tag : tags) {
    std::cout << *tag << " ";
  }
  std::cout<< std::endl<< std::endl;
}

int main(int ac, const char **av) {

  /* Set the arch */
  api.setArchitecture(ARCH_X86_64);

  /* create a tag */
  auto ctag = new triton::engines::taint::CovTag(99, true);

  /* Taint the RAX */
  api.taintRegister(api.getRegister(ID_REG_RAX), ctag);

  /* Is RDX tainted ? */
  printRegInfo("RDX", api.getRegister(ID_REG_RDX));

  /* Spread RAX into RDX */
  api.taintAssignmentRegisterRegister(api.getRegister(ID_REG_RDX), api.getRegister(ID_REG_RAX));

  /* Is RDX tainted ? */
  printRegInfo("RDX", api.getRegister(ID_REG_RDX));

  /* Untaint RDX */
  api.untaintRegister(api.getRegister(ID_REG_RDX));

  /* Is RDX tainted ? */
  printRegInfo("RDX", api.getRegister(ID_REG_RDX));

  return 0;
}

