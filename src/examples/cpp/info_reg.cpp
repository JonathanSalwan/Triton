/*
** Output:
**
**  $ ./info_reg.bin
**  Name        : ah
**  Size byte   : 1
**  Size bit    : 8
**  Highed bit  : 15
**  Lower  bit  : 8
**  Parent      : rax
**  operator<<  : ah:8 bitsvector[15..8]
*/

#include <iostream>
#include <triton/x86Specifications.hpp>
#include <triton/api.hpp>

using namespace triton;
using namespace triton::arch;
using namespace triton::arch::x86;


int main(int ac, const char **av) {

  /* Set the arch */
  api.setArchitecture(ARCH_X86_64);

  std::cout << "Name        : " << TRITON_X86_REG_AH.getName() << std::endl;
  std::cout << "Size byte   : " << TRITON_X86_REG_AH.getSize() << std::endl;
  std::cout << "Size bit    : " << TRITON_X86_REG_AH.getBitSize() << std::endl;
  std::cout << "Highed bit  : " << TRITON_X86_REG_AH.getHigh() << std::endl;
  std::cout << "Lower  bit  : " << TRITON_X86_REG_AH.getLow() << std::endl;
  std::cout << "Parent      : " << TRITON_X86_REG_AH.getParent().getName() << std::endl;
  std::cout << "operator<<  : " << TRITON_X86_REG_AH << std::endl;

  std::cout << "----------------------------" << std::endl;

  auto reg = api.getAllRegisters();
  for (auto it = reg.begin(); it != reg.end(); it++) {
    Register r = **it;
    std::cout << r << std::endl;
  }

  return 0;
}

