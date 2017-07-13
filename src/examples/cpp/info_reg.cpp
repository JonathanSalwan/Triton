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
  triton::API api;

  /* Set the arch */
  api.setArchitecture(ARCH_X86_64);

  std::cout << "Name        : " << api.getRegister(ID_REG_AH).getName() << std::endl;
  std::cout << "Size byte   : " << api.getRegister(ID_REG_AH).getSize() << std::endl;
  std::cout << "Size bit    : " << api.getRegister(ID_REG_AH).getBitSize() << std::endl;
  std::cout << "Higher bit  : " << api.getRegister(ID_REG_AH).getHigh() << std::endl;
  std::cout << "Lower  bit  : " << api.getRegister(ID_REG_AH).getLow() << std::endl;
  std::cout << "Parent      : " << api.getParentRegister(ID_REG_AH).getName() << std::endl;
  std::cout << "operator<<  : " << api.getRegister(ID_REG_AH) << std::endl;

  std::cout << "----------------------------" << std::endl;

  for(const auto& kv: api.getAllRegisters())
    std::cout << kv.second << std::endl;

  return 0;
}

