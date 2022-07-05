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
**  Object      : ah:8 bitsvector[15..8]
**  Object      : ah:8 bitsvector[15..8]
*/

#include <iostream>
#include <triton/x86Specifications.hpp>
#include <triton/context.hpp>

using namespace triton;
using namespace triton::arch;
using namespace triton::arch::x86;


int main(int ac, const char **av) {
  triton::Context ctx;

  /* Set the arch */
  ctx.setArchitecture(ARCH_X86_64);

  std::cout << "Name        : " << ctx.registers.x86_ah.getName() << std::endl;
  std::cout << "Size byte   : " << ctx.registers.x86_ah.getSize() << std::endl;
  std::cout << "Size bit    : " << ctx.registers.x86_ah.getBitSize() << std::endl;
  std::cout << "Higher bit  : " << ctx.registers.x86_ah.getHigh() << std::endl;
  std::cout << "Lower  bit  : " << ctx.registers.x86_ah.getLow() << std::endl;
  std::cout << "Parent      : " << ctx.getParentRegister(ID_REG_X86_AH).getName() << std::endl;
  std::cout << "operator<<  : " << ctx.getRegister(ID_REG_X86_AH) << std::endl;
  std::cout << "Object      : " << ctx.getRegister("ah") << std::endl;
  std::cout << "Object      : " << ctx.getRegister("AH") << std::endl;

  std::cout << "----------------------------" << std::endl;

  for(const auto& kv: ctx.getAllRegisters())
    std::cout << kv.second << std::endl;

  return 0;
}

