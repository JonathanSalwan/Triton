
#include <iostream>
#include <triton/api.hpp>
#include <triton/basicBlock.hpp>

using namespace triton;
using namespace triton::arch;


int main(int ac, const char **av) {
  /* Init the triton context */
  triton::API api;

  /* Set the arch */
  api.setArchitecture(ARCH_X86_64);

  BasicBlock block = BasicBlock({
    Instruction((unsigned char *)"\x89\xd0", 2),      /* mov   eax, edx  */
    Instruction((unsigned char *)"\x80\xf4\x99", 3),  /* xor   ah, 0x99  */
    Instruction((unsigned char *)"\x85\xc0", 2),      /* test  eax, eax  */
    Instruction((unsigned char *)"\x74\x08", 2),      /* jz    10        */
  });

  api.disassembly(block);

  std::cout << block << std::endl;
  std::cout << "----------" << std::endl;

  auto i = Instruction((unsigned char *)"\x90", 1); /* nop */
  api.disassembly(i);

  block.add(i);
  block.add(i);
  block.add(i);

  std::cout << block << std::endl;
  std::cout << "----------" << std::endl;

  block.remove(0);

  std::cout << block << std::endl;
  std::cout << "----------" << std::endl;

  api.disassembly(block, 0x1000);

  std::cout << block << std::endl;

  std::cout << "First addr: 0x" << std::hex << block.getFirstAddress() << std::endl;
  std::cout << "Last addr: " << std::hex << block.getLastAddress() << std::endl;
  std::cout << "Number of instructions: " << std::hex << block.getSize() << std::endl;

  std::cout << "----------" << std::endl;

  block.remove(2); /* remove the jz */
  api.processing(block);

  std::cout << block << std::endl;

  return 0;
}
