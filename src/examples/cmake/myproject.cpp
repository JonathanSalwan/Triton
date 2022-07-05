// This is an example about how to compile Triton using it's config file.
// See the CMakeLists.txt from this directory.

#include <iostream>
#include <triton/api.hpp>

int main(int ac, const char *av[]) {
  /* Triton's context */
  triton::API api = triton::API(triton::arch::ARCH_X86_64);

  /* Symbolize rax */
  api.symbolizeRegister(api.registers.x86_rax);

  /* Process an instruction (inc rax) */
  triton::arch::Instruction inst = triton::arch::Instruction(0x40000, "\x48\xff\xc0", 3);
  api.processing(inst);

  /* Display instruction's expressions */
  std::cout << inst << std::endl;
  for (const auto& se : inst.symbolicExpressions) {
    std::cout << "    -> " << se << std::endl;
  }

  return 0;
}
