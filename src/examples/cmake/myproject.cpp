// This is an example about how to compile Triton using its config file.
// See the CMakeLists.txt from this directory.

#include <iostream>
#include <triton/context.hpp>

int main(int ac, const char *av[]) {
  /* Triton's context */
  triton::Context ctx = triton::Context(triton::arch::ARCH_X86_64);

  /* Symbolize rax */
  ctx.symbolizeRegister(ctx.registers.x86_rax);

  /* Process an instruction (inc rax) */
  triton::arch::Instruction inst = triton::arch::Instruction(0x40000, "\x48\xff\xc0", 3);
  ctx.processing(inst);

  /* Display instruction's expressions */
  std::cout << inst << std::endl;
  for (const auto& se : inst.symbolicExpressions) {
    std::cout << "    -> " << se << std::endl;
  }

  return 0;
}
