
#include <iostream>
#include <triton/api.hpp>
#include <triton/x86Specifications.hpp>

using namespace triton;
using namespace triton::arch;


struct op {
  unsigned int    addr;
  unsigned char*  inst;
  unsigned int    size;
};

struct op trace[] = {
  {0x400000, (unsigned char *)"\x48\x8b\x05\xb8\x13\x00\x00", 7}, /* mov        rax, QWORD PTR [rip+0x13b8] */
  {0x400007, (unsigned char *)"\x48\x8d\x34\xc3",             4}, /* lea        rsi, [rbx+rax*8]            */
  {0x40000b, (unsigned char *)"\x67\x48\x8D\x74\xC3\x0A",     6}, /* lea        rsi, [ebx+eax*8+0xa]        */
  {0x40000b, (unsigned char *)"\x67\x8D\x74\xC3\x0A",         5}, /* lea        esi, [ebx+eax*8+0xa]        */
  {0x40000b, (unsigned char *)"\x48\x8D\x74\xDB\x0A",         5}, /* lea        rsi, [rbx+rax*8+0xa]        */
  {0x40000b, (unsigned char *)"\x48\x8D\x74\xC3\x0A",         5}, /* lea        rsi, [rbx+rax*8+0xa]        */
  {0x40000b, (unsigned char *)"\x48\x8D\x73\x0A",             4}, /* lea        rsi, [rbx+0xa]              */
  {0x400011, (unsigned char *)"\x66\x0F\xD7\xD1",             4}, /* pmovmskb   edx, xmm1                   */
  {0x400015, (unsigned char *)"\x89\xd0",                     2}, /* mov        eax, edx                    */
  {0x400017, (unsigned char *)"\x80\xf4\x99",                 3}, /* xor        ah, 0x99                    */
  {0x40001a, (unsigned char *)"\x48\x31\xc0",                 3}, /* xor        rax, rax                    */
  {0x40001d, (unsigned char *)"\x80\x30\x99",                 3}, /* xor        byte ptr [rax], 0x99        */
  {0x400020, (unsigned char *)"\x80\x30\x99",                 3}, /* xor        byte ptr [rax], 0x99        */
  {0x400023, (unsigned char *)"\x0F\x87\x00\x00\x00\x00",     6}, /* ja         11                          */
  {0x0,      nullptr,                                         0}
};


int main(int ac, const char **av) {

  /* Set the arch */
  api.setArchitecture(ARCH_X86_64);

  for (unsigned int i = 0; trace[i].inst; i++) {
    /* Build an instruction */
    Instruction inst;

    /* Setup opcodes */
    inst.setOpcodes(trace[i].inst, trace[i].size);

    /* optional - Setup address */
    inst.setAddress(trace[i].addr);

    /* Process everything */
    api.processing(inst);

    std::cout << inst << std::endl;
    for (unsigned int op_index = 0; op_index != inst.operands.size(); op_index++) {
      std::cout << "\tOperand " << op_index << ": " << inst.operands[op_index] << std::endl;
      if (inst.operands[op_index].getType() == OP_MEM) {
        std::cout << "\t   base  : " << inst.operands[op_index].getMemory().getBaseRegister() << std::endl;
        std::cout << "\t   index : " << inst.operands[op_index].getMemory().getIndexRegister() << std::endl;
        std::cout << "\t   disp  : " << inst.operands[op_index].getMemory().getDisplacement() << std::endl;
        std::cout << "\t   scale : " << inst.operands[op_index].getMemory().getScale() << std::endl;
      }
    }

    std::cout << "\t-------" << std::endl;

    for (unsigned int exp_index = 0; exp_index != inst.symbolicExpressions.size(); exp_index++) {
      auto expr = inst.symbolicExpressions[exp_index];
      std::cout << "\tSymExpr " << exp_index << ": " << expr << std::endl;
    }

    std::cout << std::endl << std::endl;
  }

  return 0;
}

