/* Used to test the C++ API */

#include <iostream>
#include <sstream>

#include <triton/api.hpp>
#include <triton/bitsVector.hpp>
#include <triton/immediate.hpp>
#include <triton/instruction.hpp>
#include <triton/memoryAccess.hpp>
#include <triton/operandWrapper.hpp>
#include <triton/register.hpp>
#include <triton/x8664Cpu.hpp>
#include <triton/x86Cpu.hpp>
#include <triton/x86Specifications.hpp>


int test_1(void) {
  triton::arch::x86::x8664Cpu   cpy;
  triton::API                   api;

  api.setArchitecture(triton::arch::ARCH_X86_64);
  api.setConcreteRegisterValue(api.getRegister(triton::arch::ID_REG_RAX), 12345);

  if (api.getConcreteRegisterValue(api.getRegister(triton::arch::ID_REG_RAX)) != 12345)
    return 1;

  cpy = *reinterpret_cast<triton::arch::x86::x8664Cpu*>(api.getCpuInstance());
  if (cpy.getConcreteRegisterValue(api.getRegister(triton::arch::ID_REG_RAX)) != 12345) {
    std::cerr << "test_1: KO (cpy context != api context)" << std::endl;
    return 1;
  }

  std::cout << "test_1: OK" << std::endl;
  return 0;
}


int test_2(void) {
  triton::arch::x86::x86Cpu   cpy;
  triton::API                 api;

  api.setArchitecture(triton::arch::ARCH_X86);
  api.setConcreteRegisterValue(api.getRegister(triton::arch::ID_REG_EAX), 12345);

  if (api.getConcreteRegisterValue(api.getRegister(triton::arch::ID_REG_EAX)) != 12345)
    return 1;

  cpy = *reinterpret_cast<triton::arch::x86::x86Cpu*>(api.getCpuInstance());
  if (cpy.getConcreteRegisterValue(api.getRegister(triton::arch::ID_REG_EAX)) != 12345) {
    std::cerr << "test_2: KO (cpy context != api context)" << std::endl;
    return 1;
  }

  std::cout << "test_2: OK" << std::endl;
  return 0;
}


int test_3(void) {
  triton::arch::BitsVector bv;
  std::stringstream        s;

  bv.setHigh(31);
  bv.setLow(0);
  s << &bv;
  if (s.str() != "bv[31..0]") {
    std::cerr << "test_3: KO (" << s.str() << " != bv[31..0])" << std::endl;
    return 1;
  }

  std::cout << "test_3: OK" << std::endl;
  return 0;
}


int test_4(void) {
  triton::arch::Immediate imm;

  imm.setValue(0xff, 1);
  if (imm.getValue() != 0xff) {
    std::cerr << "test_4: KO (" << std::hex << imm.getValue() << std::dec << " != 0xff)" << std::endl;
    return 1;
  }

  imm.setValue(0x1122, 1);
  if (imm.getValue() != 0x22) {
    std::cerr << "test_4: KO (" << std::hex << imm.getValue() << std::dec << " != 0x22)" << std::endl;
    return 1;
  }

  imm.setValue(0x1122, 2);
  if (imm.getValue() != 0x1122) {
    std::cerr << "test_4: KO (" << std::hex << imm.getValue() << std::dec << " != 0x1122)" << std::endl;
    return 1;
  }

  if (imm.getAbstractLow() != 0) {
    std::cerr << "test_4: KO (" << std::hex << imm.getAbstractLow() << std::dec << " != 0)" << std::endl;
    return 1;
  }

  if (imm.getAbstractHigh() != 15) {
    std::cerr << "test_4: KO (" << std::hex << imm.getAbstractHigh() << std::dec << " != 15)" << std::endl;
    return 1;
  }

  triton::arch::Immediate imm1(12345, 8);
  triton::arch::Immediate imm2(12345, 8);
  if (imm1 != imm2) {
    std::cerr << "test_4: KO (" << imm2 << " != " << imm2 << ")" << std::endl;
    return 1;
  }

  std::cout << "test_4: OK" << std::endl;
  return 0;
}


int test_5(void) {
  triton::arch::Immediate imm1(0xff, 1);
  triton::arch::Immediate imm2(0xff, 2);
  triton::arch::MemoryAccess mem1(0x1000, 1);
  triton::arch::MemoryAccess mem2(0x1001, 1);
  triton::arch::OperandWrapper op1(imm1);
  triton::arch::OperandWrapper op2(imm2);
  triton::arch::OperandWrapper op3(mem1);
  triton::arch::OperandWrapper op4(mem2);
  std::stringstream s1;
  std::stringstream s2;

  if (op1 == op2) {
    std::cerr << "test_5: KO (" << op1 << " == " << op2 << ")" << std::endl;
    return 1;
  }

  if (op1.getType() != op2.getType()) {
    std::cerr << "test_5: KO (" << op1.getType() << " == " << op2.getType() << ")" << std::endl;
    return 1;
  }

  if (op1.getImmediate() != imm1) {
    std::cerr << "test_5: KO (" << op1.getImmediate() << " != " << imm1 << ")" << std::endl;
    return 1;
  }

  if (op1.getSize() != imm1.getSize()) {
    std::cerr << "test_5: KO (" << op1.getSize() << " != " << imm1.getSize() << ")" << std::endl;
    return 1;
  }

  if (op1.getAbstractHigh() != imm1.getAbstractHigh()) {
    std::cerr << "test_5: KO (" << op1.getAbstractHigh() << " != " << imm1.getAbstractHigh() << ")" << std::endl;
    return 1;
  }

  if (op1.getAbstractLow() != imm1.getAbstractLow()) {
    std::cerr << "test_5: KO (" << op1.getAbstractLow() << " != " << imm1.getAbstractLow() << ")" << std::endl;
    return 1;
  }

  triton::arch::OperandWrapper opx = op1;
  if (opx != op1) {
    std::cerr << "test_5: KO (" << opx << " == " << op1 << ")" << std::endl;
    return 1;
  }

  s1 << &op1;
  s2 << &imm1;
  if (s1.str() != s2.str()) {
    std::cerr << "test_3: KO (" << s1.str() << " != " << s2.str() << ")" << std::endl;
    return 1;
  }

  if (op2 < op1) {
    std::cerr << "test_3: KO (" << op2 << " < " << op1 << ")" << std::endl;
    return 1;
  }

  if (op3 == op4) {
    std::cerr << "test_5: KO (" << op3 << " == " << op4 << ")" << std::endl;
    return 1;
  }

  op3 = op4;
  if (op3 != op4) {
    std::cerr << "test_5: KO (" << op3 << " != " << op4 << ")" << std::endl;
    return 1;
  }

  op3.setMemory(mem2);
  if (op3.getMemory() != mem2) {
    std::cerr << "test_5: KO (" << op3.getMemory() << " != " << mem2 << ")" << std::endl;
    return 1;
  }

  op1.setImmediate(imm2);
  if (op1.getImmediate() != imm2) {
    std::cerr << "test_5: KO (" << op1.getImmediate() << " != " << imm2 << ")" << std::endl;
    return 1;
  }

  std::cout << "test_5: OK" << std::endl;
  return 0;
}


int test_6(void) {
  triton::API ctx;

  ctx.setArchitecture(triton::arch::ARCH_X86_64);
  triton::arch::Instruction inst1((const unsigned char*)"\x48\x89\xd8", 3); // mov rax, rbx
  triton::arch::Instruction inst2;

  ctx.processing(inst1);
  inst2 = inst1;

  if (inst2.getType() != inst1.getType()) {
    std::cerr << "test_6: KO (" << inst2.getType() << " != " << inst1.getType() << ")" << std::endl;
    return 1;
  }

  triton::arch::Instruction inst3(inst2);
  if (inst3.getType() != inst2.getType()) {
    std::cerr << "test_6: KO (" << inst3.getType() << " != " << inst2.getType() << ")" << std::endl;
    return 1;
  }

  if (!inst3.isReadFrom(triton::arch::OperandWrapper(ctx.getRegister(triton::arch::ID_REG_RBX)))) {
    std::cerr << "test_6: KO (!isReadFrom(rbx))" << std::endl;
    return 1;
  }

  inst3.removeReadRegister(ctx.getRegister(triton::arch::ID_REG_RBX));
  if (inst3.isReadFrom(triton::arch::OperandWrapper(ctx.getRegister(triton::arch::ID_REG_RBX)))) {
    std::cerr << "test_6: KO (isReadFrom(rbx))" << std::endl;
    return 1;
  }

  if (!inst3.isWriteTo(triton::arch::OperandWrapper(ctx.getRegister(triton::arch::ID_REG_RAX)))) {
    std::cerr << "test_6: KO (!isWriteTo(rax))" << std::endl;
    return 1;
  }

  inst3.removeWrittenRegister(ctx.getRegister(triton::arch::ID_REG_RAX));
  if (inst3.isWriteTo(triton::arch::OperandWrapper(ctx.getRegister(triton::arch::ID_REG_RAX)))) {
    std::cerr << "test_6: KO (isReadFrom(rax))" << std::endl;
    return 1;
  }

  if (inst3.isSymbolized()) {
    std::cerr << "test_6: KO (isSymbolized)" << std::endl;
    return 1;
  }

  if (inst3.isTainted()) {
    std::cerr << "test_6: KO (isTainted)" << std::endl;
    return 1;
  }

  inst3.setTaint(true);
  if (!inst3.isTainted()) {
    std::cerr << "test_6: KO (!isTainted)" << std::endl;
    return 1;
  }

  triton::arch::Instruction inst4((const unsigned char*)"\x48\x8b\x03", 3); // mov rax, [rbx]
  ctx.processing(inst4);
  if (!inst4.isReadFrom(triton::arch::OperandWrapper(triton::arch::MemoryAccess(0, 8)))) {
    std::cerr << "test_6: KO (!isReadFrom(0x0))" << std::endl;
    return 1;
  }

  inst4.removeLoadAccess(triton::arch::MemoryAccess(0, 8));
  if (inst4.isReadFrom(triton::arch::OperandWrapper(triton::arch::MemoryAccess(0, 8)))) {
    std::cerr << "test_6: KO (isReadFrom(0x0))" << std::endl;
    return 1;
  }

  triton::arch::Instruction inst5((const unsigned char*)"\x48\x89\x18", 3); // mov [rax], rbx
  ctx.processing(inst5);
  if (!inst5.isWriteTo(triton::arch::OperandWrapper(triton::arch::MemoryAccess(0, 8)))) {
    std::cerr << "test_6: KO (!isWriteTo(0x0))" << std::endl;
    return 1;
  }

  inst5.removeStoreAccess(triton::arch::MemoryAccess(0, 8));
  if (inst5.isWriteTo(triton::arch::OperandWrapper(triton::arch::MemoryAccess(0, 8)))) {
    std::cerr << "test_6: KO (isWriteTo(0x0))" << std::endl;
    return 1;
  }

  triton::arch::Instruction inst6((const unsigned char*)"\xb0\x01", 2); // mov al, 1
  ctx.processing(inst6);
  if (!inst6.isReadFrom(triton::arch::OperandWrapper(triton::arch::Immediate(1, 1)))) {
    std::cerr << "test_6: KO (!isReadFrom(1))" << std::endl;
    return 1;
  }

  inst5.removeReadImmediate(triton::arch::Immediate(1, 1));
  if (inst5.isReadFrom(triton::arch::OperandWrapper(triton::arch::Immediate(1, 1)))) {
    std::cerr << "test_6: KO (isReadFrom(1))" << std::endl;
    return 1;
  }

  std::cout << "test_6: OK" << std::endl;
  return 0;
}


int main(int ac, const char **av) {
  if (test_1())
    return 1;

  if (test_2())
    return 1;

  if (test_3())
    return 1;

  if (test_4())
    return 1;

  if (test_5())
    return 1;

  if (test_6())
    return 1;

  return 0;
}
