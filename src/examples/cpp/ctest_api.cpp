/* Used to test the C++ API */

#include <iostream>
#include <sstream>

#include <triton/api.hpp>
#include <triton/bitsVector.hpp>
#include <triton/immediate.hpp>
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

  std::cout << "test_4: OK" << std::endl;
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

  return 0;
}
