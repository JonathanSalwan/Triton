
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

struct op traceA = {0x400000, (unsigned char *)"\x66\x0F\xA5\xC2",             4}; /* shld       dx,ax,cl                    */
struct op traceB = {0x400000, (unsigned char *)"\x0F\xA5\xC2",             3}; /* shld       edx,eax,cl                    */

uint16_t expectedEDX[] ={0x962C, 0x2C58, 0x58B0, 0xB161, 0x62C3, 0xC586, 0x8B0C, 0x1619, 0x2C33, 0x5867, 0xB0CF, 0x619E, 0xC33D, 0x867A, 0x0CF4, 0x19E9, 0x33D2, 0x67A5, 0xCF4A, 0x9E94, 0x3D29, 0x7A52, 0xF4A5, 0xE94B, 0xD296, 0xA52C, 0x4A58, 0x94B1, 0x2962, 0x52C5, 0xA58B, 0x4B16};

uint8_t expectedCF[] ={0x00, 0x01, 0x00, 0x00, 0x01, 0x00, 0x01, 0x01, 0x00, 0x00, 0x00, 0x01,
 0x00, 0x01, 0x01, 0x00, 0x00, 0x00, 0x00, 0x01, 0x01, 0x00, 0x00, 0x01, 0x01, 0x01, 0x01, 0x00,
 0x01, 0x00, 0x00, 0x01, 0x01};

uint8_t expectedPF[] ={0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x01, 0x00, 0x01, 0x00, 0x01, 0x00,
 0x00, 0x00, 0x00, 0x00, 0x01, 0x01, 0x00, 0x00, 0x00, 0x00, 0x01, 0x01, 0x01, 0x00, 0x00, 0x01, 
 0x00, 0x01, 0x01, 0x00, 0x01};

uint8_t expectedSF[] ={0x00, 0x00, 0x00, 0x01, 0x00, 0x01, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00,
 0x01, 0x01, 0x00, 0x00, 0x00, 0x00, 0x01, 0x01, 0x00, 0x00, 0x01, 0x01, 0x01, 0x01, 0x00, 0x01,
 0x00, 0x00, 0x01, 0x00, 0x01};

uint8_t expectedZF[] ={0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x01, 0x01, 0x00, 
 0x00, 0x00, 0x00, 0x00, 0x01};

uint32_t expectedEDX32[] ={0x3B7BBC1D, 0x76F7783B, 0xEDEEF077, 0xDBDDE0EE, 0xB7BBC1DC, 0x6F7783B8, 
 0xDEEF0771, 0xBDDE0EE2, 0x7BBC1DC5, 0xF7783B8A, 0xEEF07714, 0xDDE0EE29, 0xBBC1DC52, 0x7783B8A4, 
 0xEF077148, 0xDE0EE290, 0xBC1DC520, 0x783B8A40, 0xF0771481, 0xE0EE2902, 0xC1DC5204, 0x83B8A408, 
 0x07714810, 0x0EE29021, 0x1DC52043, 0x3B8A4087, 0x7714810F, 0xEE29021F, 0xDC52043E, 0xB8A4087D, 
 0x714810FA, 0xE29021F5, 0x3B7BBC1D};

void exec(const op &trace, uint64_t eax, uint64_t ecx, uint64_t edx, uint8_t cf, uint8_t of,
    uint8_t zf) {
      Instruction inst;
      inst.setAddress(trace.addr);
      inst.setOpcodes(trace.inst, trace.size);
      api.setConcreteRegisterValue(triton::arch::Register(triton::arch::x86::ID_REG_CF,cf));
      api.setConcreteRegisterValue(triton::arch::Register(triton::arch::x86::ID_REG_OF,of));
      api.setConcreteRegisterValue(triton::arch::Register(triton::arch::x86::ID_REG_ZF,zf));
      api.setConcreteRegisterValue(triton::arch::Register(triton::arch::x86::ID_REG_EAX,eax));
      api.setConcreteRegisterValue(triton::arch::Register(triton::arch::x86::ID_REG_ECX,ecx));
      api.setConcreteRegisterValue(triton::arch::Register(triton::arch::x86::ID_REG_EDX,edx));
      api.concretizeAllRegister();
      api.processing(inst);
      /*for (unsigned int exp_index = 0; exp_index != inst.symbolicExpressions.size(); exp_index++) {
          auto expr = inst.symbolicExpressions[exp_index];
          std::cout << "\tSymExpr " << exp_index << ": " << expr << std::endl;
      }*/
}

void reportError(std::string desc, int width, triton::uint512 actual, uint64_t expected) {
    if (expected != actual) {
        std::cout << std::hex << desc << ": "  <<
        std::setfill('0') << std::setw(width) << actual << ", expected " << std::setw(width) <<
        expected << std::dec << std::endl;
    }
}

int main(int ac, const char **av) {

  /* Set the arch */
  api.setArchitecture(ARCH_X86);

  //shift and CF test
  for (int i=0; i<33; ++i) {
      Instruction inst;
      inst.setAddress(traceA.addr);
      inst.setOpcodes(traceA.inst, traceA.size);

      api.setConcreteRegisterValue(triton::arch::Register(triton::arch::x86::ID_REG_CF,i/32));
      api.setConcreteRegisterValue(triton::arch::Register(triton::arch::x86::ID_REG_PF,i/32));
      api.setConcreteRegisterValue(triton::arch::Register(triton::arch::x86::ID_REG_SF,i/32));
      api.setConcreteRegisterValue(triton::arch::Register(triton::arch::x86::ID_REG_EAX,0x33d2));
      api.setConcreteRegisterValue(triton::arch::Register(triton::arch::x86::ID_REG_ECX,
        (i%32)+0xC0));
      api.setConcreteRegisterValue(triton::arch::Register(triton::arch::x86::ID_REG_EDX,0x962C));
      api.concretizeAllRegister();

      /* Process everything */
      api.processing(inst);

    /*for (unsigned int exp_index = 0; exp_index != inst.symbolicExpressions.size(); exp_index++) {
        auto expr = inst.symbolicExpressions[exp_index];
        std::cout << "\tSymExpr " << exp_index << ": " << expr << std::endl;
    }*/

      if (i<32) {
          auto edx = api.getConcreteRegisterValue(triton::arch::x86::ID_REG_EDX);
          if (expectedEDX[i] != edx) {
              std::cout << std::hex << "incorrect edx for ecx=" << (i+0xC0) << ": "  <<
                std::setfill('0') << std::setw(4) << edx << ", expected " << std::setw(4) <<
                expectedEDX[i]<<std::dec <<  std::endl;
          }
      }
      auto cf = api.getConcreteRegisterValue(triton::arch::x86::ID_REG_CF);
      if (expectedCF[i] != cf) {
          std::cout << std::hex << "incorrect CF for ecx=" << (i+0xC0) << ": " << std::dec <<
            cf << ", expected " << int(expectedCF[i]) << std::endl;
      }
      auto pf = api.getConcreteRegisterValue(triton::arch::x86::ID_REG_PF);
      if (expectedPF[i] != pf) {
          std::cout << std::hex << "incorrect PF for ecx=" << (i+0xC0) << ": " << std::dec <<
            pf << ", expected " << int(expectedPF[i]) << std::endl;
      }
      auto sf = api.getConcreteRegisterValue(triton::arch::x86::ID_REG_SF);
      if (expectedSF[i] != sf) {
          std::cout << std::hex << "incorrect SF for ecx=" << (i+0xC0) << ": " << std::dec <<
            pf << ", expected " << int(expectedSF[i]) << std::endl;
      }
    }
    //OF test
    exec(traceA,0x33d2,0xC0,0x962C,0,0,0);
    reportError("shift 0, original OF 0", 1,
        api.getConcreteRegisterValue(triton::arch::x86::ID_REG_OF), 0);
    exec(traceA,0x33d2,0xC0,0x962C,0,1,0);
    reportError("shift 0, original OF 1", 1,
        api.getConcreteRegisterValue(triton::arch::x86::ID_REG_OF), 1);
    exec(traceA,0x33d2,0xC1,0x962C,0,0,0);
    reportError("shift 1, original OF 0, edx 0x962C", 1,
        api.getConcreteRegisterValue(triton::arch::x86::ID_REG_OF), 1);
    exec(traceA,0x33d2,0xC1,0x962C,0,1,0);
    reportError("shift 1, original OF 1, edx 0x962C", 1,
        api.getConcreteRegisterValue(triton::arch::x86::ID_REG_OF), 1);
    exec(traceA,0x33d2,0xC2,0x962C,0,0,0);
    reportError("shift 2, original OF 0, edx 0x962C", 1,
        api.getConcreteRegisterValue(triton::arch::x86::ID_REG_OF), 1);
    exec(traceA,0x33d2,0xC2,0x962C,0,1,0);
    reportError("shift 2, original OF 1, edx 0x962C", 1,
        api.getConcreteRegisterValue(triton::arch::x86::ID_REG_OF), 1);
    exec(traceA,0x33d2,0xC1,0x162C,0,0,0);
    reportError("shift 1, original OF 0, edx 0x162C", 1,
        api.getConcreteRegisterValue(triton::arch::x86::ID_REG_OF), 0);
    exec(traceA,0x33d2,0xC1,0x162C,0,1,0);
    reportError("shift 1, original OF 1, edx 0x162C", 1,
        api.getConcreteRegisterValue(triton::arch::x86::ID_REG_OF), 0);
    exec(traceA,0x33d2,0xC2,0x162C,0,0,0);
    reportError("shift 2, original OF 0, edx 0x162C", 1,
        api.getConcreteRegisterValue(triton::arch::x86::ID_REG_OF), 0);
    exec(traceA,0x33d2,0xC2,0x162C,0,1,0);
    reportError("shift 2, original OF 1, edx 0x162C", 1,
        api.getConcreteRegisterValue(triton::arch::x86::ID_REG_OF), 0);

    for (int i=0; i<33; ++i) {
        exec(traceA,0x3300,0xC0+i,0x002C,0,0,i/32);
        reportError("shift "+std::to_string(i)+", original ZF "+std::to_string(i/32), 1,
            api.getConcreteRegisterValue(triton::arch::x86::ID_REG_ZF), expectedZF[i]);
    }

    for (int i=0; i<33; ++i) {
        exec(traceB,0xC52043EA,0xC0+i,0x3B7BBC1D,0,0,0);
        reportError("shift "+std::to_string(i)+", 32-bit", 8,
            api.getConcreteRegisterValue(triton::arch::x86::ID_REG_EDX), expectedEDX32[i]);
    }
    return 0;
}

