/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <PINConverter.h>

#if defined(__x86_64__) || defined(_M_X64)

__uint PINConverter::convertDBIReg2TritonReg(__uint pinRegID) {
  switch(pinRegID){
    case REG_RAX:
    case REG_EAX:
    case REG_AX:
    case REG_AH:
    case REG_AL:
      return ID_RAX;

    case REG_RBX:
    case REG_EBX:
    case REG_BX:
    case REG_BH:
    case REG_BL:
      return ID_RBX;

    case REG_RCX:
    case REG_ECX:
    case REG_CX:
    case REG_CH:
    case REG_CL:
      return ID_RCX;

    case REG_RDX:
    case REG_EDX:
    case REG_DX:
    case REG_DH:
    case REG_DL:
      return ID_RDX;

    case REG_RDI:
    case REG_EDI:
    case REG_DI:
    case REG_DIL:
      return ID_RDI;

    case REG_RSI:
    case REG_ESI:
    case REG_SI:
    case REG_SIL:
      return ID_RSI;

    case REG_RBP:
    case REG_EBP:
    case REG_BP:
    case REG_BPL:
      return ID_RBP;

    case REG_RSP:
    case REG_ESP:
    case REG_SP:
    case REG_SPL:
      return ID_RSP;

    case REG_RIP:
    case REG_EIP:
    case REG_IP:
      return ID_RIP;

    case REG_R8:
    case REG_R8D:
    case REG_R8W:
    case REG_R8B:
      return ID_R8;

    case REG_R9:
    case REG_R9D:
    case REG_R9W:
    case REG_R9B:
      return ID_R9;

    case REG_R10:
    case REG_R10D:
    case REG_R10W:
    case REG_R10B:
      return ID_R10;

    case REG_R11:
    case REG_R11D:
    case REG_R11W:
    case REG_R11B:
      return ID_R11;

    case REG_R12:
    case REG_R12D:
    case REG_R12W:
    case REG_R12B:
      return ID_R12;

    case REG_R13:
    case REG_R13D:
    case REG_R13W:
    case REG_R13B:
      return ID_R13;

    case REG_R14:
    case REG_R14D:
    case REG_R14W:
    case REG_R14B:
      return ID_R14;

    case REG_R15:
    case REG_R15D:
    case REG_R15W:
    case REG_R15B:
      return ID_R15;

    case REG_RFLAGS:
      return ID_RFLAGS;

    case REG_XMM0:
      return ID_XMM0;

    case REG_XMM1:
      return ID_XMM1;

    case REG_XMM2:
      return ID_XMM2;

    case REG_XMM3:
      return ID_XMM3;

    case REG_XMM4:
      return ID_XMM4;

    case REG_XMM5:
      return ID_XMM5;

    case REG_XMM6:
      return ID_XMM6;

    case REG_XMM7:
      return ID_XMM7;

    case REG_XMM8:
      return ID_XMM8;

    case REG_XMM9:
      return ID_XMM9;

    case REG_XMM10:
      return ID_XMM10;

    case REG_XMM11:
      return ID_XMM11;

    case REG_XMM12:
      return ID_XMM12;

    case REG_XMM13:
      return ID_XMM13;

    case REG_XMM14:
      return ID_XMM14;

    case REG_XMM15:
      return ID_XMM15;

    default:
      return ID_INVALID;
  }
}


/* Convert a Triton register to a Pin register.
 * Besides, it can return only 64 bits wised registers.
 */
__uint PINConverter::convertTritonReg2DBIReg(__uint tritonRegId) {
  switch(tritonRegId){
    case ID_RAX:    return REG_RAX;
    case ID_RBX:    return REG_RBX;
    case ID_RCX:    return REG_RCX;
    case ID_RDX:    return REG_RDX;
    case ID_RDI:    return REG_RDI;
    case ID_RSI:    return REG_RSI;
    case ID_RBP:    return REG_RBP;
    case ID_RSP:    return REG_RSP;
    case ID_RIP:    return REG_RIP;
    case ID_R8:     return REG_R8;
    case ID_R9:     return REG_R9;
    case ID_R10:    return REG_R10;
    case ID_R11:    return REG_R11;
    case ID_R12:    return REG_R12;
    case ID_R13:    return REG_R13;
    case ID_R14:    return REG_R14;
    case ID_R15:    return REG_R15;
    case ID_RFLAGS: return REG_RFLAGS;
    case ID_XMM0:   return REG_XMM0;
    case ID_XMM1:   return REG_XMM1;
    case ID_XMM2:   return REG_XMM2;
    case ID_XMM3:   return REG_XMM3;
    case ID_XMM4:   return REG_XMM4;
    case ID_XMM5:   return REG_XMM5;
    case ID_XMM6:   return REG_XMM6;
    case ID_XMM7:   return REG_XMM7;
    case ID_XMM8:   return REG_XMM8;
    case ID_XMM9:   return REG_XMM9;
    case ID_XMM10:  return REG_XMM10;
    case ID_XMM11:  return REG_XMM11;
    case ID_XMM12:  return REG_XMM12;
    case ID_XMM13:  return REG_XMM13;
    case ID_XMM14:  return REG_XMM14;
    case ID_XMM15:  return REG_XMM15;
    default:
      return REG_INVALID_;
  }
}


/* Convert a Triton register to a string.
 * Besides, it can return only 64 bits wised registers.
 */
std::string PINConverter::getRegisterName(__uint tritonRegId) {
  switch(tritonRegId){
    case ID_RAX:    return "rax";
    case ID_RBX:    return "rbx";
    case ID_RCX:    return "rcx";
    case ID_RDX:    return "rdx";
    case ID_RDI:    return "rdi";
    case ID_RSI:    return "rsi";
    case ID_RBP:    return "rbp";
    case ID_RSP:    return "rsp";
    case ID_RIP:    return "rip";
    case ID_R8:     return "r8";
    case ID_R9:     return "r9";
    case ID_R10:    return "r10";
    case ID_R11:    return "r11";
    case ID_R12:    return "r12";
    case ID_R13:    return "r13";
    case ID_R14:    return "r14";
    case ID_R15:    return "r15";
    case ID_RFLAGS: return "rflags";
    case ID_XMM0:   return "xmm0";
    case ID_XMM1:   return "xmm1";
    case ID_XMM2:   return "xmm2";
    case ID_XMM3:   return "xmm3";
    case ID_XMM4:   return "xmm4";
    case ID_XMM5:   return "xmm5";
    case ID_XMM6:   return "xmm6";
    case ID_XMM7:   return "xmm7";
    case ID_XMM8:   return "xmm8";
    case ID_XMM9:   return "xmm9";
    case ID_XMM10:  return "xmm10";
    case ID_XMM11:  return "xmm11";
    case ID_XMM12:  return "xmm12";
    case ID_XMM13:  return "xmm13";
    case ID_XMM14:  return "xmm14";
    case ID_XMM15:  return "xmm15";
    case ID_AF:     return "af";
    case ID_CF:     return "cf";
    case ID_DF:     return "df";
    case ID_IF:     return "if";
    case ID_OF:     return "of";
    case ID_PF:     return "pf";
    case ID_SF:     return "sf";
    case ID_TF:     return "tf";
    case ID_ZF:     return "zf";
    default:
      return "invalid";
  }
}


std::pair<__uint, __uint> PINConverter::convertDBIReg2BitsVector(__uint pinRegID) {
  switch(pinRegID) {

    case REG_XMM0:
    case REG_XMM1:
    case REG_XMM2:
    case REG_XMM3:
    case REG_XMM4:
    case REG_XMM5:
    case REG_XMM6:
    case REG_XMM7:
    case REG_XMM8:
    case REG_XMM9:
    case REG_XMM10:
    case REG_XMM11:
    case REG_XMM12:
    case REG_XMM13:
    case REG_XMM14:
    case REG_XMM15:
      return std::make_pair((DQWORD_SIZE_BIT - 1), 0);

    case REG_RFLAGS:
    case REG_RAX:
    case REG_RBX:
    case REG_RCX:
    case REG_RDX:
    case REG_RDI:
    case REG_RSI:
    case REG_RBP:
    case REG_RSP:
    case REG_RIP:
    case REG_R8:
    case REG_R9:
    case REG_R10:
    case REG_R11:
    case REG_R12:
    case REG_R13:
    case REG_R14:
    case REG_R15:
      return std::make_pair((QWORD_SIZE_BIT - 1), 0);

    case REG_EAX:
    case REG_EBX:
    case REG_ECX:
    case REG_EDX:
    case REG_EDI:
    case REG_ESI:
    case REG_EBP:
    case REG_ESP:
    case REG_EIP:
    case REG_R8D:
    case REG_R9D:
    case REG_R10D:
    case REG_R11D:
    case REG_R12D:
    case REG_R13D:
    case REG_R14D:
    case REG_R15D:
      return std::make_pair((DWORD_SIZE_BIT - 1), 0);

    case REG_AX:
    case REG_BX:
    case REG_CX:
    case REG_DX:
    case REG_DI:
    case REG_SI:
    case REG_BP:
    case REG_SP:
    case REG_IP:
    case REG_R8W:
    case REG_R9W:
    case REG_R10W:
    case REG_R11W:
    case REG_R12W:
    case REG_R13W:
    case REG_R14W:
    case REG_R15W:
      return std::make_pair((WORD_SIZE_BIT - 1), 0);

    case REG_AH:
    case REG_BH:
    case REG_CH:
    case REG_DH:
      return std::make_pair((WORD_SIZE_BIT - 1), BYTE_SIZE_BIT);

    case REG_AL:
    case REG_BL:
    case REG_CL:
    case REG_DL:
    case REG_DIL:
    case REG_SIL:
    case REG_BPL:
    case REG_SPL:
    case REG_R8B:
    case REG_R9B:
    case REG_R10B:
    case REG_R11B:
    case REG_R12B:
    case REG_R13B:
    case REG_R14B:
    case REG_R15B:
      return std::make_pair((BYTE_SIZE_BIT - 1), 0);

    default:
      return std::make_pair(0, 0);
  }
}

#endif /* __x86_64__ */


#if defined(__i386) || defined(_M_IX86)

__uint PINConverter::convertDBIReg2TritonReg(__uint pinRegID) {
  switch(pinRegID){
    case REG_EAX:
    case REG_AX:
    case REG_AH:
    case REG_AL:
      return ID_EAX;

    case REG_EBX:
    case REG_BX:
    case REG_BH:
    case REG_BL:
      return ID_EBX;

    case REG_ECX:
    case REG_CX:
    case REG_CH:
    case REG_CL:
      return ID_ECX;

    case REG_EDX:
    case REG_DX:
    case REG_DH:
    case REG_DL:
      return ID_EDX;

    case REG_EDI:
    case REG_DI:
      return ID_EDI;

    case REG_ESI:
    case REG_SI:
      return ID_ESI;

    case REG_EBP:
    case REG_BP:
      return ID_EBP;

    case REG_ESP:
    case REG_SP:
      return ID_ESP;

    case REG_EIP:
    case REG_IP:
      return ID_EIP;

    case REG_EFLAGS:
      return ID_EFLAGS;

    case REG_XMM0:
      return ID_XMM0;

    case REG_XMM1:
      return ID_XMM1;

    case REG_XMM2:
      return ID_XMM2;

    case REG_XMM3:
      return ID_XMM3;

    case REG_XMM4:
      return ID_XMM4;

    case REG_XMM5:
      return ID_XMM5;

    case REG_XMM6:
      return ID_XMM6;

    case REG_XMM7:
      return ID_XMM7;

    default:
      return ID_INVALID;
  }
}


/* Convert a Triton register to a Pin register.
 * Besides, it can return only 32 bits wised registers.
 */
__uint PINConverter::convertTritonReg2DBIReg(__uint tritonRegId) {
  switch(tritonRegId){
    case ID_EAX:    return REG_EAX;
    case ID_EBX:    return REG_EBX;
    case ID_ECX:    return REG_ECX;
    case ID_EDX:    return REG_EDX;
    case ID_EDI:    return REG_EDI;
    case ID_ESI:    return REG_ESI;
    case ID_EBP:    return REG_EBP;
    case ID_ESP:    return REG_ESP;
    case ID_EIP:    return REG_EIP;
    case ID_EFLAGS: return REG_EFLAGS;
    case ID_XMM0:   return REG_XMM0;
    case ID_XMM1:   return REG_XMM1;
    case ID_XMM2:   return REG_XMM2;
    case ID_XMM3:   return REG_XMM3;
    case ID_XMM4:   return REG_XMM4;
    case ID_XMM5:   return REG_XMM5;
    case ID_XMM6:   return REG_XMM6;
    case ID_XMM7:   return REG_XMM7;
    default:
      return REG_INVALID_;
  }
}


/* Convert a Triton register to a string.
 * Besides, it can return only 64 bits wised registers.
 */
std::string PINConverter::getRegisterName(__uint tritonRegId) {
  switch(tritonRegId){
    case ID_EAX:    return "eax";
    case ID_EBX:    return "ebx";
    case ID_ECX:    return "ecx";
    case ID_EDX:    return "edx";
    case ID_EDI:    return "edi";
    case ID_ESI:    return "esi";
    case ID_EBP:    return "ebp";
    case ID_ESP:    return "esp";
    case ID_EIP:    return "eip";
    case ID_EFLAGS: return "eflags";
    case ID_XMM0:   return "xmm0";
    case ID_XMM1:   return "xmm1";
    case ID_XMM2:   return "xmm2";
    case ID_XMM3:   return "xmm3";
    case ID_XMM4:   return "xmm4";
    case ID_XMM5:   return "xmm5";
    case ID_XMM6:   return "xmm6";
    case ID_XMM7:   return "xmm7";
    case ID_AF:     return "af";
    case ID_CF:     return "cf";
    case ID_DF:     return "df";
    case ID_IF:     return "if";
    case ID_OF:     return "of";
    case ID_PF:     return "pf";
    case ID_SF:     return "sf";
    case ID_TF:     return "tf";
    case ID_ZF:     return "zf";
    default:
      return "invalid";
  }
}


std::pair<__uint, __uint> PINConverter::convertDBIReg2BitsVector(__uint pinRegID) {
  switch(pinRegID) {
    case REG_XMM0:
    case REG_XMM1:
    case REG_XMM2:
    case REG_XMM3:
    case REG_XMM4:
    case REG_XMM5:
    case REG_XMM6:
    case REG_XMM7:
      return std::make_pair((DQWORD_SIZE_BIT - 1), 0);

    case REG_EFLAGS:
      return std::make_pair((DWORD_SIZE_BIT - 1), 0);

    case REG_EAX:
    case REG_EBX:
    case REG_ECX:
    case REG_EDX:
    case REG_EDI:
    case REG_ESI:
    case REG_EBP:
    case REG_ESP:
    case REG_EIP:
      return std::make_pair((DWORD_SIZE_BIT - 1), 0);

    case REG_AX:
    case REG_BX:
    case REG_CX:
    case REG_DX:
    case REG_DI:
    case REG_SI:
    case REG_BP:
    case REG_SP:
    case REG_IP:
      return std::make_pair((WORD_SIZE_BIT - 1), 0);

    case REG_AH:
    case REG_BH:
    case REG_CH:
    case REG_DH:
      return std::make_pair((WORD_SIZE_BIT - 1), BYTE_SIZE_BIT);

    case REG_AL:
    case REG_BL:
    case REG_CL:
    case REG_DL:
      return std::make_pair((BYTE_SIZE_BIT - 1), 0);

    default:
      return std::make_pair(0, 0);
  }
}

#endif /* __i386 */

