/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <TmpReg.h>

/*
 * Inside semantics, sometime we have to use references to registers.
 * ID_TMP_RAX, ID_TMP_RBX, ..., ID_TMP_AF, ... are now available for
 * an access to RegisterOperand temporary class.
 */

#if defined(__x86_64__) || defined(_M_X64)
RegisterOperand tmp_reg_rax    = createTmpReg(ID_RAX,     REG_SIZE);
RegisterOperand tmp_reg_rbx    = createTmpReg(ID_RBX,     REG_SIZE);
RegisterOperand tmp_reg_rcx    = createTmpReg(ID_RCX,     REG_SIZE);
RegisterOperand tmp_reg_rdx    = createTmpReg(ID_RDX,     REG_SIZE);
RegisterOperand tmp_reg_rdi    = createTmpReg(ID_RDI,     REG_SIZE);
RegisterOperand tmp_reg_rsi    = createTmpReg(ID_RSI,     REG_SIZE);
RegisterOperand tmp_reg_rsp    = createTmpReg(ID_RSP,     REG_SIZE);
RegisterOperand tmp_reg_rbp    = createTmpReg(ID_RBP,     REG_SIZE);
RegisterOperand tmp_reg_rip    = createTmpReg(ID_RIP,     REG_SIZE);
RegisterOperand tmp_reg_rflags = createTmpReg(ID_RFLAGS,  DWORD_SIZE);
RegisterOperand tmp_reg_r8     = createTmpReg(ID_R8,      REG_SIZE);
RegisterOperand tmp_reg_r9     = createTmpReg(ID_R9,      REG_SIZE);
RegisterOperand tmp_reg_r10    = createTmpReg(ID_R10,     REG_SIZE);
RegisterOperand tmp_reg_r11    = createTmpReg(ID_R11,     REG_SIZE);
RegisterOperand tmp_reg_r12    = createTmpReg(ID_R12,     REG_SIZE);
RegisterOperand tmp_reg_r13    = createTmpReg(ID_R13,     REG_SIZE);
RegisterOperand tmp_reg_r14    = createTmpReg(ID_R14,     REG_SIZE);
RegisterOperand tmp_reg_r15    = createTmpReg(ID_R15,     REG_SIZE);
RegisterOperand tmp_reg_xmm8   = createTmpReg(ID_XMM8,    SSE_REG_SIZE);
RegisterOperand tmp_reg_xmm9   = createTmpReg(ID_XMM9,    SSE_REG_SIZE);
RegisterOperand tmp_reg_xmm10  = createTmpReg(ID_XMM10,   SSE_REG_SIZE);
RegisterOperand tmp_reg_xmm11  = createTmpReg(ID_XMM11,   SSE_REG_SIZE);
RegisterOperand tmp_reg_xmm12  = createTmpReg(ID_XMM12,   SSE_REG_SIZE);
RegisterOperand tmp_reg_xmm13  = createTmpReg(ID_XMM13,   SSE_REG_SIZE);
RegisterOperand tmp_reg_xmm14  = createTmpReg(ID_XMM14,   SSE_REG_SIZE);
RegisterOperand tmp_reg_xmm15  = createTmpReg(ID_XMM15,   SSE_REG_SIZE);
#endif


#if defined(__i386) || defined(_M_IX86)
RegisterOperand tmp_reg_eax    = createTmpReg(ID_EAX,     REG_SIZE);
RegisterOperand tmp_reg_ebx    = createTmpReg(ID_EBX,     REG_SIZE);
RegisterOperand tmp_reg_ecx    = createTmpReg(ID_ECX,     REG_SIZE);
RegisterOperand tmp_reg_edx    = createTmpReg(ID_EDX,     REG_SIZE);
RegisterOperand tmp_reg_edi    = createTmpReg(ID_EDI,     REG_SIZE);
RegisterOperand tmp_reg_esi    = createTmpReg(ID_ESI,     REG_SIZE);
RegisterOperand tmp_reg_esp    = createTmpReg(ID_ESP,     REG_SIZE);
RegisterOperand tmp_reg_ebp    = createTmpReg(ID_EBP,     REG_SIZE);
RegisterOperand tmp_reg_eip    = createTmpReg(ID_EIP,     REG_SIZE);
RegisterOperand tmp_reg_eflags = createTmpReg(ID_EFLAGS,  DWORD_SIZE);
#endif


RegisterOperand tmp_reg_xmm0   = createTmpReg(ID_XMM0, SSE_REG_SIZE);
RegisterOperand tmp_reg_xmm1   = createTmpReg(ID_XMM1, SSE_REG_SIZE);
RegisterOperand tmp_reg_xmm2   = createTmpReg(ID_XMM2, SSE_REG_SIZE);
RegisterOperand tmp_reg_xmm3   = createTmpReg(ID_XMM3, SSE_REG_SIZE);
RegisterOperand tmp_reg_xmm4   = createTmpReg(ID_XMM4, SSE_REG_SIZE);
RegisterOperand tmp_reg_xmm5   = createTmpReg(ID_XMM5, SSE_REG_SIZE);
RegisterOperand tmp_reg_xmm6   = createTmpReg(ID_XMM6, SSE_REG_SIZE);
RegisterOperand tmp_reg_xmm7   = createTmpReg(ID_XMM7, SSE_REG_SIZE);


RegisterOperand tmp_flag_af    = createTmpFlag(ID_AF);
RegisterOperand tmp_flag_cf    = createTmpFlag(ID_CF);
RegisterOperand tmp_flag_df    = createTmpFlag(ID_DF);
RegisterOperand tmp_flag_if    = createTmpFlag(ID_IF);
RegisterOperand tmp_flag_of    = createTmpFlag(ID_OF);
RegisterOperand tmp_flag_pf    = createTmpFlag(ID_PF);
RegisterOperand tmp_flag_sf    = createTmpFlag(ID_SF);
RegisterOperand tmp_flag_tf    = createTmpFlag(ID_TF);
RegisterOperand tmp_flag_zf    = createTmpFlag(ID_ZF);


RegisterOperand createTmpReg(__uint tritonRegId, __uint size) {
  if (isFlagId(tritonRegId))
    return createTmpFlag(tritonRegId);
  return RegisterOperand(PINConverter::convertTritonReg2DBIReg(tritonRegId), size);
}


RegisterOperand createTmpFlag(__uint flagId, __uint size) {
  RegisterOperand reg;
  reg.setTritonRegId(flagId);
  reg.setSize(size);
  return reg;
}

