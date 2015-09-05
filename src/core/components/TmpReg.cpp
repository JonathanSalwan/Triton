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

RegisterOperand tmp_reg_rax    = createTmpReg(ID_RAX);
RegisterOperand tmp_reg_rbx    = createTmpReg(ID_RBX);
RegisterOperand tmp_reg_rcx    = createTmpReg(ID_RCX);
RegisterOperand tmp_reg_rdx    = createTmpReg(ID_RDX);
RegisterOperand tmp_reg_rdi    = createTmpReg(ID_RDI);
RegisterOperand tmp_reg_rsi    = createTmpReg(ID_RSI);
RegisterOperand tmp_reg_rsp    = createTmpReg(ID_RSP);
RegisterOperand tmp_reg_rbp    = createTmpReg(ID_RBP);
RegisterOperand tmp_reg_rip    = createTmpReg(ID_RIP);
RegisterOperand tmp_reg_r8     = createTmpReg(ID_R8);
RegisterOperand tmp_reg_r9     = createTmpReg(ID_R9);
RegisterOperand tmp_reg_r10    = createTmpReg(ID_R10);
RegisterOperand tmp_reg_r11    = createTmpReg(ID_R11);
RegisterOperand tmp_reg_r12    = createTmpReg(ID_R12);
RegisterOperand tmp_reg_r13    = createTmpReg(ID_R13);
RegisterOperand tmp_reg_r14    = createTmpReg(ID_R14);
RegisterOperand tmp_reg_r15    = createTmpReg(ID_R15);
RegisterOperand tmp_reg_xmm0   = createTmpReg(ID_XMM0);
RegisterOperand tmp_reg_xmm1   = createTmpReg(ID_XMM1);
RegisterOperand tmp_reg_xmm2   = createTmpReg(ID_XMM2);
RegisterOperand tmp_reg_xmm3   = createTmpReg(ID_XMM3);
RegisterOperand tmp_reg_xmm4   = createTmpReg(ID_XMM4);
RegisterOperand tmp_reg_xmm5   = createTmpReg(ID_XMM5);
RegisterOperand tmp_reg_xmm6   = createTmpReg(ID_XMM6);
RegisterOperand tmp_reg_xmm7   = createTmpReg(ID_XMM7);
RegisterOperand tmp_reg_xmm8   = createTmpReg(ID_XMM8);
RegisterOperand tmp_reg_xmm9   = createTmpReg(ID_XMM9);
RegisterOperand tmp_reg_xmm10  = createTmpReg(ID_XMM10);
RegisterOperand tmp_reg_xmm11  = createTmpReg(ID_XMM11);
RegisterOperand tmp_reg_xmm12  = createTmpReg(ID_XMM12);
RegisterOperand tmp_reg_xmm13  = createTmpReg(ID_XMM13);
RegisterOperand tmp_reg_xmm14  = createTmpReg(ID_XMM14);
RegisterOperand tmp_reg_xmm15  = createTmpReg(ID_XMM15);
RegisterOperand tmp_reg_rflags = createTmpReg(ID_RFLAGS);
RegisterOperand tmp_flag_af    = createTmpFlag(ID_AF);
RegisterOperand tmp_flag_cf    = createTmpFlag(ID_CF);
RegisterOperand tmp_flag_df    = createTmpFlag(ID_DF);
RegisterOperand tmp_flag_if    = createTmpFlag(ID_IF);
RegisterOperand tmp_flag_of    = createTmpFlag(ID_OF);
RegisterOperand tmp_flag_pf    = createTmpFlag(ID_PF);
RegisterOperand tmp_flag_sf    = createTmpFlag(ID_SF);
RegisterOperand tmp_flag_tf    = createTmpFlag(ID_TF);
RegisterOperand tmp_flag_zf    = createTmpFlag(ID_ZF);


RegisterOperand createTmpReg(uint64 tritonRegId) {
  return RegisterOperand(PINConverter::convertTritonReg2DBIReg(tritonRegId));
}


RegisterOperand createTmpFlag(uint64 flagId) {
  RegisterOperand reg;
  reg.setTritonRegId(flagId);
  return reg;
}

