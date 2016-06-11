//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_X86SEMANTICS_H
#define TRITON_X86SEMANTICS_H

#include "instruction.hpp"
#include "tritonExport.hpp"



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The Architecture namespace
  namespace arch {
  /*!
   *  \ingroup triton
   *  \addtogroup arch
   *  @{
   */

    //! \module The x86 namespace
    namespace x86 {
    /*!
     *  \ingroup arch
     *  \addtogroup x86
     *  @{
     */

    //! \module The semantics namespace
    namespace semantics {
    /*!
     *  \ingroup x86
     *  \addtogroup semantics
     *  @{
     */

      /* Utils ================================================================================= */

      //! Builds the semantics of the instruction.
      TRITON_EXPORT void build(triton::arch::Instruction& inst);


      /* Semantics ============================================================================= */

      //! Align add stack.
      TRITON_EXPORT void alignAddStack_s(triton::arch::Instruction& inst, triton::uint32 delta);

      //! Align sub stack.
      TRITON_EXPORT void alignSubStack_s(triton::arch::Instruction& inst, triton::uint32 delta);

      //! Clears a flag.
      TRITON_EXPORT void clearFlag_s(triton::arch::Instruction& inst, triton::arch::RegisterOperand& flag, std::string comment="");

      //! Sets a flag.
      TRITON_EXPORT void setFlag_s(triton::arch::Instruction& inst, triton::arch::RegisterOperand& flag, std::string comment="");

      //! Control flow semantics. Used to represent IP.
      TRITON_EXPORT void controlFlow_s(triton::arch::Instruction& inst);

      //! The AF semantics.
      TRITON_EXPORT void af_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, triton::ast::AbstractNode* op2, bool vol=false);

      //! The AF semantics.
      TRITON_EXPORT void afNeg_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, bool vol=false);

      //! The CF semantics.
      TRITON_EXPORT void cfAdd_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, triton::ast::AbstractNode* op2, bool vol=false);

      //! The CF semantics.
      TRITON_EXPORT void cfImul_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, triton::ast::AbstractNode* res, bool vol=false);

      //! The CF semantics.
      TRITON_EXPORT void cfMul_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, bool vol=false);

      //! The CF semantics.
      TRITON_EXPORT void cfNeg_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, bool vol=false);

      //! The CF semantics.
      TRITON_EXPORT void cfPtest_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, bool vol=false);

      //! The CF semantics.
      TRITON_EXPORT void cfRcl_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::ast::AbstractNode* result, triton::ast::AbstractNode* op2, bool vol=false);

      //! The CF semantics.
      TRITON_EXPORT void cfRcr_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* result, triton::ast::AbstractNode* op2, bool vol=false);

      //! The CF semantics.
      TRITON_EXPORT void cfRol_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op2, bool vol=false);

      //! The CF semantics.
      TRITON_EXPORT void cfRor_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op2, bool vol=false);

      //! The CF semantics.
      TRITON_EXPORT void cfSar_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, triton::ast::AbstractNode* op2, bool vol=false);

      //! The CF semantics.
      TRITON_EXPORT void cfShl_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, triton::ast::AbstractNode* op2, bool vol=false);

      //! The CF semantics.
      TRITON_EXPORT void cfShr_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, triton::ast::AbstractNode* op2, bool vol=false);

      //! The CF semantics.
      TRITON_EXPORT void cfSub_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, triton::ast::AbstractNode* op2, bool vol=false);

      //! The OF semantics.
      TRITON_EXPORT void ofAdd_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, triton::ast::AbstractNode* op2, bool vol=false);

      //! The OF semantics.
      TRITON_EXPORT void ofImul_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst,  triton::ast::AbstractNode* op1, triton::ast::AbstractNode* res, bool vol=false);

      //! The OF semantics.
      TRITON_EXPORT void ofMul_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, bool vol=false);

      //! The OF semantics.
      TRITON_EXPORT void ofNeg_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, bool vol=false);

      //! The OF semantics.
      TRITON_EXPORT void ofRol_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op2, bool vol=false);

      //! The OF semantics.
      TRITON_EXPORT void ofRor_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op2, bool vol=false);

      //! The OF semantics.
      TRITON_EXPORT void ofRcr_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, triton::ast::AbstractNode* op2, bool vol=false);

      //! The OF semantics.
      TRITON_EXPORT void ofSar_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op2, bool vol=false);

      //! The OF semantics.
      TRITON_EXPORT void ofShl_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, triton::ast::AbstractNode* op2, bool vol=false);

      //! The OF semantics.
      TRITON_EXPORT void ofShr_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, triton::ast::AbstractNode* op2, bool vol=false);

      //! The OF semantics.
      TRITON_EXPORT void ofSub_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, triton::ast::AbstractNode* op2, bool vol=false);

      //! The PF semantics.
      TRITON_EXPORT void pf_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, bool vol=false);

      //! The PF semantics.
      TRITON_EXPORT void pfShl_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op2, bool vol=false);

      //! The SF semantics.
      TRITON_EXPORT void sf_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, bool vol=false);

      //! The SF semantics.
      TRITON_EXPORT void sfShl_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op2, bool vol=false);

      //! The ZF semantics.
      TRITON_EXPORT void zf_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, bool vol=false);

      //! The ZF semantics.
      TRITON_EXPORT void zfBsf_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& src, triton::ast::AbstractNode* op2, bool vol=false);

      //! The ZF semantics.
      TRITON_EXPORT void zfShl_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op2, bool vol=false);

      //! The ADC semantics.
      TRITON_EXPORT void adc_s(triton::arch::Instruction& inst);

      //! The ADD semantics.
      TRITON_EXPORT void add_s(triton::arch::Instruction& inst);

      //! The AND semantics.
      TRITON_EXPORT void and_s(triton::arch::Instruction& inst);

      //! The ANDNPD semantics.
      TRITON_EXPORT void andnpd_s(triton::arch::Instruction& inst);

      //! The ANDNPS semantics.
      TRITON_EXPORT void andnps_s(triton::arch::Instruction& inst);

      //! The ANDPD semantics.
      TRITON_EXPORT void andpd_s(triton::arch::Instruction& inst);

      //! The ANDPS semantics.
      TRITON_EXPORT void andps_s(triton::arch::Instruction& inst);

      //! The BSF semantics.
      TRITON_EXPORT void bsf_s(triton::arch::Instruction& inst);

      //! The BSR semantics.
      TRITON_EXPORT void bsr_s(triton::arch::Instruction& inst);

      //! The BSWAP semantics.
      TRITON_EXPORT void bswap_s(triton::arch::Instruction& inst);

      //! The BT semantics.
      TRITON_EXPORT void bt_s(triton::arch::Instruction& inst);

      //! The BTC semantics.
      TRITON_EXPORT void btc_s(triton::arch::Instruction& inst);

      //! The BTR semantics.
      TRITON_EXPORT void btr_s(triton::arch::Instruction& inst);

      //! The BTS semantics.
      TRITON_EXPORT void bts_s(triton::arch::Instruction& inst);

      //! The CALL semantics.
      TRITON_EXPORT void call_s(triton::arch::Instruction& inst);

      //! The CBW semantics.
      TRITON_EXPORT void cbw_s(triton::arch::Instruction& inst);

      //! The CDQ semantics.
      TRITON_EXPORT void cdq_s(triton::arch::Instruction& inst);

      //! The CDQE semantics.
      TRITON_EXPORT void cdqe_s(triton::arch::Instruction& inst);

      //! The CLC semantics.
      TRITON_EXPORT void clc_s(triton::arch::Instruction& inst);

      //! The CLD semantics.
      TRITON_EXPORT void cld_s(triton::arch::Instruction& inst);

      //! The CLTS semantics.
      TRITON_EXPORT void clts_s(triton::arch::Instruction& inst);

      //! The CMC semantics.
      TRITON_EXPORT void cmc_s(triton::arch::Instruction& inst);

      //! The CMOVA semantics.
      TRITON_EXPORT void cmova_s(triton::arch::Instruction& inst);

      //! The CMOVAE semantics.
      TRITON_EXPORT void cmovae_s(triton::arch::Instruction& inst);

      //! The CMOVB semantics.
      TRITON_EXPORT void cmovb_s(triton::arch::Instruction& inst);

      //! The CMOVBE semantics.
      TRITON_EXPORT void cmovbe_s(triton::arch::Instruction& inst);

      //! The CMOVE semantics.
      TRITON_EXPORT void cmove_s(triton::arch::Instruction& inst);

      //! The CMOVG semantics.
      TRITON_EXPORT void cmovg_s(triton::arch::Instruction& inst);

      //! The CMOVGE semantics.
      TRITON_EXPORT void cmovge_s(triton::arch::Instruction& inst);

      //! The CMOVL semantics.
      TRITON_EXPORT void cmovl_s(triton::arch::Instruction& inst);

      //! The CMOVLE semantics.
      TRITON_EXPORT void cmovle_s(triton::arch::Instruction& inst);

      //! The CMOVNE semantics.
      TRITON_EXPORT void cmovne_s(triton::arch::Instruction& inst);

      //! The CMOVNO semantics.
      TRITON_EXPORT void cmovno_s(triton::arch::Instruction& inst);

      //! The CMOVNP semantics.
      TRITON_EXPORT void cmovnp_s(triton::arch::Instruction& inst);

      //! The CMOVNS semantics.
      TRITON_EXPORT void cmovns_s(triton::arch::Instruction& inst);

      //! The CMOVO semantics.
      TRITON_EXPORT void cmovo_s(triton::arch::Instruction& inst);

      //! The CMOVP semantics.
      TRITON_EXPORT void cmovp_s(triton::arch::Instruction& inst);

      //! The CMOVS semantics.
      TRITON_EXPORT void cmovs_s(triton::arch::Instruction& inst);

      //! The CMP semantics.
      TRITON_EXPORT void cmp_s(triton::arch::Instruction& inst);

      //! The CMPSB semantics.
      TRITON_EXPORT void cmpsb_s(triton::arch::Instruction& inst);

      //! The CMPSD semantics.
      TRITON_EXPORT void cmpsd_s(triton::arch::Instruction& inst);

      //! The CMPSQ semantics.
      TRITON_EXPORT void cmpsq_s(triton::arch::Instruction& inst);

      //! The CMPSW semantics.
      TRITON_EXPORT void cmpsw_s(triton::arch::Instruction& inst);

      //! The CMPXCHG semantics.
      TRITON_EXPORT void cmpxchg_s(triton::arch::Instruction& inst);

      //! The CMPXCHG16B semantics.
      TRITON_EXPORT void cmpxchg16b_s(triton::arch::Instruction& inst);

      //! The CMPXCHG8B semantics.
      TRITON_EXPORT void cmpxchg8b_s(triton::arch::Instruction& inst);

      //! The CPUID semantics.
      TRITON_EXPORT void cpuid_s(triton::arch::Instruction& inst);

      //! The CQO semantics.
      TRITON_EXPORT void cqo_s(triton::arch::Instruction& inst);

      //! The CWD semantics.
      TRITON_EXPORT void cwd_s(triton::arch::Instruction& inst);

      //! The CWDE semantics.
      TRITON_EXPORT void cwde_s(triton::arch::Instruction& inst);

      //! The DEC semantics.
      TRITON_EXPORT void dec_s(triton::arch::Instruction& inst);

      //! The DIV semantics.
      TRITON_EXPORT void div_s(triton::arch::Instruction& inst);

      //! The EXTRACTPS semantics.
      TRITON_EXPORT void extractps_s(triton::arch::Instruction& inst);

      //! The IDIV semantics.
      TRITON_EXPORT void idiv_s(triton::arch::Instruction& inst);

      //! The IMUL semantics.
      TRITON_EXPORT void imul_s(triton::arch::Instruction& inst);

      //! The INC semantics.
      TRITON_EXPORT void inc_s(triton::arch::Instruction& inst);

      //! The JA semantics.
      TRITON_EXPORT void ja_s(triton::arch::Instruction& inst);

      //! The JAE semantics.
      TRITON_EXPORT void jae_s(triton::arch::Instruction& inst);

      //! The JB semantics.
      TRITON_EXPORT void jb_s(triton::arch::Instruction& inst);

      //! The JBE semantics.
      TRITON_EXPORT void jbe_s(triton::arch::Instruction& inst);

      //! The JE semantics.
      TRITON_EXPORT void je_s(triton::arch::Instruction& inst);

      //! The JG semantics.
      TRITON_EXPORT void jg_s(triton::arch::Instruction& inst);

      //! The JGE semantics.
      TRITON_EXPORT void jge_s(triton::arch::Instruction& inst);

      //! The JL semantics.
      TRITON_EXPORT void jl_s(triton::arch::Instruction& inst);

      //! The JLE semantics.
      TRITON_EXPORT void jle_s(triton::arch::Instruction& inst);

      //! The JMP semantics.
      TRITON_EXPORT void jmp_s(triton::arch::Instruction& inst);

      //! The JNE semantics.
      TRITON_EXPORT void jne_s(triton::arch::Instruction& inst);

      //! The JNO semantics.
      TRITON_EXPORT void jno_s(triton::arch::Instruction& inst);

      //! The JNP semantics.
      TRITON_EXPORT void jnp_s(triton::arch::Instruction& inst);

      //! The JNS semantics.
      TRITON_EXPORT void jns_s(triton::arch::Instruction& inst);

      //! The JO semantics.
      TRITON_EXPORT void jo_s(triton::arch::Instruction& inst);

      //! The JP semantics.
      TRITON_EXPORT void jp_s(triton::arch::Instruction& inst);

      //! The JS semantics.
      TRITON_EXPORT void js_s(triton::arch::Instruction& inst);

      //! The LAHF semantics.
      TRITON_EXPORT void lahf_s(triton::arch::Instruction& inst);

      //! The LDDQU semantics.
      TRITON_EXPORT void lddqu_s(triton::arch::Instruction& inst);

      //! The LDMXCSR semantics.
      TRITON_EXPORT void ldmxcsr_s(triton::arch::Instruction& inst);

      //! The LEA semantics.
      TRITON_EXPORT void lea_s(triton::arch::Instruction& inst);

      //! The LEAVE semantics.
      TRITON_EXPORT void leave_s(triton::arch::Instruction& inst);

      //! The LODSB semantics.
      TRITON_EXPORT void lodsb_s(triton::arch::Instruction& inst);

      //! The LODSD semantics.
      TRITON_EXPORT void lodsd_s(triton::arch::Instruction& inst);

      //! The LODSQ semantics.
      TRITON_EXPORT void lodsq_s(triton::arch::Instruction& inst);

      //! The LODSW semantics.
      TRITON_EXPORT void lodsw_s(triton::arch::Instruction& inst);

      //! The MOV semantics.
      TRITON_EXPORT void mov_s(triton::arch::Instruction& inst);

      //! The MOVABS semantics.
      TRITON_EXPORT void movabs_s(triton::arch::Instruction& inst);

      //! The MOVAPD semantics.
      TRITON_EXPORT void movapd_s(triton::arch::Instruction& inst);

      //! The MOVAPS semantics.
      TRITON_EXPORT void movaps_s(triton::arch::Instruction& inst);

      //! The MOVD semantics.
      TRITON_EXPORT void movd_s(triton::arch::Instruction& inst);

      //! The MOVDDUP semantics.
      TRITON_EXPORT void movddup_s(triton::arch::Instruction& inst);

      //! The MOVDQ2Q semantics.
      TRITON_EXPORT void movdq2q_s(triton::arch::Instruction& inst);

      //! The MOVDQA semantics.
      TRITON_EXPORT void movdqa_s(triton::arch::Instruction& inst);

      //! The MOVDQU semantics.
      TRITON_EXPORT void movdqu_s(triton::arch::Instruction& inst);

      //! The MOVHLPS semantics.
      TRITON_EXPORT void movhlps_s(triton::arch::Instruction& inst);

      //! The MOVHPD semantics.
      TRITON_EXPORT void movhpd_s(triton::arch::Instruction& inst);

      //! The MOVHPS semantics.
      TRITON_EXPORT void movhps_s(triton::arch::Instruction& inst);

      //! The MOVLHPS semantics.
      TRITON_EXPORT void movlhps_s(triton::arch::Instruction& inst);

      //! The MOVLPD semantics.
      TRITON_EXPORT void movlpd_s(triton::arch::Instruction& inst);

      //! The MOVLPS semantics.
      TRITON_EXPORT void movlps_s(triton::arch::Instruction& inst);

      //! The MOVMSKPD semantics.
      TRITON_EXPORT void movmskpd_s(triton::arch::Instruction& inst);

      //! The MOVMSKPS semantics.
      TRITON_EXPORT void movmskps_s(triton::arch::Instruction& inst);

      //! The MOVNTDQ semantics.
      TRITON_EXPORT void movntdq_s(triton::arch::Instruction& inst);

      //! The MOVNTI semantics.
      TRITON_EXPORT void movnti_s(triton::arch::Instruction& inst);

      //! The MOVNTPD semantics.
      TRITON_EXPORT void movntpd_s(triton::arch::Instruction& inst);

      //! The MOVNTPS semantics.
      TRITON_EXPORT void movntps_s(triton::arch::Instruction& inst);

      //! The MOVNTQ semantics.
      TRITON_EXPORT void movntq_s(triton::arch::Instruction& inst);

      //! The MOVSHDUP semantics.
      TRITON_EXPORT void movshdup_s(triton::arch::Instruction& inst);

      //! The MOVSLDUP semantics.
      TRITON_EXPORT void movsldup_s(triton::arch::Instruction& inst);

      //! The MOVQ semantics.
      TRITON_EXPORT void movq_s(triton::arch::Instruction& inst);

      //! The MOVQ2DQ semantics.
      TRITON_EXPORT void movq2dq_s(triton::arch::Instruction& inst);

      //! The MOVSB semantics.
      TRITON_EXPORT void movsb_s(triton::arch::Instruction& inst);

      //! The MOVSD semantics.
      TRITON_EXPORT void movsd_s(triton::arch::Instruction& inst);

      //! The MOVUPD semantics.
      TRITON_EXPORT void movupd_s(triton::arch::Instruction& inst);

      //! The MOVUPS semantics.
      TRITON_EXPORT void movups_s(triton::arch::Instruction& inst);

      //! The MOVSQ semantics.
      TRITON_EXPORT void movsq_s(triton::arch::Instruction& inst);

      //! The MOVSW semantics.
      TRITON_EXPORT void movsw_s(triton::arch::Instruction& inst);

      //! The MOVSX semantics.
      TRITON_EXPORT void movsx_s(triton::arch::Instruction& inst);

      //! The MOVSXD semantics.
      TRITON_EXPORT void movsxd_s(triton::arch::Instruction& inst);

      //! The MOVZX semantics.
      TRITON_EXPORT void movzx_s(triton::arch::Instruction& inst);

      //! The MUL semantics.
      TRITON_EXPORT void mul_s(triton::arch::Instruction& inst);

      //! The NEG semantics.
      TRITON_EXPORT void neg_s(triton::arch::Instruction& inst);

      //! The NOP semantics.
      TRITON_EXPORT void nop_s(triton::arch::Instruction& inst);

      //! The NOT semantics.
      TRITON_EXPORT void not_s(triton::arch::Instruction& inst);

      //! The OR semantics.
      TRITON_EXPORT void or_s(triton::arch::Instruction& inst);

      //! The ORPD semantics.
      TRITON_EXPORT void orpd_s(triton::arch::Instruction& inst);

      //! The ORPS semantics.
      TRITON_EXPORT void orps_s(triton::arch::Instruction& inst);

      //! The PADDB semantics.
      TRITON_EXPORT void paddb_s(triton::arch::Instruction& inst);

      //! The PADDD semantics.
      TRITON_EXPORT void paddd_s(triton::arch::Instruction& inst);

      //! The PADDQ semantics.
      TRITON_EXPORT void paddq_s(triton::arch::Instruction& inst);

      //! The PADDW semantics.
      TRITON_EXPORT void paddw_s(triton::arch::Instruction& inst);

      //! The PAND semantics.
      TRITON_EXPORT void pand_s(triton::arch::Instruction& inst);

      //! The PANDN semantics.
      TRITON_EXPORT void pandn_s(triton::arch::Instruction& inst);

      //! The PAVGB semantics.
      TRITON_EXPORT void pavgb_s(triton::arch::Instruction& inst);

      //! The PAVGW semantics.
      TRITON_EXPORT void pavgw_s(triton::arch::Instruction& inst);

      //! The PCMPEQB semantics.
      TRITON_EXPORT void pcmpeqb_s(triton::arch::Instruction& inst);

      //! The PCMPEQD semantics.
      TRITON_EXPORT void pcmpeqd_s(triton::arch::Instruction& inst);

      //! The PCMPEQW semantics.
      TRITON_EXPORT void pcmpeqw_s(triton::arch::Instruction& inst);

      //! The PCMPGTB semantics.
      TRITON_EXPORT void pcmpgtb_s(triton::arch::Instruction& inst);

      //! The PCMPGTD semantics.
      TRITON_EXPORT void pcmpgtd_s(triton::arch::Instruction& inst);

      //! The PCMPGTW semantics.
      TRITON_EXPORT void pcmpgtw_s(triton::arch::Instruction& inst);

      //! The PMAXSB semantics.
      TRITON_EXPORT void pmaxsb_s(triton::arch::Instruction& inst);

      //! The PMAXSD semantics.
      TRITON_EXPORT void pmaxsd_s(triton::arch::Instruction& inst);

      //! The PMAXSW semantics.
      TRITON_EXPORT void pmaxsw_s(triton::arch::Instruction& inst);

      //! The PMAXUB semantics.
      TRITON_EXPORT void pmaxub_s(triton::arch::Instruction& inst);

      //! The PMAXUD semantics.
      TRITON_EXPORT void pmaxud_s(triton::arch::Instruction& inst);

      //! The PMAXUW semantics.
      TRITON_EXPORT void pmaxuw_s(triton::arch::Instruction& inst);

      //! The PMINSB semantics.
      TRITON_EXPORT void pminsb_s(triton::arch::Instruction& inst);

      //! The PMINSD semantics.
      TRITON_EXPORT void pminsd_s(triton::arch::Instruction& inst);

      //! The PMINSW semantics.
      TRITON_EXPORT void pminsw_s(triton::arch::Instruction& inst);

      //! The PMINUB semantics.
      TRITON_EXPORT void pminub_s(triton::arch::Instruction& inst);

      //! The PMINUD semantics.
      TRITON_EXPORT void pminud_s(triton::arch::Instruction& inst);

      //! The PMINUW semantics.
      TRITON_EXPORT void pminuw_s(triton::arch::Instruction& inst);

      //! The PMOVMSKB semantics.
      TRITON_EXPORT void pmovmskb_s(triton::arch::Instruction& inst);

      //! The PMOVSXBD semantics.
      TRITON_EXPORT void pmovsxbd_s(triton::arch::Instruction& inst);

      //! The PMOVSXBQ semantics.
      TRITON_EXPORT void pmovsxbq_s(triton::arch::Instruction& inst);

      //! The PMOVSXBW semantics.
      TRITON_EXPORT void pmovsxbw_s(triton::arch::Instruction& inst);

      //! The PMOVSXDQ semantics.
      TRITON_EXPORT void pmovsxdq_s(triton::arch::Instruction& inst);

      //! The PMOVSXWD semantics.
      TRITON_EXPORT void pmovsxwd_s(triton::arch::Instruction& inst);

      //! The PMOVSXWQ semantics.
      TRITON_EXPORT void pmovsxwq_s(triton::arch::Instruction& inst);

      //! The PMOVZXBD semantics.
      TRITON_EXPORT void pmovzxbd_s(triton::arch::Instruction& inst);

      //! The PMOVZXBQ semantics.
      TRITON_EXPORT void pmovzxbq_s(triton::arch::Instruction& inst);

      //! The PMOVZXBW semantics.
      TRITON_EXPORT void pmovzxbw_s(triton::arch::Instruction& inst);

      //! The PMOVZXDQ semantics.
      TRITON_EXPORT void pmovzxdq_s(triton::arch::Instruction& inst);

      //! The PMOVZXWD semantics.
      TRITON_EXPORT void pmovzxwd_s(triton::arch::Instruction& inst);

      //! The PMOVZXWQ semantics.
      TRITON_EXPORT void pmovzxwq_s(triton::arch::Instruction& inst);

      //! The POP semantics.
      TRITON_EXPORT void pop_s(triton::arch::Instruction& inst);

      //! The POPAL semantics.
      TRITON_EXPORT void popal_s(triton::arch::Instruction& inst);

      //! The POPFD semantics.
      TRITON_EXPORT void popfd_s(triton::arch::Instruction& inst);

      //! The POPFQ semantics.
      TRITON_EXPORT void popfq_s(triton::arch::Instruction& inst);

      //! The POR semantics.
      TRITON_EXPORT void por_s(triton::arch::Instruction& inst);

      //! The PREFETCHx semantics.
      TRITON_EXPORT void prefetchx_s(triton::arch::Instruction& inst);

      //! The PSHUFD semantics.
      TRITON_EXPORT void pshufd_s(triton::arch::Instruction& inst);

      //! The PSHUFHW semantics.
      TRITON_EXPORT void pshufhw_s(triton::arch::Instruction& inst);

      //! The PSHUFLW semantics.
      TRITON_EXPORT void pshuflw_s(triton::arch::Instruction& inst);

      //! The PSHUFW semantics.
      TRITON_EXPORT void pshufw_s(triton::arch::Instruction& inst);

      //! The PSLLDQ semantics.
      TRITON_EXPORT void pslldq_s(triton::arch::Instruction& inst);

      //! The PSRLDQ semantics.
      TRITON_EXPORT void psrldq_s(triton::arch::Instruction& inst);

      //! The PSUBB semantics.
      TRITON_EXPORT void psubb_s(triton::arch::Instruction& inst);

      //! The PSUBD semantics.
      TRITON_EXPORT void psubd_s(triton::arch::Instruction& inst);

      //! The PSUBQ semantics.
      TRITON_EXPORT void psubq_s(triton::arch::Instruction& inst);

      //! The PSUBW semantics.
      TRITON_EXPORT void psubw_s(triton::arch::Instruction& inst);

      //! The PTEST semantics.
      TRITON_EXPORT void ptest_s(triton::arch::Instruction& inst);

      //! The PUNPCKHBW semantics.
      TRITON_EXPORT void punpckhbw_s(triton::arch::Instruction& inst);

      //! The PUNPCKHDQ semantics.
      TRITON_EXPORT void punpckhdq_s(triton::arch::Instruction& inst);

      //! The PUNPCKHQDQ semantics.
      TRITON_EXPORT void punpckhqdq_s(triton::arch::Instruction& inst);

      //! The PUNPCKHWD semantics.
      TRITON_EXPORT void punpckhwd_s(triton::arch::Instruction& inst);

      //! The PUNPCKLBW semantics.
      TRITON_EXPORT void punpcklbw_s(triton::arch::Instruction& inst);

      //! The PUNPCKLDQ semantics.
      TRITON_EXPORT void punpckldq_s(triton::arch::Instruction& inst);

      //! The PUNPCKLQDQ semantics.
      TRITON_EXPORT void punpcklqdq_s(triton::arch::Instruction& inst);

      //! The PUNPCKLWD semantics.
      TRITON_EXPORT void punpcklwd_s(triton::arch::Instruction& inst);

      //! The PUSH semantics.
      TRITON_EXPORT void push_s(triton::arch::Instruction& inst);

      //! The PUSHAL semantics.
      TRITON_EXPORT void pushal_s(triton::arch::Instruction& inst);

      //! The PUSHFD semantics.
      TRITON_EXPORT void pushfd_s(triton::arch::Instruction& inst);

      //! The PUSHFQ semantics.
      TRITON_EXPORT void pushfq_s(triton::arch::Instruction& inst);

      //! The PXOR semantics.
      TRITON_EXPORT void pxor_s(triton::arch::Instruction& inst);

      //! The RCL semantics.
      TRITON_EXPORT void rcl_s(triton::arch::Instruction& inst);

      //! The RCR semantics.
      TRITON_EXPORT void rcr_s(triton::arch::Instruction& inst);

      //! The RDTSC semantics.
      TRITON_EXPORT void rdtsc_s(triton::arch::Instruction& inst);

      //! The RET semantics.
      TRITON_EXPORT void ret_s(triton::arch::Instruction& inst);

      //! The ROL semantics.
      TRITON_EXPORT void rol_s(triton::arch::Instruction& inst);

      //! The ROR semantics.
      TRITON_EXPORT void ror_s(triton::arch::Instruction& inst);

      //! The SAHF semantics.
      TRITON_EXPORT void sahf_s(triton::arch::Instruction& inst);

      //! The SAR semantics.
      TRITON_EXPORT void sar_s(triton::arch::Instruction& inst);

      //! The SBB semantics.
      TRITON_EXPORT void sbb_s(triton::arch::Instruction& inst);

      //! The SCASB semantics.
      TRITON_EXPORT void scasb_s(triton::arch::Instruction& inst);

      //! The SCASD semantics.
      TRITON_EXPORT void scasd_s(triton::arch::Instruction& inst);

      //! The SCASQ semantics.
      TRITON_EXPORT void scasq_s(triton::arch::Instruction& inst);

      //! The SCASW semantics.
      TRITON_EXPORT void scasw_s(triton::arch::Instruction& inst);

      //! The SETA semantics.
      TRITON_EXPORT void seta_s(triton::arch::Instruction& inst);

      //! The SETAE semantics.
      TRITON_EXPORT void setae_s(triton::arch::Instruction& inst);

      //! The SETB semantics.
      TRITON_EXPORT void setb_s(triton::arch::Instruction& inst);

      //! The SETBE semantics.
      TRITON_EXPORT void setbe_s(triton::arch::Instruction& inst);

      //! The SETE semantics.
      TRITON_EXPORT void sete_s(triton::arch::Instruction& inst);

      //! The SETG: semantics.
      TRITON_EXPORT void setg_s(triton::arch::Instruction& inst);

      //! The SETGE semantics.
      TRITON_EXPORT void setge_s(triton::arch::Instruction& inst);

      //! The SETL semantics.
      TRITON_EXPORT void setl_s(triton::arch::Instruction& inst);

      //! The SETLE semantics.
      TRITON_EXPORT void setle_s(triton::arch::Instruction& inst);

      //! The SETNE semantics.
      TRITON_EXPORT void setne_s(triton::arch::Instruction& inst);

      //! The SETNO semantics.
      TRITON_EXPORT void setno_s(triton::arch::Instruction& inst);

      //! The SETNP semantics.
      TRITON_EXPORT void setnp_s(triton::arch::Instruction& inst);

      //! The SETNS semantics.
      TRITON_EXPORT void setns_s(triton::arch::Instruction& inst);

      //! The SETO semantics.
      TRITON_EXPORT void seto_s(triton::arch::Instruction& inst);

      //! The SETP semantics.
      TRITON_EXPORT void setp_s(triton::arch::Instruction& inst);

      //! The SETS semantics.
      TRITON_EXPORT void sets_s(triton::arch::Instruction& inst);

      //! The SHL semantics.
      TRITON_EXPORT void shl_s(triton::arch::Instruction& inst);

      //! The SHR semantics.
      TRITON_EXPORT void shr_s(triton::arch::Instruction& inst);

      //! The STC semantics.
      TRITON_EXPORT void stc_s(triton::arch::Instruction& inst);

      //! The STD semantics.
      TRITON_EXPORT void std_s(triton::arch::Instruction& inst);

      //! The STMXCSR semantics.
      TRITON_EXPORT void stmxcsr_s(triton::arch::Instruction& inst);

      //! The STOSB semantics.
      TRITON_EXPORT void stosb_s(triton::arch::Instruction& inst);

      //! The STOSD semantics.
      TRITON_EXPORT void stosd_s(triton::arch::Instruction& inst);

      //! The STOSQ semantics.
      TRITON_EXPORT void stosq_s(triton::arch::Instruction& inst);

      //! The STOSW semantics.
      TRITON_EXPORT void stosw_s(triton::arch::Instruction& inst);

      //! The SUB semantics.
      TRITON_EXPORT void sub_s(triton::arch::Instruction& inst);

      //! The SYSCALL semantics.
      TRITON_EXPORT void syscall_s(triton::arch::Instruction& inst);

      //! The TEST semantics.
      TRITON_EXPORT void test_s(triton::arch::Instruction& inst);

      //! The UNPCKHPD semantics.
      TRITON_EXPORT void unpckhpd_s(triton::arch::Instruction& inst);

      //! The UNPCKHPS semantics.
      TRITON_EXPORT void unpckhps_s(triton::arch::Instruction& inst);

      //! The UNPCKLPD semantics.
      TRITON_EXPORT void unpcklpd_s(triton::arch::Instruction& inst);

      //! The UNPCKLPS semantics.
      TRITON_EXPORT void unpcklps_s(triton::arch::Instruction& inst);

      //! The VMOVDQA semantics.
      TRITON_EXPORT void vmovdqa_s(triton::arch::Instruction& inst);

      //! The VPAND semantics.
      TRITON_EXPORT void vpand_s(triton::arch::Instruction& inst);

      //! The VPANDN semantics.
      TRITON_EXPORT void vpandn_s(triton::arch::Instruction& inst);

      //! The VPOR semantics.
      TRITON_EXPORT void vpor_s(triton::arch::Instruction& inst);

      //! The VPSHUFD semantics.
      TRITON_EXPORT void vpshufd_s(triton::arch::Instruction& inst);

      //! The VPTEST semantics.
      TRITON_EXPORT void vptest_s(triton::arch::Instruction& inst);

      //! The VPXOR semantics.
      TRITON_EXPORT void vpxor_s(triton::arch::Instruction& inst);

      //! The XADD semantics.
      TRITON_EXPORT void xadd_s(triton::arch::Instruction& inst);

      //! The XCHG semantics.
      TRITON_EXPORT void xchg_s(triton::arch::Instruction& inst);

      //! The XOR semantics.
      TRITON_EXPORT void xor_s(triton::arch::Instruction& inst);

      //! The XORPD semantics.
      TRITON_EXPORT void xorpd_s(triton::arch::Instruction& inst);

      //! The XORPS semantics.
      TRITON_EXPORT void xorps_s(triton::arch::Instruction& inst);

      /*! @} End of semantics namespace */
      };
    /*! @} End of x86 namespace */
    };
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};


#endif /* TRITON_X86SEMANTICS_H */
