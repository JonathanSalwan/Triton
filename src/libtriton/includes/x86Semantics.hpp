//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_X86SEMANTICS_H
#define TRITON_X86SEMANTICS_H

#include "instruction.hpp"



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

      //! Builds the instruction's semantics.
      void build(triton::arch::Instruction& inst);


      /* Semantics ============================================================================= */

      //! Align add stack.
      void alignAddStack_s(triton::arch::Instruction& inst, triton::uint32 delta);

      //! Align sub stack.
      void alignSubStack_s(triton::arch::Instruction& inst, triton::uint32 delta);

      //! Clears a flag.
      void clearFlag_s(triton::arch::Instruction& inst, triton::arch::RegisterOperand& flag, std::string comment="");

      //! Sets a flag.
      void setFlag_s(triton::arch::Instruction& inst, triton::arch::RegisterOperand& flag, std::string comment="");

      //! Control flow semantics. Used to represent IP.
      void controlFlow_s(triton::arch::Instruction& inst);

      //! The AF semantics.
      void af_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, smt2lib::smtAstAbstractNode* op2, bool vol=false);

      //! The AF semantics.
      void afNeg_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, bool vol=false);

      //! The CF semantics.
      void cfAdd_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, smt2lib::smtAstAbstractNode* op2, bool vol=false);

      //! The CF semantics.
      void cfImul_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, smt2lib::smtAstAbstractNode* res, bool vol=false);

      //! The CF semantics.
      void cfMul_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, bool vol=false);

      //! The CF semantics.
      void cfNeg_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, bool vol=false);

      //! The CF semantics.
      void cfRcl_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op2, bool vol=false);

      //! The CF semantics.
      void cfRol_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op2, bool vol=false);

      //! The CF semantics.
      void cfRor_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op2, bool vol=false);

      //! The CF semantics.
      void cfSar_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, smt2lib::smtAstAbstractNode* op2, bool vol=false);

      //! The CF semantics.
      void cfShl_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, smt2lib::smtAstAbstractNode* op2, bool vol=false);

      //! The CF semantics.
      void cfShr_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, smt2lib::smtAstAbstractNode* op2, bool vol=false);

      //! The CF semantics.
      void cfSub_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, smt2lib::smtAstAbstractNode* op2, bool vol=false);

      //! The OF semantics.
      void ofAdd_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, smt2lib::smtAstAbstractNode* op2, bool vol=false);

      //! The OF semantics.
      void ofImul_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst,  smt2lib::smtAstAbstractNode* op1, smt2lib::smtAstAbstractNode* res, bool vol=false);

      //! The OF semantics.
      void ofMul_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, bool vol=false);

      //! The OF semantics.
      void ofNeg_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, bool vol=false);

      //! The OF semantics.
      void ofRol_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op2, bool vol=false);

      //! The OF semantics.
      void ofRor_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op2, bool vol=false);

      //! The OF semantics.
      void ofSar_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op2, bool vol=false);

      //! The OF semantics.
      void ofShl_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, smt2lib::smtAstAbstractNode* op2, bool vol=false);

      //! The OF semantics.
      void ofShr_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, smt2lib::smtAstAbstractNode* op2, bool vol=false);

      //! The OF semantics.
      void ofSub_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, smt2lib::smtAstAbstractNode* op2, bool vol=false);

      //! The PF semantics.
      void pf_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, bool vol=false);

      //! The PF semantics.
      void pfShl_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op2, bool vol=false);

      //! The SF semantics.
      void sf_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, bool vol=false);

      //! The SF semantics.
      void sfShl_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op2, bool vol=false);

      //! The ZF semantics.
      void zf_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, bool vol=false);

      //! The ZF semantics.
      void zfShl_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op2, bool vol=false);

      //! The ADC semantics.
      void adc_s(triton::arch::Instruction& inst);

      //! The ADD semantics.
      void add_s(triton::arch::Instruction& inst);

      //! The AND semantics.
      void and_s(triton::arch::Instruction& inst);

      //! The ANDNPD semantics.
      void andnpd_s(triton::arch::Instruction& inst);

      //! The ANDNPS semantics.
      void andnps_s(triton::arch::Instruction& inst);

      //! The ANDPD semantics.
      void andpd_s(triton::arch::Instruction& inst);

      //! The ANDPS semantics.
      void andps_s(triton::arch::Instruction& inst);

      //! The BSWAP semantics.
      void bswap_s(triton::arch::Instruction& inst);

      //! The CALL semantics.
      void call_s(triton::arch::Instruction& inst);

      //! The CBW semantics.
      void cbw_s(triton::arch::Instruction& inst);

      //! The CDQE semantics.
      void cdqe_s(triton::arch::Instruction& inst);

      //! The CLC semantics.
      void clc_s(triton::arch::Instruction& inst);

      //! The CLD semantics.
      void cld_s(triton::arch::Instruction& inst);

      //! The CMC semantics.
      void cmc_s(triton::arch::Instruction& inst);

      //! The CMOVA semantics.
      void cmova_s(triton::arch::Instruction& inst);

      //! The CMOVAE semantics.
      void cmovae_s(triton::arch::Instruction& inst);

      //! The CMOVB semantics.
      void cmovb_s(triton::arch::Instruction& inst);

      //! The CMOVBE semantics.
      void cmovbe_s(triton::arch::Instruction& inst);

      //! The CMOVE semantics.
      void cmove_s(triton::arch::Instruction& inst);

      //! The CMOVG semantics.
      void cmovg_s(triton::arch::Instruction& inst);

      //! The CMOVGE semantics.
      void cmovge_s(triton::arch::Instruction& inst);

      //! The CMOVL semantics.
      void cmovl_s(triton::arch::Instruction& inst);

      //! The CMOVLE semantics.
      void cmovle_s(triton::arch::Instruction& inst);

      //! The CMOVNE semantics.
      void cmovne_s(triton::arch::Instruction& inst);

      //! The CMOVNO semantics.
      void cmovno_s(triton::arch::Instruction& inst);

      //! The CMOVNP semantics.
      void cmovnp_s(triton::arch::Instruction& inst);

      //! The CMOVNS semantics.
      void cmovns_s(triton::arch::Instruction& inst);

      //! The CMOVO semantics.
      void cmovo_s(triton::arch::Instruction& inst);

      //! The CMOVP semantics.
      void cmovp_s(triton::arch::Instruction& inst);

      //! The CMOVS semantics.
      void cmovs_s(triton::arch::Instruction& inst);

      //! The CMP semantics.
      void cmp_s(triton::arch::Instruction& inst);

      //! The CMPXCHG semantics.
      void cmpxchg_s(triton::arch::Instruction& inst);

      //! The CQO semantics.
      void cqo_s(triton::arch::Instruction& inst);

      //! The CWDE semantics.
      void cwde_s(triton::arch::Instruction& inst);

      //! The DEC semantics.
      void dec_s(triton::arch::Instruction& inst);

      //! The DIV semantics.
      void div_s(triton::arch::Instruction& inst);

      //! The IDIV semantics.
      void idiv_s(triton::arch::Instruction& inst);

      //! The IMUL semantics.
      void imul_s(triton::arch::Instruction& inst);

      //! The INC semantics.
      void inc_s(triton::arch::Instruction& inst);

      //! The JA semantics.
      void ja_s(triton::arch::Instruction& inst);

      //! The JAE semantics.
      void jae_s(triton::arch::Instruction& inst);

      //! The JB semantics.
      void jb_s(triton::arch::Instruction& inst);

      //! The JBE semantics.
      void jbe_s(triton::arch::Instruction& inst);

      //! The JE semantics.
      void je_s(triton::arch::Instruction& inst);

      //! The JG semantics.
      void jg_s(triton::arch::Instruction& inst);

      //! The JGE semantics.
      void jge_s(triton::arch::Instruction& inst);

      //! The JL semantics.
      void jl_s(triton::arch::Instruction& inst);

      //! The JLE semantics.
      void jle_s(triton::arch::Instruction& inst);

      //! The JMP semantics.
      void jmp_s(triton::arch::Instruction& inst);

      //! The JNE semantics.
      void jne_s(triton::arch::Instruction& inst);

      //! The JNO semantics.
      void jno_s(triton::arch::Instruction& inst);

      //! The JNP semantics.
      void jnp_s(triton::arch::Instruction& inst);

      //! The JNS semantics.
      void jns_s(triton::arch::Instruction& inst);

      //! The JO semantics.
      void jo_s(triton::arch::Instruction& inst);

      //! The JP semantics.
      void jp_s(triton::arch::Instruction& inst);

      //! The JS semantics.
      void js_s(triton::arch::Instruction& inst);

      //! The LEA semantics.
      void lea_s(triton::arch::Instruction& inst);

      //! The LEAVE semantics.
      void leave_s(triton::arch::Instruction& inst);

      //! The MOV semantics.
      void mov_s(triton::arch::Instruction& inst);

      //! The MOVABS semantics.
      void movabs_s(triton::arch::Instruction& inst);

      //! The MOVAPD semantics.
      void movapd_s(triton::arch::Instruction& inst);

      //! The MOVAPS semantics.
      void movaps_s(triton::arch::Instruction& inst);

      //! The MOVDQA semantics.
      void movdqa_s(triton::arch::Instruction& inst);

      //! The MOVDQU semantics.
      void movdqu_s(triton::arch::Instruction& inst);

      //! The MOVHLPS semantics.
      void movhlps_s(triton::arch::Instruction& inst);

      //! The MOVHPD semantics.
      void movhpd_s(triton::arch::Instruction& inst);

      //! The MOVHPS semantics.
      void movhps_s(triton::arch::Instruction& inst);

      //! The MOVLHPS semantics.
      void movlhps_s(triton::arch::Instruction& inst);

      //! The MOVLPD semantics.
      void movlpd_s(triton::arch::Instruction& inst);

      //! The MOVLPS semantics.
      void movlps_s(triton::arch::Instruction& inst);

      //! The MOVSX semantics.
      void movsx_s(triton::arch::Instruction& inst);

      //! The MOVSXD semantics.
      void movsxd_s(triton::arch::Instruction& inst);

      //! The MOVZX semantics.
      void movzx_s(triton::arch::Instruction& inst);

      //! The MUL semantics.
      void mul_s(triton::arch::Instruction& inst);

      //! The NEG semantics.
      void neg_s(triton::arch::Instruction& inst);

      //! The NOP semantics.
      void nop_s(triton::arch::Instruction& inst);

      //! The NOT semantics.
      void not_s(triton::arch::Instruction& inst);

      //! The OR semantics.
      void or_s(triton::arch::Instruction& inst);

      //! The ORPD semantics.
      void orpd_s(triton::arch::Instruction& inst);

      //! The ORPS semantics.
      void orps_s(triton::arch::Instruction& inst);

      //! The PCMPEQB semantics.
      void pcmpeqb_s(triton::arch::Instruction& inst);

      //! The PCMPEQD semantics.
      void pcmpeqd_s(triton::arch::Instruction& inst);

      //! The PCMPEQW semantics.
      void pcmpeqw_s(triton::arch::Instruction& inst);

      //! The PMOVMSKB semantics.
      void pmovmskb_s(triton::arch::Instruction& inst);

      //! The POP semantics.
      void pop_s(triton::arch::Instruction& inst);

      //! The PUSH semantics.
      void push_s(triton::arch::Instruction& inst);

      //! The PXOR semantics.
      void pxor_s(triton::arch::Instruction& inst);

      //! The RCL semantics.
      void rcl_s(triton::arch::Instruction& inst);

      //! The RCR semantics.
      void rcr_s(triton::arch::Instruction& inst);

      //! The RET semantics.
      void ret_s(triton::arch::Instruction& inst);

      //! The ROL semantics.
      void rol_s(triton::arch::Instruction& inst);

      //! The ROR semantics.
      void ror_s(triton::arch::Instruction& inst);

      //! The SAR semantics.
      void sar_s(triton::arch::Instruction& inst);

      //! The SBB semantics.
      void sbb_s(triton::arch::Instruction& inst);

      //! The SETA semantics.
      void seta_s(triton::arch::Instruction& inst);

      //! The SETAE semantics.
      void setae_s(triton::arch::Instruction& inst);

      //! The SETB semantics.
      void setb_s(triton::arch::Instruction& inst);

      //! The SETBE semantics.
      void setbe_s(triton::arch::Instruction& inst);

      //! The SETE semantics.
      void sete_s(triton::arch::Instruction& inst);

      //! The SETG: semantics.
      void setg_s(triton::arch::Instruction& inst);

      //! The SETGE semantics.
      void setge_s(triton::arch::Instruction& inst);

      //! The SETL semantics.
      void setl_s(triton::arch::Instruction& inst);

      //! The SETLE semantics.
      void setle_s(triton::arch::Instruction& inst);

      //! The SETNE semantics.
      void setne_s(triton::arch::Instruction& inst);

      //! The SETNO semantics.
      void setno_s(triton::arch::Instruction& inst);

      //! The SETNP semantics.
      void setnp_s(triton::arch::Instruction& inst);

      //! The SETNS semantics.
      void setns_s(triton::arch::Instruction& inst);

      //! The SETO semantics.
      void seto_s(triton::arch::Instruction& inst);

      //! The SETP semantics.
      void setp_s(triton::arch::Instruction& inst);

      //! The SETS semantics.
      void sets_s(triton::arch::Instruction& inst);

      //! The SHL semantics.
      void shl_s(triton::arch::Instruction& inst);

      //! The SHR semantics.
      void shr_s(triton::arch::Instruction& inst);

      //! The STC semantics.
      void stc_s(triton::arch::Instruction& inst);

      //! The STD semantics.
      void std_s(triton::arch::Instruction& inst);

      //! The SUB semantics.
      void sub_s(triton::arch::Instruction& inst);

      //! The TEST semantics.
      void test_s(triton::arch::Instruction& inst);

      //! The XADD semantics.
      void xadd_s(triton::arch::Instruction& inst);

      //! The XCHG semantics.
      void xchg_s(triton::arch::Instruction& inst);

      //! The XOR semantics.
      void xor_s(triton::arch::Instruction& inst);

      //! The XORPD semantics.
      void xorpd_s(triton::arch::Instruction& inst);

      //! The XORPS semantics.
      void xorps_s(triton::arch::Instruction& inst);

      /*! @} End of semantics namespace */
      };
    /*! @} End of x86 namespace */
    };
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};


#endif /* TRITON_X86SEMANTICS_H */
