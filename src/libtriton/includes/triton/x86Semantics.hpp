//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_X86SEMANTICS_H
#define TRITON_X86SEMANTICS_H

#include <triton/architecture.hpp>
#include <triton/instruction.hpp>
#include <triton/semanticsInterface.hpp>
#include <triton/symbolicEngine.hpp>
#include <triton/taintEngine.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Architecture namespace
  namespace arch {
  /*!
   *  \ingroup triton
   *  \addtogroup arch
   *  @{
   */

    //! The x86 namespace
    namespace x86 {
    /*!
     *  \ingroup arch
     *  \addtogroup x86
     *  @{
     */

      /*! \class x86Semantics
          \brief The x86 ISA semantics. */
      class x86Semantics : public SemanticsInterface {
        private:
          //! Architecture API
          triton::arch::Architecture* architecture;

          //! Symbolic Engine API
          triton::engines::symbolic::SymbolicEngine* symbolicEngine;

          //! Taint Engine API
          triton::engines::taint::TaintEngine* taintEngine;

        public:
          //! Constructor.
          x86Semantics(triton::arch::Architecture* architecture,
                       triton::engines::symbolic::SymbolicEngine* symbolicEngine,
                       triton::engines::taint::TaintEngine* taintEngine);

          //! Destructor.
          virtual ~x86Semantics();

          //! Builds the semantics of the instruction. Returns true if the instruction is supported.
          bool buildSemantics(triton::arch::Instruction& inst);

          //! Aligns the stack (add). Returns the new stack value.
          triton::uint64 alignAddStack_s(triton::arch::Instruction& inst, triton::uint32 delta);

          //! Aligns the stack (sub). Returns the new stack value.
          triton::uint64 alignSubStack_s(triton::arch::Instruction& inst, triton::uint32 delta);

          //! Clears a flag.
          void clearFlag_s(triton::arch::Instruction& inst, triton::arch::Register& flag, std::string comment="");

          //! Sets a flag.
          void setFlag_s(triton::arch::Instruction& inst, triton::arch::Register& flag, std::string comment="");

          //! Control flow semantics. Used to represent IP.
          void controlFlow_s(triton::arch::Instruction& inst);

          //! The AF semantics.
          void af_s(triton::arch::Instruction& inst,
                    triton::engines::symbolic::SymbolicExpression* parent,
                    triton::arch::OperandWrapper& dst,
                    triton::ast::AbstractNode* op1,
                    triton::ast::AbstractNode* op2,
                    bool vol=false);

          //! The AF semantics.
          void afNeg_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::AbstractNode* op1,
                       bool vol=false);

          //! The CF semantics.
          void cfAdd_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::AbstractNode* op1,
                       triton::ast::AbstractNode* op2,
                       bool vol=false);

          //! The CF semantics.
          void cfBlsi_s(triton::arch::Instruction& inst,
                        triton::engines::symbolic::SymbolicExpression* parent,
                        triton::arch::OperandWrapper& dst,
                        triton::ast::AbstractNode* op1,
                        bool vol=false);

          //! The CF semantics.
          void cfBlsmsk_s(triton::arch::Instruction& inst,
                          triton::engines::symbolic::SymbolicExpression* parent,
                          triton::arch::OperandWrapper& dst,
                          triton::ast::AbstractNode* op1,
                          bool vol=false);

          //! The CF semantics.
          void cfBlsr_s(triton::arch::Instruction& inst,
                        triton::engines::symbolic::SymbolicExpression* parent,
                        triton::arch::OperandWrapper& dst,
                        triton::ast::AbstractNode* op1,
                        bool vol=false);

          //! The CF semantics.
          void cfImul_s(triton::arch::Instruction& inst,
                        triton::engines::symbolic::SymbolicExpression* parent,
                        triton::arch::OperandWrapper& dst,
                        triton::ast::AbstractNode* op1,
                        triton::ast::AbstractNode* res,
                        bool vol=false);

          //! The CF semantics.
          void cfMul_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::AbstractNode* op1,
                       bool vol=false);

          //! The CF semantics.
          void cfNeg_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::AbstractNode* op1,
                       bool vol=false);

          //! The CF semantics.
          void cfPtest_s(triton::arch::Instruction& inst,
                         triton::engines::symbolic::SymbolicExpression* parent,
                         triton::arch::OperandWrapper& dst,
                         bool vol=false);

          //! The CF semantics.
          void cfRcl_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::ast::AbstractNode* result,
                       triton::ast::AbstractNode* op2,
                       bool vol=false);

          //! The CF semantics.
          void cfRcr_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::AbstractNode* result,
                       triton::ast::AbstractNode* op2,
                       bool vol=false);

          //! The CF semantics.
          void cfRol_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::AbstractNode* op2,
                       bool vol=false);

          //! The CF semantics.
          void cfRor_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::AbstractNode* op2,
                       bool vol=false);

          //! The CF semantics.
          void cfSar_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::AbstractNode* op1,
                       triton::ast::AbstractNode* op2,
                       bool vol=false);

          //! The CF semantics.
          void cfShl_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::AbstractNode* op1,
                       triton::ast::AbstractNode* op2,
                       bool vol=false);

          //! The CF semantics.
          void cfShld_s(triton::arch::Instruction& inst,
                        triton::engines::symbolic::SymbolicExpression* parent,
                        triton::arch::OperandWrapper& dst,
                        triton::ast::AbstractNode* op1,
                        triton::ast::AbstractNode* op2,
                        triton::ast::AbstractNode* op3,
                        bool vol=false);

          //! The CF semantics.
          void cfShr_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::AbstractNode* op1,
                       triton::ast::AbstractNode* op2,
                       bool vol=false);

          //! The CF semantics.
          void cfShrd_s(triton::arch::Instruction& inst,
                        triton::engines::symbolic::SymbolicExpression* parent,
                        triton::arch::OperandWrapper& dst,
                        triton::ast::AbstractNode* op1,
                        triton::ast::AbstractNode* op2,
                        triton::ast::AbstractNode* op3,
                        bool vol=false);

          //! The CF semantics.
          void cfSub_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::AbstractNode* op1,
                       triton::ast::AbstractNode* op2,
                       bool vol=false);

          //! The OF semantics.
          void ofAdd_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::AbstractNode* op1,
                       triton::ast::AbstractNode* op2,
                       bool vol=false);

          //! The OF semantics.
          void ofImul_s(triton::arch::Instruction& inst,
                        triton::engines::symbolic::SymbolicExpression* parent,
                        triton::arch::OperandWrapper& dst,
                        triton::ast::AbstractNode* op1,
                        triton::ast::AbstractNode* res,
                        bool vol=false);

          //! The OF semantics.
          void ofMul_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::AbstractNode* op1,
                       bool vol=false);

          //! The OF semantics.
          void ofNeg_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::AbstractNode* op1,
                       bool vol=false);

          //! The OF semantics.
          void ofRol_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::AbstractNode* op2,
                       bool vol=false);

          //! The OF semantics.
          void ofRor_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::AbstractNode* op2,
                       bool vol=false);

          //! The OF semantics.
          void ofRcr_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::AbstractNode* op1,
                       triton::ast::AbstractNode* op2,
                       bool vol=false);

          //! The OF semantics.
          void ofSar_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::AbstractNode* op2,
                       bool vol=false);

          //! The OF semantics.
          void ofShl_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::AbstractNode* op1,
                       triton::ast::AbstractNode* op2,
                       bool vol=false);

          //! The OF semantics.
          void ofShld_s(triton::arch::Instruction& inst,
                        triton::engines::symbolic::SymbolicExpression* parent,
                        triton::arch::OperandWrapper& dst,
                        triton::ast::AbstractNode* op1,
                        triton::ast::AbstractNode* op2,
                        triton::ast::AbstractNode* op3,
                        bool vol=false);

          //! The OF semantics.
          void ofShr_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::AbstractNode* op1,
                       triton::ast::AbstractNode* op2,
                       bool vol=false);

          //! The OF semantics.
          void ofShrd_s(triton::arch::Instruction& inst,
                        triton::engines::symbolic::SymbolicExpression* parent,
                        triton::arch::OperandWrapper& dst,
                        triton::ast::AbstractNode* op1,
                        triton::ast::AbstractNode* op2,
                        triton::ast::AbstractNode* op3,
                        bool vol=false);

          //! The OF semantics.
          void ofSub_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::AbstractNode* op1,
                       triton::ast::AbstractNode* op2,
                       bool vol=false);

          //! The PF semantics.
          void pf_s(triton::arch::Instruction& inst,
                    triton::engines::symbolic::SymbolicExpression* parent,
                    triton::arch::OperandWrapper& dst,
                    bool vol=false);

          //! The PF semantics.
          void pfShl_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::AbstractNode* op2,
                       bool vol=false);

          //! The SF semantics.
          void sf_s(triton::arch::Instruction& inst,
                    triton::engines::symbolic::SymbolicExpression* parent,
                    triton::arch::OperandWrapper& dst,
                    bool vol=false);

          //! The SF semantics.
          void sfShl_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::AbstractNode* op2,
                       bool vol=false);

          //! The SF semantics.
          void sfShld_s(triton::arch::Instruction& inst,
                        triton::engines::symbolic::SymbolicExpression* parent,
                        triton::arch::OperandWrapper& dst,
                        triton::ast::AbstractNode* op1,
                        triton::ast::AbstractNode* op2,
                        triton::ast::AbstractNode* op3,
                        bool vol=false);

          //! The SF semantics.
          void sfShrd_s(triton::arch::Instruction& inst,
                        triton::engines::symbolic::SymbolicExpression* parent,
                        triton::arch::OperandWrapper& dst,
                        triton::ast::AbstractNode* op1,
                        triton::ast::AbstractNode* op2,
                        triton::ast::AbstractNode* op3,
                        bool vol=false);

          //! The ZF semantics.
          void zf_s(triton::arch::Instruction& inst,
                    triton::engines::symbolic::SymbolicExpression* parent,
                    triton::arch::OperandWrapper& dst,
                    bool vol=false);

          //! The ZF semantics.
          void zfBsf_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::arch::OperandWrapper& src,
                       triton::ast::AbstractNode* op2,
                       bool vol=false);

          //! The ZF semantics.
          void zfShl_s(triton::arch::Instruction& inst,
                       triton::engines::symbolic::SymbolicExpression* parent,
                       triton::arch::OperandWrapper& dst,
                       triton::ast::AbstractNode* op2,
                       bool vol=false);

          //! The AAD semantics.
          void aad_s(triton::arch::Instruction& inst);

          //! The ADC semantics.
          void adc_s(triton::arch::Instruction& inst);

          //! The ADCX semantics.
          void adcx_s(triton::arch::Instruction& inst);

          //! The ADD semantics.
          void add_s(triton::arch::Instruction& inst);

          //! The AND semantics.
          void and_s(triton::arch::Instruction& inst);

          //! The ANDN semantics.
          void andn_s(triton::arch::Instruction& inst);

          //! The ANDNPD semantics.
          void andnpd_s(triton::arch::Instruction& inst);

          //! The ANDNPS semantics.
          void andnps_s(triton::arch::Instruction& inst);

          //! The ANDPD semantics.
          void andpd_s(triton::arch::Instruction& inst);

          //! The ANDPS semantics.
          void andps_s(triton::arch::Instruction& inst);

          //! The BEXTR semantics.
          void bextr_s(triton::arch::Instruction& inst);

          //! The BLSI semantics.
          void blsi_s(triton::arch::Instruction& inst);

          //! The BLSMSK semantics.
          void blsmsk_s(triton::arch::Instruction& inst);

          //! The BLSR semantics.
          void blsr_s(triton::arch::Instruction& inst);

          //! The BSF semantics.
          void bsf_s(triton::arch::Instruction& inst);

          //! The BSR semantics.
          void bsr_s(triton::arch::Instruction& inst);

          //! The BSWAP semantics.
          void bswap_s(triton::arch::Instruction& inst);

          //! The BT semantics.
          void bt_s(triton::arch::Instruction& inst);

          //! The BTC semantics.
          void btc_s(triton::arch::Instruction& inst);

          //! The BTR semantics.
          void btr_s(triton::arch::Instruction& inst);

          //! The BTS semantics.
          void bts_s(triton::arch::Instruction& inst);

          //! The CALL semantics.
          void call_s(triton::arch::Instruction& inst);

          //! The CBW semantics.
          void cbw_s(triton::arch::Instruction& inst);

          //! The CDQ semantics.
          void cdq_s(triton::arch::Instruction& inst);

          //! The CDQE semantics.
          void cdqe_s(triton::arch::Instruction& inst);

          //! The CLC semantics.
          void clc_s(triton::arch::Instruction& inst);

          //! The CLD semantics.
          void cld_s(triton::arch::Instruction& inst);

          //! The CLFLUSH semantics.
          void clflush_s(triton::arch::Instruction& inst);

          //! The CLTS semantics.
          void clts_s(triton::arch::Instruction& inst);

          //! The CLI semantics.
          void cli_s(triton::arch::Instruction& inst);

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

          //! The CMPSB semantics.
          void cmpsb_s(triton::arch::Instruction& inst);

          //! The CMPSD semantics.
          void cmpsd_s(triton::arch::Instruction& inst);

          //! The CMPSQ semantics.
          void cmpsq_s(triton::arch::Instruction& inst);

          //! The CMPSW semantics.
          void cmpsw_s(triton::arch::Instruction& inst);

          //! The CMPXCHG semantics.
          void cmpxchg_s(triton::arch::Instruction& inst);

          //! The CMPXCHG16B semantics.
          void cmpxchg16b_s(triton::arch::Instruction& inst);

          //! The CMPXCHG8B semantics.
          void cmpxchg8b_s(triton::arch::Instruction& inst);

          //! The CPUID semantics.
          void cpuid_s(triton::arch::Instruction& inst);

          //! The CQO semantics.
          void cqo_s(triton::arch::Instruction& inst);

          //! The CWD semantics.
          void cwd_s(triton::arch::Instruction& inst);

          //! The CWDE semantics.
          void cwde_s(triton::arch::Instruction& inst);

          //! The DEC semantics.
          void dec_s(triton::arch::Instruction& inst);

          //! The DIV semantics.
          void div_s(triton::arch::Instruction& inst);

          //! The EXTRACTPS semantics.
          void extractps_s(triton::arch::Instruction& inst);

          //! The IDIV semantics.
          void idiv_s(triton::arch::Instruction& inst);

          //! The IMUL semantics.
          void imul_s(triton::arch::Instruction& inst);

          //! The INC semantics.
          void inc_s(triton::arch::Instruction& inst);

          //! The INVD semantics.
          void invd_s(triton::arch::Instruction& inst);

          //! The INVLPG semantics.
          void invlpg_s(triton::arch::Instruction& inst);

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

          //! The LAHF semantics.
          void lahf_s(triton::arch::Instruction& inst);

          //! The LDDQU semantics.
          void lddqu_s(triton::arch::Instruction& inst);

          //! The LDMXCSR semantics.
          void ldmxcsr_s(triton::arch::Instruction& inst);

          //! The LEA semantics.
          void lea_s(triton::arch::Instruction& inst);

          //! The LEAVE semantics.
          void leave_s(triton::arch::Instruction& inst);

          //! The LFENCE semantics.
          void lfence_s(triton::arch::Instruction& inst);

          //! The LODSB semantics.
          void lodsb_s(triton::arch::Instruction& inst);

          //! The LODSD semantics.
          void lodsd_s(triton::arch::Instruction& inst);

          //! The LODSQ semantics.
          void lodsq_s(triton::arch::Instruction& inst);

          //! The LODSW semantics.
          void lodsw_s(triton::arch::Instruction& inst);

          //! The MFENCE semantics.
          void mfence_s(triton::arch::Instruction& inst);

          //! The MOV semantics.
          void mov_s(triton::arch::Instruction& inst);

          //! The MOVABS semantics.
          void movabs_s(triton::arch::Instruction& inst);

          //! The MOVAPD semantics.
          void movapd_s(triton::arch::Instruction& inst);

          //! The MOVAPS semantics.
          void movaps_s(triton::arch::Instruction& inst);

          //! The MOVD semantics.
          void movd_s(triton::arch::Instruction& inst);

          //! The MOVDDUP semantics.
          void movddup_s(triton::arch::Instruction& inst);

          //! The MOVDQ2Q semantics.
          void movdq2q_s(triton::arch::Instruction& inst);

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

          //! The MOVMSKPD semantics.
          void movmskpd_s(triton::arch::Instruction& inst);

          //! The MOVMSKPS semantics.
          void movmskps_s(triton::arch::Instruction& inst);

          //! The MOVNTDQ semantics.
          void movntdq_s(triton::arch::Instruction& inst);

          //! The MOVNTI semantics.
          void movnti_s(triton::arch::Instruction& inst);

          //! The MOVNTPD semantics.
          void movntpd_s(triton::arch::Instruction& inst);

          //! The MOVNTPS semantics.
          void movntps_s(triton::arch::Instruction& inst);

          //! The MOVNTQ semantics.
          void movntq_s(triton::arch::Instruction& inst);

          //! The MOVSHDUP semantics.
          void movshdup_s(triton::arch::Instruction& inst);

          //! The MOVSLDUP semantics.
          void movsldup_s(triton::arch::Instruction& inst);

          //! The MOVQ semantics.
          void movq_s(triton::arch::Instruction& inst);

          //! The MOVQ2DQ semantics.
          void movq2dq_s(triton::arch::Instruction& inst);

          //! The MOVSB semantics.
          void movsb_s(triton::arch::Instruction& inst);

          //! The MOVSD semantics.
          void movsd_s(triton::arch::Instruction& inst);

          //! The MOVUPD semantics.
          void movupd_s(triton::arch::Instruction& inst);

          //! The MOVUPS semantics.
          void movups_s(triton::arch::Instruction& inst);

          //! The MOVSQ semantics.
          void movsq_s(triton::arch::Instruction& inst);

          //! The MOVSW semantics.
          void movsw_s(triton::arch::Instruction& inst);

          //! The MOVSX semantics.
          void movsx_s(triton::arch::Instruction& inst);

          //! The MOVSXD semantics.
          void movsxd_s(triton::arch::Instruction& inst);

          //! The MOVZX semantics.
          void movzx_s(triton::arch::Instruction& inst);

          //! The MUL semantics.
          void mul_s(triton::arch::Instruction& inst);

          //! The MULX semantics.
          void mulx_s(triton::arch::Instruction& inst);

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

          //! The PADDB semantics.
          void paddb_s(triton::arch::Instruction& inst);

          //! The PADDD semantics.
          void paddd_s(triton::arch::Instruction& inst);

          //! The PADDQ semantics.
          void paddq_s(triton::arch::Instruction& inst);

          //! The PADDW semantics.
          void paddw_s(triton::arch::Instruction& inst);

          //! The PAND semantics.
          void pand_s(triton::arch::Instruction& inst);

          //! The PANDN semantics.
          void pandn_s(triton::arch::Instruction& inst);

          //! The PAUSE semantics.
          void pause_s(triton::arch::Instruction& inst);

          //! The PAVGB semantics.
          void pavgb_s(triton::arch::Instruction& inst);

          //! The PAVGW semantics.
          void pavgw_s(triton::arch::Instruction& inst);

          //! The PCMPEQB semantics.
          void pcmpeqb_s(triton::arch::Instruction& inst);

          //! The PCMPEQD semantics.
          void pcmpeqd_s(triton::arch::Instruction& inst);

          //! The PCMPEQW semantics.
          void pcmpeqw_s(triton::arch::Instruction& inst);

          //! The PCMPGTB semantics.
          void pcmpgtb_s(triton::arch::Instruction& inst);

          //! The PCMPGTD semantics.
          void pcmpgtd_s(triton::arch::Instruction& inst);

          //! The PCMPGTW semantics.
          void pcmpgtw_s(triton::arch::Instruction& inst);

          //! The PMAXSB semantics.
          void pmaxsb_s(triton::arch::Instruction& inst);

          //! The PMAXSD semantics.
          void pmaxsd_s(triton::arch::Instruction& inst);

          //! The PMAXSW semantics.
          void pmaxsw_s(triton::arch::Instruction& inst);

          //! The PMAXUB semantics.
          void pmaxub_s(triton::arch::Instruction& inst);

          //! The PMAXUD semantics.
          void pmaxud_s(triton::arch::Instruction& inst);

          //! The PMAXUW semantics.
          void pmaxuw_s(triton::arch::Instruction& inst);

          //! The PMINSB semantics.
          void pminsb_s(triton::arch::Instruction& inst);

          //! The PMINSD semantics.
          void pminsd_s(triton::arch::Instruction& inst);

          //! The PMINSW semantics.
          void pminsw_s(triton::arch::Instruction& inst);

          //! The PMINUB semantics.
          void pminub_s(triton::arch::Instruction& inst);

          //! The PMINUD semantics.
          void pminud_s(triton::arch::Instruction& inst);

          //! The PMINUW semantics.
          void pminuw_s(triton::arch::Instruction& inst);

          //! The PMOVMSKB semantics.
          void pmovmskb_s(triton::arch::Instruction& inst);

          //! The PMOVSXBD semantics.
          void pmovsxbd_s(triton::arch::Instruction& inst);

          //! The PMOVSXBQ semantics.
          void pmovsxbq_s(triton::arch::Instruction& inst);

          //! The PMOVSXBW semantics.
          void pmovsxbw_s(triton::arch::Instruction& inst);

          //! The PMOVSXDQ semantics.
          void pmovsxdq_s(triton::arch::Instruction& inst);

          //! The PMOVSXWD semantics.
          void pmovsxwd_s(triton::arch::Instruction& inst);

          //! The PMOVSXWQ semantics.
          void pmovsxwq_s(triton::arch::Instruction& inst);

          //! The PMOVZXBD semantics.
          void pmovzxbd_s(triton::arch::Instruction& inst);

          //! The PMOVZXBQ semantics.
          void pmovzxbq_s(triton::arch::Instruction& inst);

          //! The PMOVZXBW semantics.
          void pmovzxbw_s(triton::arch::Instruction& inst);

          //! The PMOVZXDQ semantics.
          void pmovzxdq_s(triton::arch::Instruction& inst);

          //! The PMOVZXWD semantics.
          void pmovzxwd_s(triton::arch::Instruction& inst);

          //! The PMOVZXWQ semantics.
          void pmovzxwq_s(triton::arch::Instruction& inst);

          //! The POP semantics.
          void pop_s(triton::arch::Instruction& inst);

          //! The POPAL semantics.
          void popal_s(triton::arch::Instruction& inst);

          //! The POPFD semantics.
          void popfd_s(triton::arch::Instruction& inst);

          //! The POPFQ semantics.
          void popfq_s(triton::arch::Instruction& inst);

          //! The POR semantics.
          void por_s(triton::arch::Instruction& inst);

          //! The PREFETCHx semantics.
          void prefetchx_s(triton::arch::Instruction& inst);

          //! The PSHUFD semantics.
          void pshufd_s(triton::arch::Instruction& inst);

          //! The PSHUFHW semantics.
          void pshufhw_s(triton::arch::Instruction& inst);

          //! The PSHUFLW semantics.
          void pshuflw_s(triton::arch::Instruction& inst);

          //! The PSHUFW semantics.
          void pshufw_s(triton::arch::Instruction& inst);

          //! The PSLLDQ semantics.
          void pslldq_s(triton::arch::Instruction& inst);

          //! The PSRLDQ semantics.
          void psrldq_s(triton::arch::Instruction& inst);

          //! The PSUBB semantics.
          void psubb_s(triton::arch::Instruction& inst);

          //! The PSUBD semantics.
          void psubd_s(triton::arch::Instruction& inst);

          //! The PSUBQ semantics.
          void psubq_s(triton::arch::Instruction& inst);

          //! The PSUBW semantics.
          void psubw_s(triton::arch::Instruction& inst);

          //! The PTEST semantics.
          void ptest_s(triton::arch::Instruction& inst);

          //! The PUNPCKHBW semantics.
          void punpckhbw_s(triton::arch::Instruction& inst);

          //! The PUNPCKHDQ semantics.
          void punpckhdq_s(triton::arch::Instruction& inst);

          //! The PUNPCKHQDQ semantics.
          void punpckhqdq_s(triton::arch::Instruction& inst);

          //! The PUNPCKHWD semantics.
          void punpckhwd_s(triton::arch::Instruction& inst);

          //! The PUNPCKLBW semantics.
          void punpcklbw_s(triton::arch::Instruction& inst);

          //! The PUNPCKLDQ semantics.
          void punpckldq_s(triton::arch::Instruction& inst);

          //! The PUNPCKLQDQ semantics.
          void punpcklqdq_s(triton::arch::Instruction& inst);

          //! The PUNPCKLWD semantics.
          void punpcklwd_s(triton::arch::Instruction& inst);

          //! The PUSH semantics.
          void push_s(triton::arch::Instruction& inst);

          //! The PUSHAL semantics.
          void pushal_s(triton::arch::Instruction& inst);

          //! The PUSHFD semantics.
          void pushfd_s(triton::arch::Instruction& inst);

          //! The PUSHFQ semantics.
          void pushfq_s(triton::arch::Instruction& inst);

          //! The PXOR semantics.
          void pxor_s(triton::arch::Instruction& inst);

          //! The RCL semantics.
          void rcl_s(triton::arch::Instruction& inst);

          //! The RCR semantics.
          void rcr_s(triton::arch::Instruction& inst);

          //! The RDTSC semantics.
          void rdtsc_s(triton::arch::Instruction& inst);

          //! The RET semantics.
          void ret_s(triton::arch::Instruction& inst);

          //! The ROL semantics.
          void rol_s(triton::arch::Instruction& inst);

          //! The ROR semantics.
          void ror_s(triton::arch::Instruction& inst);

          //! The RORX semantics.
          void rorx_s(triton::arch::Instruction& inst);

          //! The SAHF semantics.
          void sahf_s(triton::arch::Instruction& inst);

          //! The SAR semantics.
          void sar_s(triton::arch::Instruction& inst);

          //! The SARX semantics.
          void sarx_s(triton::arch::Instruction& inst);

          //! The SBB semantics.
          void sbb_s(triton::arch::Instruction& inst);

          //! The SCASB semantics.
          void scasb_s(triton::arch::Instruction& inst);

          //! The SCASD semantics.
          void scasd_s(triton::arch::Instruction& inst);

          //! The SCASQ semantics.
          void scasq_s(triton::arch::Instruction& inst);

          //! The SCASW semantics.
          void scasw_s(triton::arch::Instruction& inst);

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

          //! The SFENCE semantics.
          void sfence_s(triton::arch::Instruction& inst);

          //! The SHL semantics.
          void shl_s(triton::arch::Instruction& inst);

          //! The SHLD semantics.
          void shld_s(triton::arch::Instruction& inst);

          //! The SHLX semantics.
          void shlx_s(triton::arch::Instruction& inst);

          //! The SHR semantics.
          void shr_s(triton::arch::Instruction& inst);

          //! The SHRD semantics.
          void shrd_s(triton::arch::Instruction& inst);

          //! The SHRX semantics.
          void shrx_s(triton::arch::Instruction& inst);

          //! The STC semantics.
          void stc_s(triton::arch::Instruction& inst);

          //! The STD semantics.
          void std_s(triton::arch::Instruction& inst);

          //! The STI semantics.
          void sti_s(triton::arch::Instruction& inst);

          //! The STMXCSR semantics.
          void stmxcsr_s(triton::arch::Instruction& inst);

          //! The STOSB semantics.
          void stosb_s(triton::arch::Instruction& inst);

          //! The STOSD semantics.
          void stosd_s(triton::arch::Instruction& inst);

          //! The STOSQ semantics.
          void stosq_s(triton::arch::Instruction& inst);

          //! The STOSW semantics.
          void stosw_s(triton::arch::Instruction& inst);

          //! The SUB semantics.
          void sub_s(triton::arch::Instruction& inst);

          //! The SYSCALL semantics.
          void syscall_s(triton::arch::Instruction& inst);

          //! The TEST semantics.
          void test_s(triton::arch::Instruction& inst);

          //! The TZCNT semantics.
          void tzcnt_s(triton::arch::Instruction& inst);

          //! The UNPCKHPD semantics.
          void unpckhpd_s(triton::arch::Instruction& inst);

          //! The UNPCKHPS semantics.
          void unpckhps_s(triton::arch::Instruction& inst);

          //! The UNPCKLPD semantics.
          void unpcklpd_s(triton::arch::Instruction& inst);

          //! The UNPCKLPS semantics.
          void unpcklps_s(triton::arch::Instruction& inst);

          //! The VMOVDQA semantics.
          void vmovdqa_s(triton::arch::Instruction& inst);

          //! The VMOVDQU semantics.
          void vmovdqu_s(triton::arch::Instruction& inst);

          //! The VPAND semantics.
          void vpand_s(triton::arch::Instruction& inst);

          //! The VPANDN semantics.
          void vpandn_s(triton::arch::Instruction& inst);

          //! The VPOR semantics.
          void vpor_s(triton::arch::Instruction& inst);

          //! The VPSHUFD semantics.
          void vpshufd_s(triton::arch::Instruction& inst);

          //! The VPTEST semantics.
          void vptest_s(triton::arch::Instruction& inst);

          //! The VPXOR semantics.
          void vpxor_s(triton::arch::Instruction& inst);

          //! The WBINVD semantics.
          void wbinvd_s(triton::arch::Instruction& inst);

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
      };

    /*! @} End of x86 namespace */
    };
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};


#endif /* TRITON_X86SEMANTICS_H */
