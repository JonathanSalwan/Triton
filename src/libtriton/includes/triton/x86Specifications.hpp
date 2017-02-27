//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_X86SPECIFICATIONS_H
#define TRITON_X86SPECIFICATIONS_H

#include <triton/register.hpp>
#include <triton/registerSpecification.hpp>



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

      extern triton::arch::Register x86_reg_invalid;

      extern triton::arch::Register x86_reg_rax;
      extern triton::arch::Register x86_reg_eax;
      extern triton::arch::Register x86_reg_ax;
      extern triton::arch::Register x86_reg_ah;
      extern triton::arch::Register x86_reg_al;

      extern triton::arch::Register x86_reg_rbx;
      extern triton::arch::Register x86_reg_ebx;
      extern triton::arch::Register x86_reg_bx;
      extern triton::arch::Register x86_reg_bh;
      extern triton::arch::Register x86_reg_bl;

      extern triton::arch::Register x86_reg_rcx;
      extern triton::arch::Register x86_reg_ecx;
      extern triton::arch::Register x86_reg_cx;
      extern triton::arch::Register x86_reg_ch;
      extern triton::arch::Register x86_reg_cl;

      extern triton::arch::Register x86_reg_rdx;
      extern triton::arch::Register x86_reg_edx;
      extern triton::arch::Register x86_reg_dx;
      extern triton::arch::Register x86_reg_dh;
      extern triton::arch::Register x86_reg_dl;

      extern triton::arch::Register x86_reg_rdi;
      extern triton::arch::Register x86_reg_edi;
      extern triton::arch::Register x86_reg_di;
      extern triton::arch::Register x86_reg_dil;

      extern triton::arch::Register x86_reg_rsi;
      extern triton::arch::Register x86_reg_esi;
      extern triton::arch::Register x86_reg_si;
      extern triton::arch::Register x86_reg_sil;

      extern triton::arch::Register x86_reg_rsp;
      extern triton::arch::Register x86_reg_esp;
      extern triton::arch::Register x86_reg_sp;
      extern triton::arch::Register x86_reg_spl;
      extern triton::arch::Register x86_reg_stack;

      extern triton::arch::Register x86_reg_rbp;
      extern triton::arch::Register x86_reg_ebp;
      extern triton::arch::Register x86_reg_bp;
      extern triton::arch::Register x86_reg_bpl;

      extern triton::arch::Register x86_reg_rip;
      extern triton::arch::Register x86_reg_eip;
      extern triton::arch::Register x86_reg_ip;
      extern triton::arch::Register x86_reg_pc;

      extern triton::arch::Register x86_reg_eflags;

      extern triton::arch::Register x86_reg_r8;
      extern triton::arch::Register x86_reg_r8d;
      extern triton::arch::Register x86_reg_r8w;
      extern triton::arch::Register x86_reg_r8b;

      extern triton::arch::Register x86_reg_r9;
      extern triton::arch::Register x86_reg_r9d;
      extern triton::arch::Register x86_reg_r9w;
      extern triton::arch::Register x86_reg_r9b;

      extern triton::arch::Register x86_reg_r10;
      extern triton::arch::Register x86_reg_r10d;
      extern triton::arch::Register x86_reg_r10w;
      extern triton::arch::Register x86_reg_r10b;

      extern triton::arch::Register x86_reg_r11;
      extern triton::arch::Register x86_reg_r11d;
      extern triton::arch::Register x86_reg_r11w;
      extern triton::arch::Register x86_reg_r11b;

      extern triton::arch::Register x86_reg_r12;
      extern triton::arch::Register x86_reg_r12d;
      extern triton::arch::Register x86_reg_r12w;
      extern triton::arch::Register x86_reg_r12b;

      extern triton::arch::Register x86_reg_r13;
      extern triton::arch::Register x86_reg_r13d;
      extern triton::arch::Register x86_reg_r13w;
      extern triton::arch::Register x86_reg_r13b;

      extern triton::arch::Register x86_reg_r14;
      extern triton::arch::Register x86_reg_r14d;
      extern triton::arch::Register x86_reg_r14w;
      extern triton::arch::Register x86_reg_r14b;

      extern triton::arch::Register x86_reg_r15;
      extern triton::arch::Register x86_reg_r15d;
      extern triton::arch::Register x86_reg_r15w;
      extern triton::arch::Register x86_reg_r15b;

      extern triton::arch::Register x86_reg_mm0;
      extern triton::arch::Register x86_reg_mm1;
      extern triton::arch::Register x86_reg_mm2;
      extern triton::arch::Register x86_reg_mm3;
      extern triton::arch::Register x86_reg_mm4;
      extern triton::arch::Register x86_reg_mm5;
      extern triton::arch::Register x86_reg_mm6;
      extern triton::arch::Register x86_reg_mm7;

      extern triton::arch::Register x86_reg_xmm0;
      extern triton::arch::Register x86_reg_xmm1;
      extern triton::arch::Register x86_reg_xmm2;
      extern triton::arch::Register x86_reg_xmm3;
      extern triton::arch::Register x86_reg_xmm4;
      extern triton::arch::Register x86_reg_xmm5;
      extern triton::arch::Register x86_reg_xmm6;
      extern triton::arch::Register x86_reg_xmm7;
      extern triton::arch::Register x86_reg_xmm8;
      extern triton::arch::Register x86_reg_xmm9;
      extern triton::arch::Register x86_reg_xmm10;
      extern triton::arch::Register x86_reg_xmm11;
      extern triton::arch::Register x86_reg_xmm12;
      extern triton::arch::Register x86_reg_xmm13;
      extern triton::arch::Register x86_reg_xmm14;
      extern triton::arch::Register x86_reg_xmm15;

      extern triton::arch::Register x86_reg_ymm0;
      extern triton::arch::Register x86_reg_ymm1;
      extern triton::arch::Register x86_reg_ymm2;
      extern triton::arch::Register x86_reg_ymm3;
      extern triton::arch::Register x86_reg_ymm4;
      extern triton::arch::Register x86_reg_ymm5;
      extern triton::arch::Register x86_reg_ymm6;
      extern triton::arch::Register x86_reg_ymm7;
      extern triton::arch::Register x86_reg_ymm8;
      extern triton::arch::Register x86_reg_ymm9;
      extern triton::arch::Register x86_reg_ymm10;
      extern triton::arch::Register x86_reg_ymm11;
      extern triton::arch::Register x86_reg_ymm12;
      extern triton::arch::Register x86_reg_ymm13;
      extern triton::arch::Register x86_reg_ymm14;
      extern triton::arch::Register x86_reg_ymm15;

      extern triton::arch::Register x86_reg_zmm0;
      extern triton::arch::Register x86_reg_zmm1;
      extern triton::arch::Register x86_reg_zmm2;
      extern triton::arch::Register x86_reg_zmm3;
      extern triton::arch::Register x86_reg_zmm4;
      extern triton::arch::Register x86_reg_zmm5;
      extern triton::arch::Register x86_reg_zmm6;
      extern triton::arch::Register x86_reg_zmm7;
      extern triton::arch::Register x86_reg_zmm8;
      extern triton::arch::Register x86_reg_zmm9;
      extern triton::arch::Register x86_reg_zmm10;
      extern triton::arch::Register x86_reg_zmm11;
      extern triton::arch::Register x86_reg_zmm12;
      extern triton::arch::Register x86_reg_zmm13;
      extern triton::arch::Register x86_reg_zmm14;
      extern triton::arch::Register x86_reg_zmm15;
      extern triton::arch::Register x86_reg_zmm16;
      extern triton::arch::Register x86_reg_zmm17;
      extern triton::arch::Register x86_reg_zmm18;
      extern triton::arch::Register x86_reg_zmm19;
      extern triton::arch::Register x86_reg_zmm20;
      extern triton::arch::Register x86_reg_zmm21;
      extern triton::arch::Register x86_reg_zmm22;
      extern triton::arch::Register x86_reg_zmm23;
      extern triton::arch::Register x86_reg_zmm24;
      extern triton::arch::Register x86_reg_zmm25;
      extern triton::arch::Register x86_reg_zmm26;
      extern triton::arch::Register x86_reg_zmm27;
      extern triton::arch::Register x86_reg_zmm28;
      extern triton::arch::Register x86_reg_zmm29;
      extern triton::arch::Register x86_reg_zmm30;
      extern triton::arch::Register x86_reg_zmm31;

      extern triton::arch::Register x86_reg_mxcsr;

      extern triton::arch::Register x86_reg_cr0;
      extern triton::arch::Register x86_reg_cr1;
      extern triton::arch::Register x86_reg_cr2;
      extern triton::arch::Register x86_reg_cr3;
      extern triton::arch::Register x86_reg_cr4;
      extern triton::arch::Register x86_reg_cr5;
      extern triton::arch::Register x86_reg_cr6;
      extern triton::arch::Register x86_reg_cr7;
      extern triton::arch::Register x86_reg_cr8;
      extern triton::arch::Register x86_reg_cr9;
      extern triton::arch::Register x86_reg_cr10;
      extern triton::arch::Register x86_reg_cr11;
      extern triton::arch::Register x86_reg_cr12;
      extern triton::arch::Register x86_reg_cr13;
      extern triton::arch::Register x86_reg_cr14;
      extern triton::arch::Register x86_reg_cr15;

      extern triton::arch::Register x86_reg_af;
      extern triton::arch::Register x86_reg_cf;
      extern triton::arch::Register x86_reg_df;
      extern triton::arch::Register x86_reg_if;
      extern triton::arch::Register x86_reg_of;
      extern triton::arch::Register x86_reg_pf;
      extern triton::arch::Register x86_reg_sf;
      extern triton::arch::Register x86_reg_tf;
      extern triton::arch::Register x86_reg_zf;

      extern triton::arch::Register x86_reg_ie;
      extern triton::arch::Register x86_reg_de;
      extern triton::arch::Register x86_reg_ze;
      extern triton::arch::Register x86_reg_oe;
      extern triton::arch::Register x86_reg_ue;
      extern triton::arch::Register x86_reg_pe;
      extern triton::arch::Register x86_reg_daz;
      extern triton::arch::Register x86_reg_im;
      extern triton::arch::Register x86_reg_dm;
      extern triton::arch::Register x86_reg_zm;
      extern triton::arch::Register x86_reg_om;
      extern triton::arch::Register x86_reg_um;
      extern triton::arch::Register x86_reg_pm;
      extern triton::arch::Register x86_reg_rl;
      extern triton::arch::Register x86_reg_rh;
      extern triton::arch::Register x86_reg_fz;

      extern triton::arch::Register x86_reg_cs;
      extern triton::arch::Register x86_reg_ds;
      extern triton::arch::Register x86_reg_es;
      extern triton::arch::Register x86_reg_fs;
      extern triton::arch::Register x86_reg_gs;
      extern triton::arch::Register x86_reg_ss;


      //! \class x86Specifications
      /*! \brief The x86Specifications class defines specifications about the x86 and x86_64 CPU */
      class x86Specifications {
        public:
          //! Constructor.
          x86Specifications();

          //! Destructor.
          virtual ~x86Specifications();

          //! Returns all specifications about a register from its ID according to the arch (32 or 64-bits).
          triton::arch::RegisterSpecification getX86RegisterSpecification(triton::uint32 arch, triton::uint32 regId) const;

          //! Converts a capstone's register id to a triton's register id.
          triton::uint32 capstoneRegisterToTritonRegister(triton::uint32 id) const;

          //! Converts a capstone's instruction id to a triton's instruction id.
          triton::uint32 capstoneInstructionToTritonInstruction(triton::uint32 id) const;

          //! Converts a capstone's prefix id to a triton's prefix id.
          triton::uint32 capstonePrefixToTritonPrefix(triton::uint32 id) const;
      };


      //! The list of registers.
      enum registers_e {
        ID_REG_INVALID = 0, //!< invalid = 0

        /* GPR 64-bits */
        ID_REG_RAX, //!< rax
        ID_REG_RBX, //!< rbx
        ID_REG_RCX, //!< rcx
        ID_REG_RDX, //!< rdx
        ID_REG_RDI, //!< rdi
        ID_REG_RSI, //!< rsi
        ID_REG_RBP, //!< rbp
        ID_REG_RSP, //!< rsp
        ID_REG_RIP, //!< rip

        ID_REG_R8, //!< r8
        ID_REG_R8D, //!< r8d
        ID_REG_R8W, //!< r8w
        ID_REG_R8B, //!< r8b

        ID_REG_R9, //!< r9
        ID_REG_R9D, //!< r9d
        ID_REG_R9W, //!< r9w
        ID_REG_R9B, //!< r9b

        ID_REG_R10, //!< r10
        ID_REG_R10D, //!< r10d
        ID_REG_R10W, //!< r10w
        ID_REG_R10B, //!< r10b

        ID_REG_R11, //!< r11
        ID_REG_R11D, //!< r11d
        ID_REG_R11W, //!< r11w
        ID_REG_R11B, //!< r11b

        ID_REG_R12, //!< r12
        ID_REG_R12D, //!< r12d
        ID_REG_R12W, //!< r12w
        ID_REG_R12B, //!< r12b

        ID_REG_R13, //!< r13
        ID_REG_R13D, //!< r13d
        ID_REG_R13W, //!< r13w
        ID_REG_R13B, //!< r13b

        ID_REG_R14, //!< r14
        ID_REG_R14D, //!< r14d
        ID_REG_R14W, //!< r14w
        ID_REG_R14B, //!< r14b

        ID_REG_R15, //!< r15
        ID_REG_R15D, //!< r15d
        ID_REG_R15W, //!< r15w
        ID_REG_R15B, //!< r15b

        /* GPR 32-bits */
        ID_REG_EAX, //!< eax
        ID_REG_AX, //!< ax
        ID_REG_AH, //!< ah
        ID_REG_AL, //!< al

        ID_REG_EBX, //!< ebx
        ID_REG_BX, //!< bx
        ID_REG_BH, //!< bh
        ID_REG_BL, //!< bl

        ID_REG_ECX, //!< ecx
        ID_REG_CX, //!< cx
        ID_REG_CH, //!< ch
        ID_REG_CL, //!< cl

        ID_REG_EDX, //!< edx
        ID_REG_DX, //!< dx
        ID_REG_DH, //!< dh
        ID_REG_DL, //!< dl

        ID_REG_EDI, //!< edi
        ID_REG_DI, //!< di
        ID_REG_DIL, //!< dil

        ID_REG_ESI, //!< esi
        ID_REG_SI, //!< si
        ID_REG_SIL, //!< sil

        ID_REG_EBP, //!< ebp
        ID_REG_BP, //!< bp
        ID_REG_BPL, //!< bpl

        ID_REG_ESP, //!< esp
        ID_REG_SP, //!< sp
        ID_REG_SPL, //!< spl

        ID_REG_EIP, //!< eip
        ID_REG_IP, //!< ip

        ID_REG_EFLAGS, //!< eflags

        /* MMX */
        ID_REG_MM0, //!< mm0
        ID_REG_MM1, //!< mm1
        ID_REG_MM2, //!< mm2
        ID_REG_MM3, //!< mm3
        ID_REG_MM4, //!< mm4
        ID_REG_MM5, //!< mm5
        ID_REG_MM6, //!< mm6
        ID_REG_MM7, //!< mm7

        /* SSE */
        ID_REG_MXCSR, //!< mxcsr
        ID_REG_XMM0, //!< xmm0
        ID_REG_XMM1, //!< xmm1
        ID_REG_XMM2, //!< xmm2
        ID_REG_XMM3, //!< xmm3
        ID_REG_XMM4, //!< xmm4
        ID_REG_XMM5, //!< xmm5
        ID_REG_XMM6, //!< xmm6
        ID_REG_XMM7, //!< xmm7
        ID_REG_XMM8, //!< xmm8
        ID_REG_XMM9, //!< xmm9
        ID_REG_XMM10, //!< xmm10
        ID_REG_XMM11, //!< xmm11
        ID_REG_XMM12, //!< xmm12
        ID_REG_XMM13, //!< xmm13
        ID_REG_XMM14, //!< xmm14
        ID_REG_XMM15, //!< xmm15

        /* AVX-256 */
        ID_REG_YMM0, //!< ymm0
        ID_REG_YMM1, //!< ymm1
        ID_REG_YMM2, //!< ymm2
        ID_REG_YMM3, //!< ymm3
        ID_REG_YMM4, //!< ymm4
        ID_REG_YMM5, //!< ymm5
        ID_REG_YMM6, //!< ymm6
        ID_REG_YMM7, //!< ymm7
        ID_REG_YMM8, //!< ymm8
        ID_REG_YMM9, //!< ymm9
        ID_REG_YMM10, //!< ymm10
        ID_REG_YMM11, //!< ymm11
        ID_REG_YMM12, //!< ymm12
        ID_REG_YMM13, //!< ymm13
        ID_REG_YMM14, //!< ymm14
        ID_REG_YMM15, //!< ymm15

        /* AVX-512 */
        ID_REG_ZMM0, //!< zmm0
        ID_REG_ZMM1, //!< zmm1
        ID_REG_ZMM2, //!< zmm2
        ID_REG_ZMM3, //!< zmm3
        ID_REG_ZMM4, //!< zmm4
        ID_REG_ZMM5, //!< zmm5
        ID_REG_ZMM6, //!< zmm6
        ID_REG_ZMM7, //!< zmm7
        ID_REG_ZMM8, //!< zmm8
        ID_REG_ZMM9, //!< zmm9
        ID_REG_ZMM10, //!< zmm10
        ID_REG_ZMM11, //!< zmm11
        ID_REG_ZMM12, //!< zmm12
        ID_REG_ZMM13, //!< zmm13
        ID_REG_ZMM14, //!< zmm14
        ID_REG_ZMM15, //!< zmm15
        ID_REG_ZMM16, //!< zmm16
        ID_REG_ZMM17, //!< zmm17
        ID_REG_ZMM18, //!< zmm18
        ID_REG_ZMM19, //!< zmm19
        ID_REG_ZMM20, //!< zmm20
        ID_REG_ZMM21, //!< zmm21
        ID_REG_ZMM22, //!< zmm22
        ID_REG_ZMM23, //!< zmm23
        ID_REG_ZMM24, //!< zmm24
        ID_REG_ZMM25, //!< zmm25
        ID_REG_ZMM26, //!< zmm26
        ID_REG_ZMM27, //!< zmm27
        ID_REG_ZMM28, //!< zmm28
        ID_REG_ZMM29, //!< zmm29
        ID_REG_ZMM30, //!< zmm30
        ID_REG_ZMM31, //!< zmm31

        /* Control */
        ID_REG_CR0, //!< cr0
        ID_REG_CR1, //!< cr1
        ID_REG_CR2, //!< cr2
        ID_REG_CR3, //!< cr3
        ID_REG_CR4, //!< cr4
        ID_REG_CR5, //!< cr5
        ID_REG_CR6, //!< cr6
        ID_REG_CR7, //!< cr7
        ID_REG_CR8, //!< cr8
        ID_REG_CR9, //!< cr9
        ID_REG_CR10, //!< cr10
        ID_REG_CR11, //!< cr11
        ID_REG_CR12, //!< cr12
        ID_REG_CR13, //!< cr13
        ID_REG_CR14, //!< cr14
        ID_REG_CR15, //!< cr15

        /* Flags ID used in the Taint and Symbolic Engines */
        ID_REG_AF, //!< af
        ID_REG_CF, //!< cf
        ID_REG_DF, //!< df
        ID_REG_IF, //!< if
        ID_REG_OF, //!< of
        ID_REG_PF, //!< pf
        ID_REG_SF, //!< sf
        ID_REG_TF, //!< tf
        ID_REG_ZF, //!< zf

        /* SSE flags */
        ID_REG_IE,  //!< ie (Invalid Operation Flag)
        ID_REG_DE,  //!< de (Denormal Flag)
        ID_REG_ZE,  //!< ze (Divide By Zero Flag)
        ID_REG_OE,  //!< oe (Overflow Flag)
        ID_REG_UE,  //!< ue (Underflow Flag)
        ID_REG_PE,  //!< pe (Precision Flag)
        ID_REG_DAZ, //!< da (Denormals Are Zero)
        ID_REG_IM,  //!< im (Invalid Operation Mask)
        ID_REG_DM,  //!< dm (Denormal Mask)
        ID_REG_ZM,  //!< zm (Divide By Zero Mask)
        ID_REG_OM,  //!< om (Overflow Mask)
        ID_REG_UM,  //!< um (Underflow Mask)
        ID_REG_PM,  //!< pm (Precision Mask)
        ID_REG_RL,  //!< r- (Round Negative)
        ID_REG_RH,  //!< r+ (Round Positive)
        ID_REG_FZ,  //!< fz (Flush To Zero)

        /* Segments */
        ID_REG_CS,  //!< Code Segment
        ID_REG_DS,  //!< Data Segment
        ID_REG_ES,  //!< Extra Segment
        ID_REG_FS,  //!< F Segment
        ID_REG_GS,  //!< G Segment
        ID_REG_SS,  //!< Stack Segment

        /* Must be the last item */
        ID_REG_LAST_ITEM //!< must be the last item
      };

      //! Global set of registers.
      extern triton::arch::Register* x86_regs[ID_REG_LAST_ITEM];

      /*! \brief The list of prefixes.
       *
       *  \description
       *  Note that `REP` and `REPE` have the some opcode. The `REP`
       *  prefix becomes a `REPE` if the instruction modifies `ZF`.
       */
      enum prefix_e {
        ID_PREFIX_INVALID = 0,  //!< invalid
        ID_PREFIX_LOCK,         //!< LOCK
        ID_PREFIX_REP,          //!< REP
        ID_PREFIX_REPE,         //!< REPE
        ID_PREFIX_REPNE,        //!< REPNE

        /* Must be the last item */
        ID_PREFIX_LAST_ITEM     //!< must be the last item
      };

      //! The list of opcodes.
      enum instructions_e {
        ID_INST_INVALID = 0, //!< invalid

        ID_INS_AAA, //!< AAA
        ID_INS_AAD, //!< AAD
        ID_INS_AAM, //!< AAM
        ID_INS_AAS, //!< AAS
        ID_INS_FABS, //!< FABS
        ID_INS_ADC, //!< ADC
        ID_INS_ADCX, //!< ADCX
        ID_INS_ADD, //!< ADD
        ID_INS_ADDPD, //!< ADDPD
        ID_INS_ADDPS, //!< ADDPS
        ID_INS_ADDSD, //!< ADDSD
        ID_INS_ADDSS, //!< ADDSS
        ID_INS_ADDSUBPD, //!< ADDSUBPD
        ID_INS_ADDSUBPS, //!< ADDSUBPS
        ID_INS_FADD, //!< FADD
        ID_INS_FIADD, //!< FIADD
        ID_INS_FADDP, //!< FADDP
        ID_INS_ADOX, //!< ADOX
        ID_INS_AESDECLAST, //!< AESDECLAST
        ID_INS_AESDEC, //!< AESDEC
        ID_INS_AESENCLAST, //!< AESENCLAST
        ID_INS_AESENC, //!< AESENC
        ID_INS_AESIMC, //!< AESIMC
        ID_INS_AESKEYGENASSIST, //!< AESKEYGENASSIST
        ID_INS_AND, //!< AND
        ID_INS_ANDN, //!< ANDN
        ID_INS_ANDNPD, //!< ANDNPD
        ID_INS_ANDNPS, //!< ANDNPS
        ID_INS_ANDPD, //!< ANDPD
        ID_INS_ANDPS, //!< ANDPS
        ID_INS_ARPL, //!< ARPL
        ID_INS_BEXTR, //!< BEXTR
        ID_INS_BLCFILL, //!< BLCFILL
        ID_INS_BLCI, //!< BLCI
        ID_INS_BLCIC, //!< BLCIC
        ID_INS_BLCMSK, //!< BLCMSK
        ID_INS_BLCS, //!< BLCS
        ID_INS_BLENDPD, //!< BLENDPD
        ID_INS_BLENDPS, //!< BLENDPS
        ID_INS_BLENDVPD, //!< BLENDVPD
        ID_INS_BLENDVPS, //!< BLENDVPS
        ID_INS_BLSFILL, //!< BLSFILL
        ID_INS_BLSI, //!< BLSI
        ID_INS_BLSIC, //!< BLSIC
        ID_INS_BLSMSK, //!< BLSMSK
        ID_INS_BLSR, //!< BLSR
        ID_INS_BOUND, //!< BOUND
        ID_INS_BSF, //!< BSF
        ID_INS_BSR, //!< BSR
        ID_INS_BSWAP, //!< BSWAP
        ID_INS_BT, //!< BT
        ID_INS_BTC, //!< BTC
        ID_INS_BTR, //!< BTR
        ID_INS_BTS, //!< BTS
        ID_INS_BZHI, //!< BZHI
        ID_INS_CALL, //!< CALL
        ID_INS_CBW, //!< CBW
        ID_INS_CDQ, //!< CDQ
        ID_INS_CDQE, //!< CDQE
        ID_INS_FCHS, //!< FCHS
        ID_INS_CLAC, //!< CLAC
        ID_INS_CLC, //!< CLC
        ID_INS_CLD, //!< CLD
        ID_INS_CLFLUSH, //!< CLFLUSH
        ID_INS_CLGI, //!< CLGI
        ID_INS_CLI, //!< CLI
        ID_INS_CLTS, //!< CLTS
        ID_INS_CMC, //!< CMC
        ID_INS_CMOVA, //!< CMOVA
        ID_INS_CMOVAE, //!< CMOVAE
        ID_INS_CMOVB, //!< CMOVB
        ID_INS_CMOVBE, //!< CMOVBE
        ID_INS_FCMOVBE, //!< FCMOVBE
        ID_INS_FCMOVB, //!< FCMOVB
        ID_INS_CMOVE, //!< CMOVE
        ID_INS_FCMOVE, //!< FCMOVE
        ID_INS_CMOVG, //!< CMOVG
        ID_INS_CMOVGE, //!< CMOVGE
        ID_INS_CMOVL, //!< CMOVL
        ID_INS_CMOVLE, //!< CMOVLE
        ID_INS_FCMOVNBE, //!< FCMOVNBE
        ID_INS_FCMOVNB, //!< FCMOVNB
        ID_INS_CMOVNE, //!< CMOVNE
        ID_INS_FCMOVNE, //!< FCMOVNE
        ID_INS_CMOVNO, //!< CMOVNO
        ID_INS_CMOVNP, //!< CMOVNP
        ID_INS_FCMOVNU, //!< FCMOVNU
        ID_INS_CMOVNS, //!< CMOVNS
        ID_INS_CMOVO, //!< CMOVO
        ID_INS_CMOVP, //!< CMOVP
        ID_INS_FCMOVU, //!< FCMOVU
        ID_INS_CMOVS, //!< CMOVS
        ID_INS_CMP, //!< CMP
        ID_INS_CMPPD, //!< CMPPD
        ID_INS_CMPPS, //!< CMPPS
        ID_INS_CMPSB, //!< CMPSB
        ID_INS_CMPSD, //!< CMPSD
        ID_INS_CMPSQ, //!< CMPSQ
        ID_INS_CMPSS, //!< CMPSS
        ID_INS_CMPSW, //!< CMPSW
        ID_INS_CMPXCHG16B, //!< CMPXCHG16B
        ID_INS_CMPXCHG, //!< CMPXCHG
        ID_INS_CMPXCHG8B, //!< CMPXCHG8B
        ID_INS_COMISD, //!< COMISD
        ID_INS_COMISS, //!< COMISS
        ID_INS_FCOMP, //!< FCOMP
        ID_INS_FCOMPI, //!< FCOMPI
        ID_INS_FCOMI, //!< FCOMI
        ID_INS_FCOM, //!< FCOM
        ID_INS_FCOS, //!< FCOS
        ID_INS_CPUID, //!< CPUID
        ID_INS_CQO, //!< CQO
        ID_INS_CRC32, //!< CRC32
        ID_INS_CVTDQ2PD, //!< CVTDQ2PD
        ID_INS_CVTDQ2PS, //!< CVTDQ2PS
        ID_INS_CVTPD2DQ, //!< CVTPD2DQ
        ID_INS_CVTPD2PS, //!< CVTPD2PS
        ID_INS_CVTPS2DQ, //!< CVTPS2DQ
        ID_INS_CVTPS2PD, //!< CVTPS2PD
        ID_INS_CVTSD2SI, //!< CVTSD2SI
        ID_INS_CVTSD2SS, //!< CVTSD2SS
        ID_INS_CVTSI2SD, //!< CVTSI2SD
        ID_INS_CVTSI2SS, //!< CVTSI2SS
        ID_INS_CVTSS2SD, //!< CVTSS2SD
        ID_INS_CVTSS2SI, //!< CVTSS2SI
        ID_INS_CVTTPD2DQ, //!< CVTTPD2DQ
        ID_INS_CVTTPS2DQ, //!< CVTTPS2DQ
        ID_INS_CVTTSD2SI, //!< CVTTSD2SI
        ID_INS_CVTTSS2SI, //!< CVTTSS2SI
        ID_INS_CWD, //!< CWD
        ID_INS_CWDE, //!< CWDE
        ID_INS_DAA, //!< DAA
        ID_INS_DAS, //!< DAS
        ID_INS_DATA16, //!< DATA16
        ID_INS_DEC, //!< DEC
        ID_INS_DIV, //!< DIV
        ID_INS_DIVPD, //!< DIVPD
        ID_INS_DIVPS, //!< DIVPS
        ID_INS_FDIVR, //!< FDIVR
        ID_INS_FIDIVR, //!< FIDIVR
        ID_INS_FDIVRP, //!< FDIVRP
        ID_INS_DIVSD, //!< DIVSD
        ID_INS_DIVSS, //!< DIVSS
        ID_INS_FDIV, //!< FDIV
        ID_INS_FIDIV, //!< FIDIV
        ID_INS_FDIVP, //!< FDIVP
        ID_INS_DPPD, //!< DPPD
        ID_INS_DPPS, //!< DPPS
        ID_INS_RET, //!< RET
        ID_INS_ENCLS, //!< ENCLS
        ID_INS_ENCLU, //!< ENCLU
        ID_INS_ENTER, //!< ENTER
        ID_INS_EXTRACTPS, //!< EXTRACTPS
        ID_INS_EXTRQ, //!< EXTRQ
        ID_INS_F2XM1, //!< F2XM1
        ID_INS_LCALL, //!< LCALL
        ID_INS_LJMP, //!< LJMP
        ID_INS_FBLD, //!< FBLD
        ID_INS_FBSTP, //!< FBSTP
        ID_INS_FCOMPP, //!< FCOMPP
        ID_INS_FDECSTP, //!< FDECSTP
        ID_INS_FEMMS, //!< FEMMS
        ID_INS_FFREE, //!< FFREE
        ID_INS_FICOM, //!< FICOM
        ID_INS_FICOMP, //!< FICOMP
        ID_INS_FINCSTP, //!< FINCSTP
        ID_INS_FLDCW, //!< FLDCW
        ID_INS_FLDENV, //!< FLDENV
        ID_INS_FLDL2E, //!< FLDL2E
        ID_INS_FLDL2T, //!< FLDL2T
        ID_INS_FLDLG2, //!< FLDLG2
        ID_INS_FLDLN2, //!< FLDLN2
        ID_INS_FLDPI, //!< FLDPI
        ID_INS_FNCLEX, //!< FNCLEX
        ID_INS_FNINIT, //!< FNINIT
        ID_INS_FNOP, //!< FNOP
        ID_INS_FNSTCW, //!< FNSTCW
        ID_INS_FNSTSW, //!< FNSTSW
        ID_INS_FPATAN, //!< FPATAN
        ID_INS_FPREM, //!< FPREM
        ID_INS_FPREM1, //!< FPREM1
        ID_INS_FPTAN, //!< FPTAN
        ID_INS_FRNDINT, //!< FRNDINT
        ID_INS_FRSTOR, //!< FRSTOR
        ID_INS_FNSAVE, //!< FNSAVE
        ID_INS_FSCALE, //!< FSCALE
        ID_INS_FSETPM, //!< FSETPM
        ID_INS_FSINCOS, //!< FSINCOS
        ID_INS_FNSTENV, //!< FNSTENV
        ID_INS_FXAM, //!< FXAM
        ID_INS_FXRSTOR, //!< FXRSTOR
        ID_INS_FXRSTOR64, //!< FXRSTOR64
        ID_INS_FXSAVE, //!< FXSAVE
        ID_INS_FXSAVE64, //!< FXSAVE64
        ID_INS_FXTRACT, //!< FXTRACT
        ID_INS_FYL2X, //!< FYL2X
        ID_INS_FYL2XP1, //!< FYL2XP1
        ID_INS_MOVAPD, //!< MOVAPD
        ID_INS_MOVAPS, //!< MOVAPS
        ID_INS_ORPD, //!< ORPD
        ID_INS_ORPS, //!< ORPS
        ID_INS_VMOVAPD, //!< VMOVAPD
        ID_INS_VMOVAPS, //!< VMOVAPS
        ID_INS_XORPD, //!< XORPD
        ID_INS_XORPS, //!< XORPS
        ID_INS_GETSEC, //!< GETSEC
        ID_INS_HADDPD, //!< HADDPD
        ID_INS_HADDPS, //!< HADDPS
        ID_INS_HLT, //!< HLT
        ID_INS_HSUBPD, //!< HSUBPD
        ID_INS_HSUBPS, //!< HSUBPS
        ID_INS_IDIV, //!< IDIV
        ID_INS_FILD, //!< FILD
        ID_INS_IMUL, //!< IMUL
        ID_INS_IN, //!< IN
        ID_INS_INC, //!< INC
        ID_INS_INSB, //!< INSB
        ID_INS_INSERTPS, //!< INSERTPS
        ID_INS_INSERTQ, //!< INSERTQ
        ID_INS_INSD, //!< INSD
        ID_INS_INSW, //!< INSW
        ID_INS_INT, //!< INT
        ID_INS_INT1, //!< INT1
        ID_INS_INT3, //!< INT3
        ID_INS_INTO, //!< INTO
        ID_INS_INVD, //!< INVD
        ID_INS_INVEPT, //!< INVEPT
        ID_INS_INVLPG, //!< INVLPG
        ID_INS_INVLPGA, //!< INVLPGA
        ID_INS_INVPCID, //!< INVPCID
        ID_INS_INVVPID, //!< INVVPID
        ID_INS_IRET, //!< IRET
        ID_INS_IRETD, //!< IRETD
        ID_INS_IRETQ, //!< IRETQ
        ID_INS_FISTTP, //!< FISTTP
        ID_INS_FIST, //!< FIST
        ID_INS_FISTP, //!< FISTP
        ID_INS_UCOMISD, //!< UCOMISD
        ID_INS_UCOMISS, //!< UCOMISS
        ID_INS_VCMP, //!< VCMP
        ID_INS_VCOMISD, //!< VCOMISD
        ID_INS_VCOMISS, //!< VCOMISS
        ID_INS_VCVTSD2SS, //!< VCVTSD2SS
        ID_INS_VCVTSI2SD, //!< VCVTSI2SD
        ID_INS_VCVTSI2SS, //!< VCVTSI2SS
        ID_INS_VCVTSS2SD, //!< VCVTSS2SD
        ID_INS_VCVTTSD2SI, //!< VCVTTSD2SI
        ID_INS_VCVTTSD2USI, //!< VCVTTSD2USI
        ID_INS_VCVTTSS2SI, //!< VCVTTSS2SI
        ID_INS_VCVTTSS2USI, //!< VCVTTSS2USI
        ID_INS_VCVTUSI2SD, //!< VCVTUSI2SD
        ID_INS_VCVTUSI2SS, //!< VCVTUSI2SS
        ID_INS_VUCOMISD, //!< VUCOMISD
        ID_INS_VUCOMISS, //!< VUCOMISS
        ID_INS_JAE, //!< JAE
        ID_INS_JA, //!< JA
        ID_INS_JBE, //!< JBE
        ID_INS_JB, //!< JB
        ID_INS_JCXZ, //!< JCXZ
        ID_INS_JECXZ, //!< JECXZ
        ID_INS_JE, //!< JE
        ID_INS_JGE, //!< JGE
        ID_INS_JG, //!< JG
        ID_INS_JLE, //!< JLE
        ID_INS_JL, //!< JL
        ID_INS_JMP, //!< JMP
        ID_INS_JNE, //!< JNE
        ID_INS_JNO, //!< JNO
        ID_INS_JNP, //!< JNP
        ID_INS_JNS, //!< JNS
        ID_INS_JO, //!< JO
        ID_INS_JP, //!< JP
        ID_INS_JRCXZ, //!< JRCXZ
        ID_INS_JS, //!< JS
        ID_INS_KANDB, //!< KANDB
        ID_INS_KANDD, //!< KANDD
        ID_INS_KANDNB, //!< KANDNB
        ID_INS_KANDND, //!< KANDND
        ID_INS_KANDNQ, //!< KANDNQ
        ID_INS_KANDNW, //!< KANDNW
        ID_INS_KANDQ, //!< KANDQ
        ID_INS_KANDW, //!< KANDW
        ID_INS_KMOVB, //!< KMOVB
        ID_INS_KMOVD, //!< KMOVD
        ID_INS_KMOVQ, //!< KMOVQ
        ID_INS_KMOVW, //!< KMOVW
        ID_INS_KNOTB, //!< KNOTB
        ID_INS_KNOTD, //!< KNOTD
        ID_INS_KNOTQ, //!< KNOTQ
        ID_INS_KNOTW, //!< KNOTW
        ID_INS_KORB, //!< KORB
        ID_INS_KORD, //!< KORD
        ID_INS_KORQ, //!< KORQ
        ID_INS_KORTESTW, //!< KORTESTW
        ID_INS_KORW, //!< KORW
        ID_INS_KSHIFTLW, //!< KSHIFTLW
        ID_INS_KSHIFTRW, //!< KSHIFTRW
        ID_INS_KUNPCKBW, //!< KUNPCKBW
        ID_INS_KXNORB, //!< KXNORB
        ID_INS_KXNORD, //!< KXNORD
        ID_INS_KXNORQ, //!< KXNORQ
        ID_INS_KXNORW, //!< KXNORW
        ID_INS_KXORB, //!< KXORB
        ID_INS_KXORD, //!< KXORD
        ID_INS_KXORQ, //!< KXORQ
        ID_INS_KXORW, //!< KXORW
        ID_INS_LAHF, //!< LAHF
        ID_INS_LAR, //!< LAR
        ID_INS_LDDQU, //!< LDDQU
        ID_INS_LDMXCSR, //!< LDMXCSR
        ID_INS_LDS, //!< LDS
        ID_INS_FLDZ, //!< FLDZ
        ID_INS_FLD1, //!< FLD1
        ID_INS_FLD, //!< FLD
        ID_INS_LEA, //!< LEA
        ID_INS_LEAVE, //!< LEAVE
        ID_INS_LES, //!< LES
        ID_INS_LFENCE, //!< LFENCE
        ID_INS_LFS, //!< LFS
        ID_INS_LGDT, //!< LGDT
        ID_INS_LGS, //!< LGS
        ID_INS_LIDT, //!< LIDT
        ID_INS_LLDT, //!< LLDT
        ID_INS_LMSW, //!< LMSW
        ID_INS_OR, //!< OR
        ID_INS_SUB, //!< SUB
        ID_INS_XOR, //!< XOR
        ID_INS_LODSB, //!< LODSB
        ID_INS_LODSD, //!< LODSD
        ID_INS_LODSQ, //!< LODSQ
        ID_INS_LODSW, //!< LODSW
        ID_INS_LOOP, //!< LOOP
        ID_INS_LOOPE, //!< LOOPE
        ID_INS_LOOPNE, //!< LOOPNE
        ID_INS_RETF, //!< RETF
        ID_INS_RETFQ, //!< RETFQ
        ID_INS_LSL, //!< LSL
        ID_INS_LSS, //!< LSS
        ID_INS_LTR, //!< LTR
        ID_INS_XADD, //!< XADD
        ID_INS_LZCNT, //!< LZCNT
        ID_INS_MASKMOVDQU, //!< MASKMOVDQU
        ID_INS_MAXPD, //!< MAXPD
        ID_INS_MAXPS, //!< MAXPS
        ID_INS_MAXSD, //!< MAXSD
        ID_INS_MAXSS, //!< MAXSS
        ID_INS_MFENCE, //!< MFENCE
        ID_INS_MINPD, //!< MINPD
        ID_INS_MINPS, //!< MINPS
        ID_INS_MINSD, //!< MINSD
        ID_INS_MINSS, //!< MINSS
        ID_INS_CVTPD2PI, //!< CVTPD2PI
        ID_INS_CVTPI2PD, //!< CVTPI2PD
        ID_INS_CVTPI2PS, //!< CVTPI2PS
        ID_INS_CVTPS2PI, //!< CVTPS2PI
        ID_INS_CVTTPD2PI, //!< CVTTPD2PI
        ID_INS_CVTTPS2PI, //!< CVTTPS2PI
        ID_INS_EMMS, //!< EMMS
        ID_INS_MASKMOVQ, //!< MASKMOVQ
        ID_INS_MOVD, //!< MOVD
        ID_INS_MOVDQ2Q, //!< MOVDQ2Q
        ID_INS_MOVNTQ, //!< MOVNTQ
        ID_INS_MOVQ2DQ, //!< MOVQ2DQ
        ID_INS_MOVQ, //!< MOVQ
        ID_INS_PABSB, //!< PABSB
        ID_INS_PABSD, //!< PABSD
        ID_INS_PABSW, //!< PABSW
        ID_INS_PACKSSDW, //!< PACKSSDW
        ID_INS_PACKSSWB, //!< PACKSSWB
        ID_INS_PACKUSWB, //!< PACKUSWB
        ID_INS_PADDB, //!< PADDB
        ID_INS_PADDD, //!< PADDD
        ID_INS_PADDQ, //!< PADDQ
        ID_INS_PADDSB, //!< PADDSB
        ID_INS_PADDSW, //!< PADDSW
        ID_INS_PADDUSB, //!< PADDUSB
        ID_INS_PADDUSW, //!< PADDUSW
        ID_INS_PADDW, //!< PADDW
        ID_INS_PALIGNR, //!< PALIGNR
        ID_INS_PANDN, //!< PANDN
        ID_INS_PAND, //!< PAND
        ID_INS_PAVGB, //!< PAVGB
        ID_INS_PAVGW, //!< PAVGW
        ID_INS_PCMPEQB, //!< PCMPEQB
        ID_INS_PCMPEQD, //!< PCMPEQD
        ID_INS_PCMPEQW, //!< PCMPEQW
        ID_INS_PCMPGTB, //!< PCMPGTB
        ID_INS_PCMPGTD, //!< PCMPGTD
        ID_INS_PCMPGTW, //!< PCMPGTW
        ID_INS_PEXTRW, //!< PEXTRW
        ID_INS_PHADDSW, //!< PHADDSW
        ID_INS_PHADDW, //!< PHADDW
        ID_INS_PHADDD, //!< PHADDD
        ID_INS_PHSUBD, //!< PHSUBD
        ID_INS_PHSUBSW, //!< PHSUBSW
        ID_INS_PHSUBW, //!< PHSUBW
        ID_INS_PINSRW, //!< PINSRW
        ID_INS_PMADDUBSW, //!< PMADDUBSW
        ID_INS_PMADDWD, //!< PMADDWD
        ID_INS_PMAXSW, //!< PMAXSW
        ID_INS_PMAXUB, //!< PMAXUB
        ID_INS_PMINSW, //!< PMINSW
        ID_INS_PMINUB, //!< PMINUB
        ID_INS_PMOVMSKB, //!< PMOVMSKB
        ID_INS_PMULHRSW, //!< PMULHRSW
        ID_INS_PMULHUW, //!< PMULHUW
        ID_INS_PMULHW, //!< PMULHW
        ID_INS_PMULLW, //!< PMULLW
        ID_INS_PMULUDQ, //!< PMULUDQ
        ID_INS_POR, //!< POR
        ID_INS_PSADBW, //!< PSADBW
        ID_INS_PSHUFB, //!< PSHUFB
        ID_INS_PSHUFW, //!< PSHUFW
        ID_INS_PSIGNB, //!< PSIGNB
        ID_INS_PSIGND, //!< PSIGND
        ID_INS_PSIGNW, //!< PSIGNW
        ID_INS_PSLLD, //!< PSLLD
        ID_INS_PSLLQ, //!< PSLLQ
        ID_INS_PSLLW, //!< PSLLW
        ID_INS_PSRAD, //!< PSRAD
        ID_INS_PSRAW, //!< PSRAW
        ID_INS_PSRLD, //!< PSRLD
        ID_INS_PSRLQ, //!< PSRLQ
        ID_INS_PSRLW, //!< PSRLW
        ID_INS_PSUBB, //!< PSUBB
        ID_INS_PSUBD, //!< PSUBD
        ID_INS_PSUBQ, //!< PSUBQ
        ID_INS_PSUBSB, //!< PSUBSB
        ID_INS_PSUBSW, //!< PSUBSW
        ID_INS_PSUBUSB, //!< PSUBUSB
        ID_INS_PSUBUSW, //!< PSUBUSW
        ID_INS_PSUBW, //!< PSUBW
        ID_INS_PUNPCKHBW, //!< PUNPCKHBW
        ID_INS_PUNPCKHDQ, //!< PUNPCKHDQ
        ID_INS_PUNPCKHWD, //!< PUNPCKHWD
        ID_INS_PUNPCKLBW, //!< PUNPCKLBW
        ID_INS_PUNPCKLDQ, //!< PUNPCKLDQ
        ID_INS_PUNPCKLWD, //!< PUNPCKLWD
        ID_INS_PXOR, //!< PXOR
        ID_INS_MONITOR, //!< MONITOR
        ID_INS_MONTMUL, //!< MONTMUL
        ID_INS_MOV, //!< MOV
        ID_INS_MOVABS, //!< MOVABS
        ID_INS_MOVBE, //!< MOVBE
        ID_INS_MOVDDUP, //!< MOVDDUP
        ID_INS_MOVDQA, //!< MOVDQA
        ID_INS_MOVDQU, //!< MOVDQU
        ID_INS_MOVHLPS, //!< MOVHLPS
        ID_INS_MOVHPD, //!< MOVHPD
        ID_INS_MOVHPS, //!< MOVHPS
        ID_INS_MOVLHPS, //!< MOVLHPS
        ID_INS_MOVLPD, //!< MOVLPD
        ID_INS_MOVLPS, //!< MOVLPS
        ID_INS_MOVMSKPD, //!< MOVMSKPD
        ID_INS_MOVMSKPS, //!< MOVMSKPS
        ID_INS_MOVNTDQA, //!< MOVNTDQA
        ID_INS_MOVNTDQ, //!< MOVNTDQ
        ID_INS_MOVNTI, //!< MOVNTI
        ID_INS_MOVNTPD, //!< MOVNTPD
        ID_INS_MOVNTPS, //!< MOVNTPS
        ID_INS_MOVNTSD, //!< MOVNTSD
        ID_INS_MOVNTSS, //!< MOVNTSS
        ID_INS_MOVSB, //!< MOVSB
        ID_INS_MOVSD, //!< MOVSD
        ID_INS_MOVSHDUP, //!< MOVSHDUP
        ID_INS_MOVSLDUP, //!< MOVSLDUP
        ID_INS_MOVSQ, //!< MOVSQ
        ID_INS_MOVSS, //!< MOVSS
        ID_INS_MOVSW, //!< MOVSW
        ID_INS_MOVSX, //!< MOVSX
        ID_INS_MOVSXD, //!< MOVSXD
        ID_INS_MOVUPD, //!< MOVUPD
        ID_INS_MOVUPS, //!< MOVUPS
        ID_INS_MOVZX, //!< MOVZX
        ID_INS_MPSADBW, //!< MPSADBW
        ID_INS_MUL, //!< MUL
        ID_INS_MULPD, //!< MULPD
        ID_INS_MULPS, //!< MULPS
        ID_INS_MULSD, //!< MULSD
        ID_INS_MULSS, //!< MULSS
        ID_INS_MULX, //!< MULX
        ID_INS_FMUL, //!< FMUL
        ID_INS_FIMUL, //!< FIMUL
        ID_INS_FMULP, //!< FMULP
        ID_INS_MWAIT, //!< MWAIT
        ID_INS_NEG, //!< NEG
        ID_INS_NOP, //!< NOP
        ID_INS_NOT, //!< NOT
        ID_INS_OUT, //!< OUT
        ID_INS_OUTSB, //!< OUTSB
        ID_INS_OUTSD, //!< OUTSD
        ID_INS_OUTSW, //!< OUTSW
        ID_INS_PACKUSDW, //!< PACKUSDW
        ID_INS_PAUSE, //!< PAUSE
        ID_INS_PAVGUSB, //!< PAVGUSB
        ID_INS_PBLENDVB, //!< PBLENDVB
        ID_INS_PBLENDW, //!< PBLENDW
        ID_INS_PCLMULQDQ, //!< PCLMULQDQ
        ID_INS_PCMPEQQ, //!< PCMPEQQ
        ID_INS_PCMPESTRI, //!< PCMPESTRI
        ID_INS_PCMPESTRM, //!< PCMPESTRM
        ID_INS_PCMPGTQ, //!< PCMPGTQ
        ID_INS_PCMPISTRI, //!< PCMPISTRI
        ID_INS_PCMPISTRM, //!< PCMPISTRM
        ID_INS_PDEP, //!< PDEP
        ID_INS_PEXT, //!< PEXT
        ID_INS_PEXTRB, //!< PEXTRB
        ID_INS_PEXTRD, //!< PEXTRD
        ID_INS_PEXTRQ, //!< PEXTRQ
        ID_INS_PF2ID, //!< PF2ID
        ID_INS_PF2IW, //!< PF2IW
        ID_INS_PFACC, //!< PFACC
        ID_INS_PFADD, //!< PFADD
        ID_INS_PFCMPEQ, //!< PFCMPEQ
        ID_INS_PFCMPGE, //!< PFCMPGE
        ID_INS_PFCMPGT, //!< PFCMPGT
        ID_INS_PFMAX, //!< PFMAX
        ID_INS_PFMIN, //!< PFMIN
        ID_INS_PFMUL, //!< PFMUL
        ID_INS_PFNACC, //!< PFNACC
        ID_INS_PFPNACC, //!< PFPNACC
        ID_INS_PFRCPIT1, //!< PFRCPIT1
        ID_INS_PFRCPIT2, //!< PFRCPIT2
        ID_INS_PFRCP, //!< PFRCP
        ID_INS_PFRSQIT1, //!< PFRSQIT1
        ID_INS_PFRSQRT, //!< PFRSQRT
        ID_INS_PFSUBR, //!< PFSUBR
        ID_INS_PFSUB, //!< PFSUB
        ID_INS_PHMINPOSUW, //!< PHMINPOSUW
        ID_INS_PI2FD, //!< PI2FD
        ID_INS_PI2FW, //!< PI2FW
        ID_INS_PINSRB, //!< PINSRB
        ID_INS_PINSRD, //!< PINSRD
        ID_INS_PINSRQ, //!< PINSRQ
        ID_INS_PMAXSB, //!< PMAXSB
        ID_INS_PMAXSD, //!< PMAXSD
        ID_INS_PMAXUD, //!< PMAXUD
        ID_INS_PMAXUW, //!< PMAXUW
        ID_INS_PMINSB, //!< PMINSB
        ID_INS_PMINSD, //!< PMINSD
        ID_INS_PMINUD, //!< PMINUD
        ID_INS_PMINUW, //!< PMINUW
        ID_INS_PMOVSXBD, //!< PMOVSXBD
        ID_INS_PMOVSXBQ, //!< PMOVSXBQ
        ID_INS_PMOVSXBW, //!< PMOVSXBW
        ID_INS_PMOVSXDQ, //!< PMOVSXDQ
        ID_INS_PMOVSXWD, //!< PMOVSXWD
        ID_INS_PMOVSXWQ, //!< PMOVSXWQ
        ID_INS_PMOVZXBD, //!< PMOVZXBD
        ID_INS_PMOVZXBQ, //!< PMOVZXBQ
        ID_INS_PMOVZXBW, //!< PMOVZXBW
        ID_INS_PMOVZXDQ, //!< PMOVZXDQ
        ID_INS_PMOVZXWD, //!< PMOVZXWD
        ID_INS_PMOVZXWQ, //!< PMOVZXWQ
        ID_INS_PMULDQ, //!< PMULDQ
        ID_INS_PMULHRW, //!< PMULHRW
        ID_INS_PMULLD, //!< PMULLD
        ID_INS_POP, //!< POP
        ID_INS_POPAW, //!< POPAW
        ID_INS_POPAL, //!< POPAL
        ID_INS_POPCNT, //!< POPCNT
        ID_INS_POPF, //!< POPF
        ID_INS_POPFD, //!< POPFD
        ID_INS_POPFQ, //!< POPFQ
        ID_INS_PREFETCH, //!< PREFETCH
        ID_INS_PREFETCHNTA, //!< PREFETCHNTA
        ID_INS_PREFETCHT0, //!< PREFETCHT0
        ID_INS_PREFETCHT1, //!< PREFETCHT1
        ID_INS_PREFETCHT2, //!< PREFETCHT2
        ID_INS_PREFETCHW, //!< PREFETCHW
        ID_INS_PSHUFD, //!< PSHUFD
        ID_INS_PSHUFHW, //!< PSHUFHW
        ID_INS_PSHUFLW, //!< PSHUFLW
        ID_INS_PSLLDQ, //!< PSLLDQ
        ID_INS_PSRLDQ, //!< PSRLDQ
        ID_INS_PSWAPD, //!< PSWAPD
        ID_INS_PTEST, //!< PTEST
        ID_INS_PUNPCKHQDQ, //!< PUNPCKHQDQ
        ID_INS_PUNPCKLQDQ, //!< PUNPCKLQDQ
        ID_INS_PUSH, //!< PUSH
        ID_INS_PUSHAW, //!< PUSHAW
        ID_INS_PUSHAL, //!< PUSHAL
        ID_INS_PUSHF, //!< PUSHF
        ID_INS_PUSHFD, //!< PUSHFD
        ID_INS_PUSHFQ, //!< PUSHFQ
        ID_INS_RCL, //!< RCL
        ID_INS_RCPPS, //!< RCPPS
        ID_INS_RCPSS, //!< RCPSS
        ID_INS_RCR, //!< RCR
        ID_INS_RDFSBASE, //!< RDFSBASE
        ID_INS_RDGSBASE, //!< RDGSBASE
        ID_INS_RDMSR, //!< RDMSR
        ID_INS_RDPMC, //!< RDPMC
        ID_INS_RDRAND, //!< RDRAND
        ID_INS_RDSEED, //!< RDSEED
        ID_INS_RDTSC, //!< RDTSC
        ID_INS_RDTSCP, //!< RDTSCP
        ID_INS_ROL, //!< ROL
        ID_INS_ROR, //!< ROR
        ID_INS_RORX, //!< RORX
        ID_INS_ROUNDPD, //!< ROUNDPD
        ID_INS_ROUNDPS, //!< ROUNDPS
        ID_INS_ROUNDSD, //!< ROUNDSD
        ID_INS_ROUNDSS, //!< ROUNDSS
        ID_INS_RSM, //!< RSM
        ID_INS_RSQRTPS, //!< RSQRTPS
        ID_INS_RSQRTSS, //!< RSQRTSS
        ID_INS_SAHF, //!< SAHF
        ID_INS_SAL, //!< SAL
        ID_INS_SALC, //!< SALC
        ID_INS_SAR, //!< SAR
        ID_INS_SARX, //!< SARX
        ID_INS_SBB, //!< SBB
        ID_INS_SCASB, //!< SCASB
        ID_INS_SCASD, //!< SCASD
        ID_INS_SCASQ, //!< SCASQ
        ID_INS_SCASW, //!< SCASW
        ID_INS_SETAE, //!< SETAE
        ID_INS_SETA, //!< SETA
        ID_INS_SETBE, //!< SETBE
        ID_INS_SETB, //!< SETB
        ID_INS_SETE, //!< SETE
        ID_INS_SETGE, //!< SETGE
        ID_INS_SETG, //!< SETG
        ID_INS_SETLE, //!< SETLE
        ID_INS_SETL, //!< SETL
        ID_INS_SETNE, //!< SETNE
        ID_INS_SETNO, //!< SETNO
        ID_INS_SETNP, //!< SETNP
        ID_INS_SETNS, //!< SETNS
        ID_INS_SETO, //!< SETO
        ID_INS_SETP, //!< SETP
        ID_INS_SETS, //!< SETS
        ID_INS_SFENCE, //!< SFENCE
        ID_INS_SGDT, //!< SGDT
        ID_INS_SHA1MSG1, //!< SHA1MSG1
        ID_INS_SHA1MSG2, //!< SHA1MSG2
        ID_INS_SHA1NEXTE, //!< SHA1NEXTE
        ID_INS_SHA1RNDS4, //!< SHA1RNDS4
        ID_INS_SHA256MSG1, //!< SHA256MSG1
        ID_INS_SHA256MSG2, //!< SHA256MSG2
        ID_INS_SHA256RNDS2, //!< SHA256RNDS2
        ID_INS_SHL, //!< SHL
        ID_INS_SHLD, //!< SHLD
        ID_INS_SHLX, //!< SHLX
        ID_INS_SHR, //!< SHR
        ID_INS_SHRD, //!< SHRD
        ID_INS_SHRX, //!< SHRX
        ID_INS_SHUFPD, //!< SHUFPD
        ID_INS_SHUFPS, //!< SHUFPS
        ID_INS_SIDT, //!< SIDT
        ID_INS_FSIN, //!< FSIN
        ID_INS_SKINIT, //!< SKINIT
        ID_INS_SLDT, //!< SLDT
        ID_INS_SMSW, //!< SMSW
        ID_INS_SQRTPD, //!< SQRTPD
        ID_INS_SQRTPS, //!< SQRTPS
        ID_INS_SQRTSD, //!< SQRTSD
        ID_INS_SQRTSS, //!< SQRTSS
        ID_INS_FSQRT, //!< FSQRT
        ID_INS_STAC, //!< STAC
        ID_INS_STC, //!< STC
        ID_INS_STD, //!< STD
        ID_INS_STGI, //!< STGI
        ID_INS_STI, //!< STI
        ID_INS_STMXCSR, //!< STMXCSR
        ID_INS_STOSB, //!< STOSB
        ID_INS_STOSD, //!< STOSD
        ID_INS_STOSQ, //!< STOSQ
        ID_INS_STOSW, //!< STOSW
        ID_INS_STR, //!< STR
        ID_INS_FST, //!< FST
        ID_INS_FSTP, //!< FSTP
        ID_INS_FSTPNCE, //!< FSTPNCE
        ID_INS_SUBPD, //!< SUBPD
        ID_INS_SUBPS, //!< SUBPS
        ID_INS_FSUBR, //!< FSUBR
        ID_INS_FISUBR, //!< FISUBR
        ID_INS_FSUBRP, //!< FSUBRP
        ID_INS_SUBSD, //!< SUBSD
        ID_INS_SUBSS, //!< SUBSS
        ID_INS_FSUB, //!< FSUB
        ID_INS_FISUB, //!< FISUB
        ID_INS_FSUBP, //!< FSUBP
        ID_INS_SWAPGS, //!< SWAPGS
        ID_INS_SYSCALL, //!< SYSCALL
        ID_INS_SYSENTER, //!< SYSENTER
        ID_INS_SYSEXIT, //!< SYSEXIT
        ID_INS_SYSRET, //!< SYSRET
        ID_INS_T1MSKC, //!< T1MSKC
        ID_INS_TEST, //!< TEST
        ID_INS_UD2, //!< UD2
        ID_INS_FTST, //!< FTST
        ID_INS_TZCNT, //!< TZCNT
        ID_INS_TZMSK, //!< TZMSK
        ID_INS_FUCOMPI, //!< FUCOMPI
        ID_INS_FUCOMI, //!< FUCOMI
        ID_INS_FUCOMPP, //!< FUCOMPP
        ID_INS_FUCOMP, //!< FUCOMP
        ID_INS_FUCOM, //!< FUCOM
        ID_INS_UD2B, //!< UD2B
        ID_INS_UNPCKHPD, //!< UNPCKHPD
        ID_INS_UNPCKHPS, //!< UNPCKHPS
        ID_INS_UNPCKLPD, //!< UNPCKLPD
        ID_INS_UNPCKLPS, //!< UNPCKLPS
        ID_INS_VADDPD, //!< VADDPD
        ID_INS_VADDPS, //!< VADDPS
        ID_INS_VADDSD, //!< VADDSD
        ID_INS_VADDSS, //!< VADDSS
        ID_INS_VADDSUBPD, //!< VADDSUBPD
        ID_INS_VADDSUBPS, //!< VADDSUBPS
        ID_INS_VAESDECLAST, //!< VAESDECLAST
        ID_INS_VAESDEC, //!< VAESDEC
        ID_INS_VAESENCLAST, //!< VAESENCLAST
        ID_INS_VAESENC, //!< VAESENC
        ID_INS_VAESIMC, //!< VAESIMC
        ID_INS_VAESKEYGENASSIST, //!< VAESKEYGENASSIST
        ID_INS_VALIGND, //!< VALIGND
        ID_INS_VALIGNQ, //!< VALIGNQ
        ID_INS_VANDNPD, //!< VANDNPD
        ID_INS_VANDNPS, //!< VANDNPS
        ID_INS_VANDPD, //!< VANDPD
        ID_INS_VANDPS, //!< VANDPS
        ID_INS_VBLENDMPD, //!< VBLENDMPD
        ID_INS_VBLENDMPS, //!< VBLENDMPS
        ID_INS_VBLENDPD, //!< VBLENDPD
        ID_INS_VBLENDPS, //!< VBLENDPS
        ID_INS_VBLENDVPD, //!< VBLENDVPD
        ID_INS_VBLENDVPS, //!< VBLENDVPS
        ID_INS_VBROADCASTF128, //!< VBROADCASTF128
        ID_INS_VBROADCASTI128, //!< VBROADCASTI128
        ID_INS_VBROADCASTI32X4, //!< VBROADCASTI32X4
        ID_INS_VBROADCASTI64X4, //!< VBROADCASTI64X4
        ID_INS_VBROADCASTSD, //!< VBROADCASTSD
        ID_INS_VBROADCASTSS, //!< VBROADCASTSS
        ID_INS_VCMPPD, //!< VCMPPD
        ID_INS_VCMPPS, //!< VCMPPS
        ID_INS_VCMPSD, //!< VCMPSD
        ID_INS_VCMPSS, //!< VCMPSS
        ID_INS_VCVTDQ2PD, //!< VCVTDQ2PD
        ID_INS_VCVTDQ2PS, //!< VCVTDQ2PS
        ID_INS_VCVTPD2DQX, //!< VCVTPD2DQX
        ID_INS_VCVTPD2DQ, //!< VCVTPD2DQ
        ID_INS_VCVTPD2PSX, //!< VCVTPD2PSX
        ID_INS_VCVTPD2PS, //!< VCVTPD2PS
        ID_INS_VCVTPD2UDQ, //!< VCVTPD2UDQ
        ID_INS_VCVTPH2PS, //!< VCVTPH2PS
        ID_INS_VCVTPS2DQ, //!< VCVTPS2DQ
        ID_INS_VCVTPS2PD, //!< VCVTPS2PD
        ID_INS_VCVTPS2PH, //!< VCVTPS2PH
        ID_INS_VCVTPS2UDQ, //!< VCVTPS2UDQ
        ID_INS_VCVTSD2SI, //!< VCVTSD2SI
        ID_INS_VCVTSD2USI, //!< VCVTSD2USI
        ID_INS_VCVTSS2SI, //!< VCVTSS2SI
        ID_INS_VCVTSS2USI, //!< VCVTSS2USI
        ID_INS_VCVTTPD2DQX, //!< VCVTTPD2DQX
        ID_INS_VCVTTPD2DQ, //!< VCVTTPD2DQ
        ID_INS_VCVTTPD2UDQ, //!< VCVTTPD2UDQ
        ID_INS_VCVTTPS2DQ, //!< VCVTTPS2DQ
        ID_INS_VCVTTPS2UDQ, //!< VCVTTPS2UDQ
        ID_INS_VCVTUDQ2PD, //!< VCVTUDQ2PD
        ID_INS_VCVTUDQ2PS, //!< VCVTUDQ2PS
        ID_INS_VDIVPD, //!< VDIVPD
        ID_INS_VDIVPS, //!< VDIVPS
        ID_INS_VDIVSD, //!< VDIVSD
        ID_INS_VDIVSS, //!< VDIVSS
        ID_INS_VDPPD, //!< VDPPD
        ID_INS_VDPPS, //!< VDPPS
        ID_INS_VERR, //!< VERR
        ID_INS_VERW, //!< VERW
        ID_INS_VEXTRACTF128, //!< VEXTRACTF128
        ID_INS_VEXTRACTF32X4, //!< VEXTRACTF32X4
        ID_INS_VEXTRACTF64X4, //!< VEXTRACTF64X4
        ID_INS_VEXTRACTI128, //!< VEXTRACTI128
        ID_INS_VEXTRACTI32X4, //!< VEXTRACTI32X4
        ID_INS_VEXTRACTI64X4, //!< VEXTRACTI64X4
        ID_INS_VEXTRACTPS, //!< VEXTRACTPS
        ID_INS_VFMADD132PD, //!< VFMADD132PD
        ID_INS_VFMADD132PS, //!< VFMADD132PS
        ID_INS_VFMADD213PD, //!< VFMADD213PD
        ID_INS_VFMADD213PS, //!< VFMADD213PS
        ID_INS_VFMADDPD, //!< VFMADDPD
        ID_INS_VFMADD231PD, //!< VFMADD231PD
        ID_INS_VFMADDPS, //!< VFMADDPS
        ID_INS_VFMADD231PS, //!< VFMADD231PS
        ID_INS_VFMADDSD, //!< VFMADDSD
        ID_INS_VFMADD213SD, //!< VFMADD213SD
        ID_INS_VFMADD132SD, //!< VFMADD132SD
        ID_INS_VFMADD231SD, //!< VFMADD231SD
        ID_INS_VFMADDSS, //!< VFMADDSS
        ID_INS_VFMADD213SS, //!< VFMADD213SS
        ID_INS_VFMADD132SS, //!< VFMADD132SS
        ID_INS_VFMADD231SS, //!< VFMADD231SS
        ID_INS_VFMADDSUB132PD, //!< VFMADDSUB132PD
        ID_INS_VFMADDSUB132PS, //!< VFMADDSUB132PS
        ID_INS_VFMADDSUB213PD, //!< VFMADDSUB213PD
        ID_INS_VFMADDSUB213PS, //!< VFMADDSUB213PS
        ID_INS_VFMADDSUBPD, //!< VFMADDSUBPD
        ID_INS_VFMADDSUB231PD, //!< VFMADDSUB231PD
        ID_INS_VFMADDSUBPS, //!< VFMADDSUBPS
        ID_INS_VFMADDSUB231PS, //!< VFMADDSUB231PS
        ID_INS_VFMSUB132PD, //!< VFMSUB132PD
        ID_INS_VFMSUB132PS, //!< VFMSUB132PS
        ID_INS_VFMSUB213PD, //!< VFMSUB213PD
        ID_INS_VFMSUB213PS, //!< VFMSUB213PS
        ID_INS_VFMSUBADD132PD, //!< VFMSUBADD132PD
        ID_INS_VFMSUBADD132PS, //!< VFMSUBADD132PS
        ID_INS_VFMSUBADD213PD, //!< VFMSUBADD213PD
        ID_INS_VFMSUBADD213PS, //!< VFMSUBADD213PS
        ID_INS_VFMSUBADDPD, //!< VFMSUBADDPD
        ID_INS_VFMSUBADD231PD, //!< VFMSUBADD231PD
        ID_INS_VFMSUBADDPS, //!< VFMSUBADDPS
        ID_INS_VFMSUBADD231PS, //!< VFMSUBADD231PS
        ID_INS_VFMSUBPD, //!< VFMSUBPD
        ID_INS_VFMSUB231PD, //!< VFMSUB231PD
        ID_INS_VFMSUBPS, //!< VFMSUBPS
        ID_INS_VFMSUB231PS, //!< VFMSUB231PS
        ID_INS_VFMSUBSD, //!< VFMSUBSD
        ID_INS_VFMSUB213SD, //!< VFMSUB213SD
        ID_INS_VFMSUB132SD, //!< VFMSUB132SD
        ID_INS_VFMSUB231SD, //!< VFMSUB231SD
        ID_INS_VFMSUBSS, //!< VFMSUBSS
        ID_INS_VFMSUB213SS, //!< VFMSUB213SS
        ID_INS_VFMSUB132SS, //!< VFMSUB132SS
        ID_INS_VFMSUB231SS, //!< VFMSUB231SS
        ID_INS_VFNMADD132PD, //!< VFNMADD132PD
        ID_INS_VFNMADD132PS, //!< VFNMADD132PS
        ID_INS_VFNMADD213PD, //!< VFNMADD213PD
        ID_INS_VFNMADD213PS, //!< VFNMADD213PS
        ID_INS_VFNMADDPD, //!< VFNMADDPD
        ID_INS_VFNMADD231PD, //!< VFNMADD231PD
        ID_INS_VFNMADDPS, //!< VFNMADDPS
        ID_INS_VFNMADD231PS, //!< VFNMADD231PS
        ID_INS_VFNMADDSD, //!< VFNMADDSD
        ID_INS_VFNMADD213SD, //!< VFNMADD213SD
        ID_INS_VFNMADD132SD, //!< VFNMADD132SD
        ID_INS_VFNMADD231SD, //!< VFNMADD231SD
        ID_INS_VFNMADDSS, //!< VFNMADDSS
        ID_INS_VFNMADD213SS, //!< VFNMADD213SS
        ID_INS_VFNMADD132SS, //!< VFNMADD132SS
        ID_INS_VFNMADD231SS, //!< VFNMADD231SS
        ID_INS_VFNMSUB132PD, //!< VFNMSUB132PD
        ID_INS_VFNMSUB132PS, //!< VFNMSUB132PS
        ID_INS_VFNMSUB213PD, //!< VFNMSUB213PD
        ID_INS_VFNMSUB213PS, //!< VFNMSUB213PS
        ID_INS_VFNMSUBPD, //!< VFNMSUBPD
        ID_INS_VFNMSUB231PD, //!< VFNMSUB231PD
        ID_INS_VFNMSUBPS, //!< VFNMSUBPS
        ID_INS_VFNMSUB231PS, //!< VFNMSUB231PS
        ID_INS_VFNMSUBSD, //!< VFNMSUBSD
        ID_INS_VFNMSUB213SD, //!< VFNMSUB213SD
        ID_INS_VFNMSUB132SD, //!< VFNMSUB132SD
        ID_INS_VFNMSUB231SD, //!< VFNMSUB231SD
        ID_INS_VFNMSUBSS, //!< VFNMSUBSS
        ID_INS_VFNMSUB213SS, //!< VFNMSUB213SS
        ID_INS_VFNMSUB132SS, //!< VFNMSUB132SS
        ID_INS_VFNMSUB231SS, //!< VFNMSUB231SS
        ID_INS_VFRCZPD, //!< VFRCZPD
        ID_INS_VFRCZPS, //!< VFRCZPS
        ID_INS_VFRCZSD, //!< VFRCZSD
        ID_INS_VFRCZSS, //!< VFRCZSS
        ID_INS_VORPD, //!< VORPD
        ID_INS_VORPS, //!< VORPS
        ID_INS_VXORPD, //!< VXORPD
        ID_INS_VXORPS, //!< VXORPS
        ID_INS_VGATHERDPD, //!< VGATHERDPD
        ID_INS_VGATHERDPS, //!< VGATHERDPS
        ID_INS_VGATHERPF0DPD, //!< VGATHERPF0DPD
        ID_INS_VGATHERPF0DPS, //!< VGATHERPF0DPS
        ID_INS_VGATHERPF0QPD, //!< VGATHERPF0QPD
        ID_INS_VGATHERPF0QPS, //!< VGATHERPF0QPS
        ID_INS_VGATHERPF1DPD, //!< VGATHERPF1DPD
        ID_INS_VGATHERPF1DPS, //!< VGATHERPF1DPS
        ID_INS_VGATHERPF1QPD, //!< VGATHERPF1QPD
        ID_INS_VGATHERPF1QPS, //!< VGATHERPF1QPS
        ID_INS_VGATHERQPD, //!< VGATHERQPD
        ID_INS_VGATHERQPS, //!< VGATHERQPS
        ID_INS_VHADDPD, //!< VHADDPD
        ID_INS_VHADDPS, //!< VHADDPS
        ID_INS_VHSUBPD, //!< VHSUBPD
        ID_INS_VHSUBPS, //!< VHSUBPS
        ID_INS_VINSERTF128, //!< VINSERTF128
        ID_INS_VINSERTF32X4, //!< VINSERTF32X4
        ID_INS_VINSERTF64X4, //!< VINSERTF64X4
        ID_INS_VINSERTI128, //!< VINSERTI128
        ID_INS_VINSERTI32X4, //!< VINSERTI32X4
        ID_INS_VINSERTI64X4, //!< VINSERTI64X4
        ID_INS_VINSERTPS, //!< VINSERTPS
        ID_INS_VLDDQU, //!< VLDDQU
        ID_INS_VLDMXCSR, //!< VLDMXCSR
        ID_INS_VMASKMOVDQU, //!< VMASKMOVDQU
        ID_INS_VMASKMOVPD, //!< VMASKMOVPD
        ID_INS_VMASKMOVPS, //!< VMASKMOVPS
        ID_INS_VMAXPD, //!< VMAXPD
        ID_INS_VMAXPS, //!< VMAXPS
        ID_INS_VMAXSD, //!< VMAXSD
        ID_INS_VMAXSS, //!< VMAXSS
        ID_INS_VMCALL, //!< VMCALL
        ID_INS_VMCLEAR, //!< VMCLEAR
        ID_INS_VMFUNC, //!< VMFUNC
        ID_INS_VMINPD, //!< VMINPD
        ID_INS_VMINPS, //!< VMINPS
        ID_INS_VMINSD, //!< VMINSD
        ID_INS_VMINSS, //!< VMINSS
        ID_INS_VMLAUNCH, //!< VMLAUNCH
        ID_INS_VMLOAD, //!< VMLOAD
        ID_INS_VMMCALL, //!< VMMCALL
        ID_INS_VMOVQ, //!< VMOVQ
        ID_INS_VMOVDDUP, //!< VMOVDDUP
        ID_INS_VMOVD, //!< VMOVD
        ID_INS_VMOVDQA32, //!< VMOVDQA32
        ID_INS_VMOVDQA64, //!< VMOVDQA64
        ID_INS_VMOVDQA, //!< VMOVDQA
        ID_INS_VMOVDQU16, //!< VMOVDQU16
        ID_INS_VMOVDQU32, //!< VMOVDQU32
        ID_INS_VMOVDQU64, //!< VMOVDQU64
        ID_INS_VMOVDQU8, //!< VMOVDQU8
        ID_INS_VMOVDQU, //!< VMOVDQU
        ID_INS_VMOVHLPS, //!< VMOVHLPS
        ID_INS_VMOVHPD, //!< VMOVHPD
        ID_INS_VMOVHPS, //!< VMOVHPS
        ID_INS_VMOVLHPS, //!< VMOVLHPS
        ID_INS_VMOVLPD, //!< VMOVLPD
        ID_INS_VMOVLPS, //!< VMOVLPS
        ID_INS_VMOVMSKPD, //!< VMOVMSKPD
        ID_INS_VMOVMSKPS, //!< VMOVMSKPS
        ID_INS_VMOVNTDQA, //!< VMOVNTDQA
        ID_INS_VMOVNTDQ, //!< VMOVNTDQ
        ID_INS_VMOVNTPD, //!< VMOVNTPD
        ID_INS_VMOVNTPS, //!< VMOVNTPS
        ID_INS_VMOVSD, //!< VMOVSD
        ID_INS_VMOVSHDUP, //!< VMOVSHDUP
        ID_INS_VMOVSLDUP, //!< VMOVSLDUP
        ID_INS_VMOVSS, //!< VMOVSS
        ID_INS_VMOVUPD, //!< VMOVUPD
        ID_INS_VMOVUPS, //!< VMOVUPS
        ID_INS_VMPSADBW, //!< VMPSADBW
        ID_INS_VMPTRLD, //!< VMPTRLD
        ID_INS_VMPTRST, //!< VMPTRST
        ID_INS_VMREAD, //!< VMREAD
        ID_INS_VMRESUME, //!< VMRESUME
        ID_INS_VMRUN, //!< VMRUN
        ID_INS_VMSAVE, //!< VMSAVE
        ID_INS_VMULPD, //!< VMULPD
        ID_INS_VMULPS, //!< VMULPS
        ID_INS_VMULSD, //!< VMULSD
        ID_INS_VMULSS, //!< VMULSS
        ID_INS_VMWRITE, //!< VMWRITE
        ID_INS_VMXOFF, //!< VMXOFF
        ID_INS_VMXON, //!< VMXON
        ID_INS_VPABSB, //!< VPABSB
        ID_INS_VPABSD, //!< VPABSD
        ID_INS_VPABSQ, //!< VPABSQ
        ID_INS_VPABSW, //!< VPABSW
        ID_INS_VPACKSSDW, //!< VPACKSSDW
        ID_INS_VPACKSSWB, //!< VPACKSSWB
        ID_INS_VPACKUSDW, //!< VPACKUSDW
        ID_INS_VPACKUSWB, //!< VPACKUSWB
        ID_INS_VPADDB, //!< VPADDB
        ID_INS_VPADDD, //!< VPADDD
        ID_INS_VPADDQ, //!< VPADDQ
        ID_INS_VPADDSB, //!< VPADDSB
        ID_INS_VPADDSW, //!< VPADDSW
        ID_INS_VPADDUSB, //!< VPADDUSB
        ID_INS_VPADDUSW, //!< VPADDUSW
        ID_INS_VPADDW, //!< VPADDW
        ID_INS_VPALIGNR, //!< VPALIGNR
        ID_INS_VPANDD, //!< VPANDD
        ID_INS_VPANDND, //!< VPANDND
        ID_INS_VPANDNQ, //!< VPANDNQ
        ID_INS_VPANDN, //!< VPANDN
        ID_INS_VPANDQ, //!< VPANDQ
        ID_INS_VPAND, //!< VPAND
        ID_INS_VPAVGB, //!< VPAVGB
        ID_INS_VPAVGW, //!< VPAVGW
        ID_INS_VPBLENDD, //!< VPBLENDD
        ID_INS_VPBLENDMD, //!< VPBLENDMD
        ID_INS_VPBLENDMQ, //!< VPBLENDMQ
        ID_INS_VPBLENDVB, //!< VPBLENDVB
        ID_INS_VPBLENDW, //!< VPBLENDW
        ID_INS_VPBROADCASTB, //!< VPBROADCASTB
        ID_INS_VPBROADCASTD, //!< VPBROADCASTD
        ID_INS_VPBROADCASTMB2Q, //!< VPBROADCASTMB2Q
        ID_INS_VPBROADCASTMW2D, //!< VPBROADCASTMW2D
        ID_INS_VPBROADCASTQ, //!< VPBROADCASTQ
        ID_INS_VPBROADCASTW, //!< VPBROADCASTW
        ID_INS_VPCLMULQDQ, //!< VPCLMULQDQ
        ID_INS_VPCMOV, //!< VPCMOV
        ID_INS_VPCMP, //!< VPCMP
        ID_INS_VPCMPD, //!< VPCMPD
        ID_INS_VPCMPEQB, //!< VPCMPEQB
        ID_INS_VPCMPEQD, //!< VPCMPEQD
        ID_INS_VPCMPEQQ, //!< VPCMPEQQ
        ID_INS_VPCMPEQW, //!< VPCMPEQW
        ID_INS_VPCMPESTRI, //!< VPCMPESTRI
        ID_INS_VPCMPESTRM, //!< VPCMPESTRM
        ID_INS_VPCMPGTB, //!< VPCMPGTB
        ID_INS_VPCMPGTD, //!< VPCMPGTD
        ID_INS_VPCMPGTQ, //!< VPCMPGTQ
        ID_INS_VPCMPGTW, //!< VPCMPGTW
        ID_INS_VPCMPISTRI, //!< VPCMPISTRI
        ID_INS_VPCMPISTRM, //!< VPCMPISTRM
        ID_INS_VPCMPQ, //!< VPCMPQ
        ID_INS_VPCMPUD, //!< VPCMPUD
        ID_INS_VPCMPUQ, //!< VPCMPUQ
        ID_INS_VPCOMB, //!< VPCOMB
        ID_INS_VPCOMD, //!< VPCOMD
        ID_INS_VPCOMQ, //!< VPCOMQ
        ID_INS_VPCOMUB, //!< VPCOMUB
        ID_INS_VPCOMUD, //!< VPCOMUD
        ID_INS_VPCOMUQ, //!< VPCOMUQ
        ID_INS_VPCOMUW, //!< VPCOMUW
        ID_INS_VPCOMW, //!< VPCOMW
        ID_INS_VPCONFLICTD, //!< VPCONFLICTD
        ID_INS_VPCONFLICTQ, //!< VPCONFLICTQ
        ID_INS_VPERM2F128, //!< VPERM2F128
        ID_INS_VPERM2I128, //!< VPERM2I128
        ID_INS_VPERMD, //!< VPERMD
        ID_INS_VPERMI2D, //!< VPERMI2D
        ID_INS_VPERMI2PD, //!< VPERMI2PD
        ID_INS_VPERMI2PS, //!< VPERMI2PS
        ID_INS_VPERMI2Q, //!< VPERMI2Q
        ID_INS_VPERMIL2PD, //!< VPERMIL2PD
        ID_INS_VPERMIL2PS, //!< VPERMIL2PS
        ID_INS_VPERMILPD, //!< VPERMILPD
        ID_INS_VPERMILPS, //!< VPERMILPS
        ID_INS_VPERMPD, //!< VPERMPD
        ID_INS_VPERMPS, //!< VPERMPS
        ID_INS_VPERMQ, //!< VPERMQ
        ID_INS_VPERMT2D, //!< VPERMT2D
        ID_INS_VPERMT2PD, //!< VPERMT2PD
        ID_INS_VPERMT2PS, //!< VPERMT2PS
        ID_INS_VPERMT2Q, //!< VPERMT2Q
        ID_INS_VPEXTRB, //!< VPEXTRB
        ID_INS_VPEXTRD, //!< VPEXTRD
        ID_INS_VPEXTRQ, //!< VPEXTRQ
        ID_INS_VPEXTRW, //!< VPEXTRW
        ID_INS_VPGATHERDD, //!< VPGATHERDD
        ID_INS_VPGATHERDQ, //!< VPGATHERDQ
        ID_INS_VPGATHERQD, //!< VPGATHERQD
        ID_INS_VPGATHERQQ, //!< VPGATHERQQ
        ID_INS_VPHADDBD, //!< VPHADDBD
        ID_INS_VPHADDBQ, //!< VPHADDBQ
        ID_INS_VPHADDBW, //!< VPHADDBW
        ID_INS_VPHADDDQ, //!< VPHADDDQ
        ID_INS_VPHADDD, //!< VPHADDD
        ID_INS_VPHADDSW, //!< VPHADDSW
        ID_INS_VPHADDUBD, //!< VPHADDUBD
        ID_INS_VPHADDUBQ, //!< VPHADDUBQ
        ID_INS_VPHADDUBW, //!< VPHADDUBW
        ID_INS_VPHADDUDQ, //!< VPHADDUDQ
        ID_INS_VPHADDUWD, //!< VPHADDUWD
        ID_INS_VPHADDUWQ, //!< VPHADDUWQ
        ID_INS_VPHADDWD, //!< VPHADDWD
        ID_INS_VPHADDWQ, //!< VPHADDWQ
        ID_INS_VPHADDW, //!< VPHADDW
        ID_INS_VPHMINPOSUW, //!< VPHMINPOSUW
        ID_INS_VPHSUBBW, //!< VPHSUBBW
        ID_INS_VPHSUBDQ, //!< VPHSUBDQ
        ID_INS_VPHSUBD, //!< VPHSUBD
        ID_INS_VPHSUBSW, //!< VPHSUBSW
        ID_INS_VPHSUBWD, //!< VPHSUBWD
        ID_INS_VPHSUBW, //!< VPHSUBW
        ID_INS_VPINSRB, //!< VPINSRB
        ID_INS_VPINSRD, //!< VPINSRD
        ID_INS_VPINSRQ, //!< VPINSRQ
        ID_INS_VPINSRW, //!< VPINSRW
        ID_INS_VPLZCNTD, //!< VPLZCNTD
        ID_INS_VPLZCNTQ, //!< VPLZCNTQ
        ID_INS_VPMACSDD, //!< VPMACSDD
        ID_INS_VPMACSDQH, //!< VPMACSDQH
        ID_INS_VPMACSDQL, //!< VPMACSDQL
        ID_INS_VPMACSSDD, //!< VPMACSSDD
        ID_INS_VPMACSSDQH, //!< VPMACSSDQH
        ID_INS_VPMACSSDQL, //!< VPMACSSDQL
        ID_INS_VPMACSSWD, //!< VPMACSSWD
        ID_INS_VPMACSSWW, //!< VPMACSSWW
        ID_INS_VPMACSWD, //!< VPMACSWD
        ID_INS_VPMACSWW, //!< VPMACSWW
        ID_INS_VPMADCSSWD, //!< VPMADCSSWD
        ID_INS_VPMADCSWD, //!< VPMADCSWD
        ID_INS_VPMADDUBSW, //!< VPMADDUBSW
        ID_INS_VPMADDWD, //!< VPMADDWD
        ID_INS_VPMASKMOVD, //!< VPMASKMOVD
        ID_INS_VPMASKMOVQ, //!< VPMASKMOVQ
        ID_INS_VPMAXSB, //!< VPMAXSB
        ID_INS_VPMAXSD, //!< VPMAXSD
        ID_INS_VPMAXSQ, //!< VPMAXSQ
        ID_INS_VPMAXSW, //!< VPMAXSW
        ID_INS_VPMAXUB, //!< VPMAXUB
        ID_INS_VPMAXUD, //!< VPMAXUD
        ID_INS_VPMAXUQ, //!< VPMAXUQ
        ID_INS_VPMAXUW, //!< VPMAXUW
        ID_INS_VPMINSB, //!< VPMINSB
        ID_INS_VPMINSD, //!< VPMINSD
        ID_INS_VPMINSQ, //!< VPMINSQ
        ID_INS_VPMINSW, //!< VPMINSW
        ID_INS_VPMINUB, //!< VPMINUB
        ID_INS_VPMINUD, //!< VPMINUD
        ID_INS_VPMINUQ, //!< VPMINUQ
        ID_INS_VPMINUW, //!< VPMINUW
        ID_INS_VPMOVDB, //!< VPMOVDB
        ID_INS_VPMOVDW, //!< VPMOVDW
        ID_INS_VPMOVMSKB, //!< VPMOVMSKB
        ID_INS_VPMOVQB, //!< VPMOVQB
        ID_INS_VPMOVQD, //!< VPMOVQD
        ID_INS_VPMOVQW, //!< VPMOVQW
        ID_INS_VPMOVSDB, //!< VPMOVSDB
        ID_INS_VPMOVSDW, //!< VPMOVSDW
        ID_INS_VPMOVSQB, //!< VPMOVSQB
        ID_INS_VPMOVSQD, //!< VPMOVSQD
        ID_INS_VPMOVSQW, //!< VPMOVSQW
        ID_INS_VPMOVSXBD, //!< VPMOVSXBD
        ID_INS_VPMOVSXBQ, //!< VPMOVSXBQ
        ID_INS_VPMOVSXBW, //!< VPMOVSXBW
        ID_INS_VPMOVSXDQ, //!< VPMOVSXDQ
        ID_INS_VPMOVSXWD, //!< VPMOVSXWD
        ID_INS_VPMOVSXWQ, //!< VPMOVSXWQ
        ID_INS_VPMOVUSDB, //!< VPMOVUSDB
        ID_INS_VPMOVUSDW, //!< VPMOVUSDW
        ID_INS_VPMOVUSQB, //!< VPMOVUSQB
        ID_INS_VPMOVUSQD, //!< VPMOVUSQD
        ID_INS_VPMOVUSQW, //!< VPMOVUSQW
        ID_INS_VPMOVZXBD, //!< VPMOVZXBD
        ID_INS_VPMOVZXBQ, //!< VPMOVZXBQ
        ID_INS_VPMOVZXBW, //!< VPMOVZXBW
        ID_INS_VPMOVZXDQ, //!< VPMOVZXDQ
        ID_INS_VPMOVZXWD, //!< VPMOVZXWD
        ID_INS_VPMOVZXWQ, //!< VPMOVZXWQ
        ID_INS_VPMULDQ, //!< VPMULDQ
        ID_INS_VPMULHRSW, //!< VPMULHRSW
        ID_INS_VPMULHUW, //!< VPMULHUW
        ID_INS_VPMULHW, //!< VPMULHW
        ID_INS_VPMULLD, //!< VPMULLD
        ID_INS_VPMULLW, //!< VPMULLW
        ID_INS_VPMULUDQ, //!< VPMULUDQ
        ID_INS_VPORD, //!< VPORD
        ID_INS_VPORQ, //!< VPORQ
        ID_INS_VPOR, //!< VPOR
        ID_INS_VPPERM, //!< VPPERM
        ID_INS_VPROTB, //!< VPROTB
        ID_INS_VPROTD, //!< VPROTD
        ID_INS_VPROTQ, //!< VPROTQ
        ID_INS_VPROTW, //!< VPROTW
        ID_INS_VPSADBW, //!< VPSADBW
        ID_INS_VPSCATTERDD, //!< VPSCATTERDD
        ID_INS_VPSCATTERDQ, //!< VPSCATTERDQ
        ID_INS_VPSCATTERQD, //!< VPSCATTERQD
        ID_INS_VPSCATTERQQ, //!< VPSCATTERQQ
        ID_INS_VPSHAB, //!< VPSHAB
        ID_INS_VPSHAD, //!< VPSHAD
        ID_INS_VPSHAQ, //!< VPSHAQ
        ID_INS_VPSHAW, //!< VPSHAW
        ID_INS_VPSHLB, //!< VPSHLB
        ID_INS_VPSHLD, //!< VPSHLD
        ID_INS_VPSHLQ, //!< VPSHLQ
        ID_INS_VPSHLW, //!< VPSHLW
        ID_INS_VPSHUFB, //!< VPSHUFB
        ID_INS_VPSHUFD, //!< VPSHUFD
        ID_INS_VPSHUFHW, //!< VPSHUFHW
        ID_INS_VPSHUFLW, //!< VPSHUFLW
        ID_INS_VPSIGNB, //!< VPSIGNB
        ID_INS_VPSIGND, //!< VPSIGND
        ID_INS_VPSIGNW, //!< VPSIGNW
        ID_INS_VPSLLDQ, //!< VPSLLDQ
        ID_INS_VPSLLD, //!< VPSLLD
        ID_INS_VPSLLQ, //!< VPSLLQ
        ID_INS_VPSLLVD, //!< VPSLLVD
        ID_INS_VPSLLVQ, //!< VPSLLVQ
        ID_INS_VPSLLW, //!< VPSLLW
        ID_INS_VPSRAD, //!< VPSRAD
        ID_INS_VPSRAQ, //!< VPSRAQ
        ID_INS_VPSRAVD, //!< VPSRAVD
        ID_INS_VPSRAVQ, //!< VPSRAVQ
        ID_INS_VPSRAW, //!< VPSRAW
        ID_INS_VPSRLDQ, //!< VPSRLDQ
        ID_INS_VPSRLD, //!< VPSRLD
        ID_INS_VPSRLQ, //!< VPSRLQ
        ID_INS_VPSRLVD, //!< VPSRLVD
        ID_INS_VPSRLVQ, //!< VPSRLVQ
        ID_INS_VPSRLW, //!< VPSRLW
        ID_INS_VPSUBB, //!< VPSUBB
        ID_INS_VPSUBD, //!< VPSUBD
        ID_INS_VPSUBQ, //!< VPSUBQ
        ID_INS_VPSUBSB, //!< VPSUBSB
        ID_INS_VPSUBSW, //!< VPSUBSW
        ID_INS_VPSUBUSB, //!< VPSUBUSB
        ID_INS_VPSUBUSW, //!< VPSUBUSW
        ID_INS_VPSUBW, //!< VPSUBW
        ID_INS_VPTESTMD, //!< VPTESTMD
        ID_INS_VPTESTMQ, //!< VPTESTMQ
        ID_INS_VPTESTNMD, //!< VPTESTNMD
        ID_INS_VPTESTNMQ, //!< VPTESTNMQ
        ID_INS_VPTEST, //!< VPTEST
        ID_INS_VPUNPCKHBW, //!< VPUNPCKHBW
        ID_INS_VPUNPCKHDQ, //!< VPUNPCKHDQ
        ID_INS_VPUNPCKHQDQ, //!< VPUNPCKHQDQ
        ID_INS_VPUNPCKHWD, //!< VPUNPCKHWD
        ID_INS_VPUNPCKLBW, //!< VPUNPCKLBW
        ID_INS_VPUNPCKLDQ, //!< VPUNPCKLDQ
        ID_INS_VPUNPCKLQDQ, //!< VPUNPCKLQDQ
        ID_INS_VPUNPCKLWD, //!< VPUNPCKLWD
        ID_INS_VPXORD, //!< VPXORD
        ID_INS_VPXORQ, //!< VPXORQ
        ID_INS_VPXOR, //!< VPXOR
        ID_INS_VRCP14PD, //!< VRCP14PD
        ID_INS_VRCP14PS, //!< VRCP14PS
        ID_INS_VRCP14SD, //!< VRCP14SD
        ID_INS_VRCP14SS, //!< VRCP14SS
        ID_INS_VRCP28PD, //!< VRCP28PD
        ID_INS_VRCP28PS, //!< VRCP28PS
        ID_INS_VRCP28SD, //!< VRCP28SD
        ID_INS_VRCP28SS, //!< VRCP28SS
        ID_INS_VRCPPS, //!< VRCPPS
        ID_INS_VRCPSS, //!< VRCPSS
        ID_INS_VRNDSCALEPD, //!< VRNDSCALEPD
        ID_INS_VRNDSCALEPS, //!< VRNDSCALEPS
        ID_INS_VRNDSCALESD, //!< VRNDSCALESD
        ID_INS_VRNDSCALESS, //!< VRNDSCALESS
        ID_INS_VROUNDPD, //!< VROUNDPD
        ID_INS_VROUNDPS, //!< VROUNDPS
        ID_INS_VROUNDSD, //!< VROUNDSD
        ID_INS_VROUNDSS, //!< VROUNDSS
        ID_INS_VRSQRT14PD, //!< VRSQRT14PD
        ID_INS_VRSQRT14PS, //!< VRSQRT14PS
        ID_INS_VRSQRT14SD, //!< VRSQRT14SD
        ID_INS_VRSQRT14SS, //!< VRSQRT14SS
        ID_INS_VRSQRT28PD, //!< VRSQRT28PD
        ID_INS_VRSQRT28PS, //!< VRSQRT28PS
        ID_INS_VRSQRT28SD, //!< VRSQRT28SD
        ID_INS_VRSQRT28SS, //!< VRSQRT28SS
        ID_INS_VRSQRTPS, //!< VRSQRTPS
        ID_INS_VRSQRTSS, //!< VRSQRTSS
        ID_INS_VSCATTERDPD, //!< VSCATTERDPD
        ID_INS_VSCATTERDPS, //!< VSCATTERDPS
        ID_INS_VSCATTERPF0DPD, //!< VSCATTERPF0DPD
        ID_INS_VSCATTERPF0DPS, //!< VSCATTERPF0DPS
        ID_INS_VSCATTERPF0QPD, //!< VSCATTERPF0QPD
        ID_INS_VSCATTERPF0QPS, //!< VSCATTERPF0QPS
        ID_INS_VSCATTERPF1DPD, //!< VSCATTERPF1DPD
        ID_INS_VSCATTERPF1DPS, //!< VSCATTERPF1DPS
        ID_INS_VSCATTERPF1QPD, //!< VSCATTERPF1QPD
        ID_INS_VSCATTERPF1QPS, //!< VSCATTERPF1QPS
        ID_INS_VSCATTERQPD, //!< VSCATTERQPD
        ID_INS_VSCATTERQPS, //!< VSCATTERQPS
        ID_INS_VSHUFPD, //!< VSHUFPD
        ID_INS_VSHUFPS, //!< VSHUFPS
        ID_INS_VSQRTPD, //!< VSQRTPD
        ID_INS_VSQRTPS, //!< VSQRTPS
        ID_INS_VSQRTSD, //!< VSQRTSD
        ID_INS_VSQRTSS, //!< VSQRTSS
        ID_INS_VSTMXCSR, //!< VSTMXCSR
        ID_INS_VSUBPD, //!< VSUBPD
        ID_INS_VSUBPS, //!< VSUBPS
        ID_INS_VSUBSD, //!< VSUBSD
        ID_INS_VSUBSS, //!< VSUBSS
        ID_INS_VTESTPD, //!< VTESTPD
        ID_INS_VTESTPS, //!< VTESTPS
        ID_INS_VUNPCKHPD, //!< VUNPCKHPD
        ID_INS_VUNPCKHPS, //!< VUNPCKHPS
        ID_INS_VUNPCKLPD, //!< VUNPCKLPD
        ID_INS_VUNPCKLPS, //!< VUNPCKLPS
        ID_INS_VZEROALL, //!< VZEROALL
        ID_INS_VZEROUPPER, //!< VZEROUPPER
        ID_INS_WAIT, //!< WAIT
        ID_INS_WBINVD, //!< WBINVD
        ID_INS_WRFSBASE, //!< WRFSBASE
        ID_INS_WRGSBASE, //!< WRGSBASE
        ID_INS_WRMSR, //!< WRMSR
        ID_INS_XABORT, //!< XABORT
        ID_INS_XACQUIRE, //!< XACQUIRE
        ID_INS_XBEGIN, //!< XBEGIN
        ID_INS_XCHG, //!< XCHG
        ID_INS_FXCH, //!< FXCH
        ID_INS_XCRYPTCBC, //!< XCRYPTCBC
        ID_INS_XCRYPTCFB, //!< XCRYPTCFB
        ID_INS_XCRYPTCTR, //!< XCRYPTCTR
        ID_INS_XCRYPTECB, //!< XCRYPTECB
        ID_INS_XCRYPTOFB, //!< XCRYPTOFB
        ID_INS_XEND, //!< XEND
        ID_INS_XGETBV, //!< XGETBV
        ID_INS_XLATB, //!< XLATB
        ID_INS_XRELEASE, //!< XRELEASE
        ID_INS_XRSTOR, //!< XRSTOR
        ID_INS_XRSTOR64, //!< XRSTOR64
        ID_INS_XSAVE, //!< XSAVE
        ID_INS_XSAVE64, //!< XSAVE64
        ID_INS_XSAVEOPT, //!< XSAVEOPT
        ID_INS_XSAVEOPT64, //!< XSAVEOPT64
        ID_INS_XSETBV, //!< XSETBV
        ID_INS_XSHA1, //!< XSHA1
        ID_INS_XSHA256, //!< XSHA256
        ID_INS_XSTORE, //!< XSTORE
        ID_INS_XTEST, //!< XTEST

        /* Must be the last item */
        ID_INST_LAST_ITEM //!< must be the last item
      };

    /*! @} End of x86 namespace */
    };
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};


//! Temporary INVALID register.
#define TRITON_X86_REG_INVALID  triton::arch::x86::x86_reg_invalid
//! Temporary RAX register.
#define TRITON_X86_REG_RAX      triton::arch::x86::x86_reg_rax
//! Temporary EAX register.
#define TRITON_X86_REG_EAX      triton::arch::x86::x86_reg_eax
//! Temporary AX register.
#define TRITON_X86_REG_AX       triton::arch::x86::x86_reg_ax
//! Temporary AH register.
#define TRITON_X86_REG_AH       triton::arch::x86::x86_reg_ah
//! Temporary AL register.
#define TRITON_X86_REG_AL       triton::arch::x86::x86_reg_al
//! Temporary RBX register.
#define TRITON_X86_REG_RBX      triton::arch::x86::x86_reg_rbx
//! Temporary EBX register.
#define TRITON_X86_REG_EBX      triton::arch::x86::x86_reg_ebx
//! Temporary BX register.
#define TRITON_X86_REG_BX       triton::arch::x86::x86_reg_bx
//! Temporary BH register.
#define TRITON_X86_REG_BH       triton::arch::x86::x86_reg_bh
//! Temporary BL register.
#define TRITON_X86_REG_BL       triton::arch::x86::x86_reg_bl
//! Temporary RCX register.
#define TRITON_X86_REG_RCX      triton::arch::x86::x86_reg_rcx
//! Temporary ECX register.
#define TRITON_X86_REG_ECX      triton::arch::x86::x86_reg_ecx
//! Temporary CX register.
#define TRITON_X86_REG_CX       triton::arch::x86::x86_reg_cx
//! Temporary CH register.
#define TRITON_X86_REG_CH       triton::arch::x86::x86_reg_ch
//! Temporary CL register.
#define TRITON_X86_REG_CL       triton::arch::x86::x86_reg_cl
//! Temporary RDX register.
#define TRITON_X86_REG_RDX      triton::arch::x86::x86_reg_rdx
//! Temporary EDX register.
#define TRITON_X86_REG_EDX      triton::arch::x86::x86_reg_edx
//! Temporary DX register.
#define TRITON_X86_REG_DX       triton::arch::x86::x86_reg_dx
//! Temporary DH register.
#define TRITON_X86_REG_DH       triton::arch::x86::x86_reg_dh
//! Temporary DL register.
#define TRITON_X86_REG_DL       triton::arch::x86::x86_reg_dl
//! Temporary RDI register.
#define TRITON_X86_REG_RDI      triton::arch::x86::x86_reg_rdi
//! Temporary EDI register.
#define TRITON_X86_REG_EDI      triton::arch::x86::x86_reg_edi
//! Temporary DI register.
#define TRITON_X86_REG_DI       triton::arch::x86::x86_reg_di
//! Temporary DIL register.
#define TRITON_X86_REG_DIL      triton::arch::x86::x86_reg_dil
//! Temporary RSI register.
#define TRITON_X86_REG_RSI      triton::arch::x86::x86_reg_rsi
//! Temporary ESI register.
#define TRITON_X86_REG_ESI      triton::arch::x86::x86_reg_esi
//! Temporary SI register.
#define TRITON_X86_REG_SI       triton::arch::x86::x86_reg_si
//! Temporary SIL register.
#define TRITON_X86_REG_SIL      triton::arch::x86::x86_reg_sil
//! Temporary RSP register.
#define TRITON_X86_REG_RSP      triton::arch::x86::x86_reg_rsp
//! Temporary ESP register.
#define TRITON_X86_REG_ESP      triton::arch::x86::x86_reg_esp
//! Temporary SP register.
#define TRITON_X86_REG_SP       triton::arch::x86::x86_reg_sp
//! Temporary SPL register.
#define TRITON_X86_REG_SPL      triton::arch::x86::x86_reg_spl
//! Temporary STACK register.
#define TRITON_X86_REG_STACK    triton::arch::x86::x86_reg_stack
//! Temporary RBP register.
#define TRITON_X86_REG_RBP      triton::arch::x86::x86_reg_rbp
//! Temporary EBP register.
#define TRITON_X86_REG_EBP      triton::arch::x86::x86_reg_ebp
//! Temporary BP register.
#define TRITON_X86_REG_BP       triton::arch::x86::x86_reg_bp
//! Temporary BPL register.
#define TRITON_X86_REG_BPL      triton::arch::x86::x86_reg_bpl
//! Temporary RIP register.
#define TRITON_X86_REG_RIP      triton::arch::x86::x86_reg_rip
//! Temporary EIP register.
#define TRITON_X86_REG_EIP      triton::arch::x86::x86_reg_eip
//! Temporary IP register.
#define TRITON_X86_REG_IP       triton::arch::x86::x86_reg_ip
//! Temporary PC register.
#define TRITON_X86_REG_PC       triton::arch::x86::x86_reg_pc
//! Temporary EFLAGS register.
#define TRITON_X86_REG_EFLAGS   triton::arch::x86::x86_reg_eflags
//! Temporary R8 register.
#define TRITON_X86_REG_R8       triton::arch::x86::x86_reg_r8
//! Temporary R8D register.
#define TRITON_X86_REG_R8D      triton::arch::x86::x86_reg_r8d
//! Temporary R8W register.
#define TRITON_X86_REG_R8W      triton::arch::x86::x86_reg_r8w
//! Temporary R8B register.
#define TRITON_X86_REG_R8B      triton::arch::x86::x86_reg_r8b
//! Temporary R9 register.
#define TRITON_X86_REG_R9       triton::arch::x86::x86_reg_r9
//! Temporary R9D register.
#define TRITON_X86_REG_R9D      triton::arch::x86::x86_reg_r9d
//! Temporary R9W register.
#define TRITON_X86_REG_R9W      triton::arch::x86::x86_reg_r9w
//! Temporary R9B register.
#define TRITON_X86_REG_R9B      triton::arch::x86::x86_reg_r9b
//! Temporary R10 register.
#define TRITON_X86_REG_R10      triton::arch::x86::x86_reg_r10
//! Temporary R10D register.
#define TRITON_X86_REG_R10D     triton::arch::x86::x86_reg_r10d
//! Temporary R10W register.
#define TRITON_X86_REG_R10W     triton::arch::x86::x86_reg_r10w
//! Temporary R10B register.
#define TRITON_X86_REG_R10B     triton::arch::x86::x86_reg_r10b
//! Temporary R11 register.
#define TRITON_X86_REG_R11      triton::arch::x86::x86_reg_r11
//! Temporary R11D register.
#define TRITON_X86_REG_R11D     triton::arch::x86::x86_reg_r11d
//! Temporary R11W register.
#define TRITON_X86_REG_R11W     triton::arch::x86::x86_reg_r11w
//! Temporary R11B register.
#define TRITON_X86_REG_R11B     triton::arch::x86::x86_reg_r11b
//! Temporary R12 register.
#define TRITON_X86_REG_R12      triton::arch::x86::x86_reg_r12
//! Temporary R12D register.
#define TRITON_X86_REG_R12D     triton::arch::x86::x86_reg_r12d
//! Temporary R12W register.
#define TRITON_X86_REG_R12W     triton::arch::x86::x86_reg_r12w
//! Temporary R12B register.
#define TRITON_X86_REG_R12B     triton::arch::x86::x86_reg_r12b
//! Temporary R13 register.
#define TRITON_X86_REG_R13      triton::arch::x86::x86_reg_r13
//! Temporary R13D register.
#define TRITON_X86_REG_R13D     triton::arch::x86::x86_reg_r13d
//! Temporary R13W register.
#define TRITON_X86_REG_R13W     triton::arch::x86::x86_reg_r13w
//! Temporary R13B register.
#define TRITON_X86_REG_R13B     triton::arch::x86::x86_reg_r13b
//! Temporary R14 register.
#define TRITON_X86_REG_R14      triton::arch::x86::x86_reg_r14
//! Temporary R14D register.
#define TRITON_X86_REG_R14D     triton::arch::x86::x86_reg_r14d
//! Temporary R14W register.
#define TRITON_X86_REG_R14W     triton::arch::x86::x86_reg_r14w
//! Temporary R14B register.
#define TRITON_X86_REG_R14B     triton::arch::x86::x86_reg_r14b
//! Temporary R15 register.
#define TRITON_X86_REG_R15      triton::arch::x86::x86_reg_r15
//! Temporary R15D register.
#define TRITON_X86_REG_R15D     triton::arch::x86::x86_reg_r15d
//! Temporary R15W register.
#define TRITON_X86_REG_R15W     triton::arch::x86::x86_reg_r15w
//! Temporary R15B register.
#define TRITON_X86_REG_R15B     triton::arch::x86::x86_reg_r15b
//! Temporary MM0 register.
#define TRITON_X86_REG_MM0      triton::arch::x86::x86_reg_mm0
//! Temporary MM1 register.
#define TRITON_X86_REG_MM1      triton::arch::x86::x86_reg_mm1
//! Temporary MM2 register.
#define TRITON_X86_REG_MM2      triton::arch::x86::x86_reg_mm2
//! Temporary MM3 register.
#define TRITON_X86_REG_MM3      triton::arch::x86::x86_reg_mm3
//! Temporary MM4 register.
#define TRITON_X86_REG_MM4      triton::arch::x86::x86_reg_mm4
//! Temporary MM5 register.
#define TRITON_X86_REG_MM5      triton::arch::x86::x86_reg_mm5
//! Temporary MM6 register.
#define TRITON_X86_REG_MM6      triton::arch::x86::x86_reg_mm6
//! Temporary MM7 register.
#define TRITON_X86_REG_MM7      triton::arch::x86::x86_reg_mm7
//! Temporary XMM0 register.
#define TRITON_X86_REG_XMM0     triton::arch::x86::x86_reg_xmm0
//! Temporary XMM1 register.
#define TRITON_X86_REG_XMM1     triton::arch::x86::x86_reg_xmm1
//! Temporary XMM2 register.
#define TRITON_X86_REG_XMM2     triton::arch::x86::x86_reg_xmm2
//! Temporary XMM3 register.
#define TRITON_X86_REG_XMM3     triton::arch::x86::x86_reg_xmm3
//! Temporary XMM4 register.
#define TRITON_X86_REG_XMM4     triton::arch::x86::x86_reg_xmm4
//! Temporary XMM5 register.
#define TRITON_X86_REG_XMM5     triton::arch::x86::x86_reg_xmm5
//! Temporary XMM6 register.
#define TRITON_X86_REG_XMM6     triton::arch::x86::x86_reg_xmm6
//! Temporary XMM7 register.
#define TRITON_X86_REG_XMM7     triton::arch::x86::x86_reg_xmm7
//! Temporary XMM8 register.
#define TRITON_X86_REG_XMM8     triton::arch::x86::x86_reg_xmm8
//! Temporary XMM9 register.
#define TRITON_X86_REG_XMM9     triton::arch::x86::x86_reg_xmm9
//! Temporary XMM10 register.
#define TRITON_X86_REG_XMM10    triton::arch::x86::x86_reg_xmm10
//! Temporary XMM11 register.
#define TRITON_X86_REG_XMM11    triton::arch::x86::x86_reg_xmm11
//! Temporary XMM12 register.
#define TRITON_X86_REG_XMM12    triton::arch::x86::x86_reg_xmm12
//! Temporary XMM13 register.
#define TRITON_X86_REG_XMM13    triton::arch::x86::x86_reg_xmm13
//! Temporary XMM14 register.
#define TRITON_X86_REG_XMM14    triton::arch::x86::x86_reg_xmm14
//! Temporary XMM15 register.
#define TRITON_X86_REG_XMM15    triton::arch::x86::x86_reg_xmm15
//! Temporary YMM0 register.
#define TRITON_X86_REG_YMM0     triton::arch::x86::x86_reg_ymm0
//! Temporary YMM1 register.
#define TRITON_X86_REG_YMM1     triton::arch::x86::x86_reg_ymm1
//! Temporary YMM2 register.
#define TRITON_X86_REG_YMM2     triton::arch::x86::x86_reg_ymm2
//! Temporary YMM3 register.
#define TRITON_X86_REG_YMM3     triton::arch::x86::x86_reg_ymm3
//! Temporary YMM4 register.
#define TRITON_X86_REG_YMM4     triton::arch::x86::x86_reg_ymm4
//! Temporary YMM5 register.
#define TRITON_X86_REG_YMM5     triton::arch::x86::x86_reg_ymm5
//! Temporary YMM6 register.
#define TRITON_X86_REG_YMM6     triton::arch::x86::x86_reg_ymm6
//! Temporary YMM7 register.
#define TRITON_X86_REG_YMM7     triton::arch::x86::x86_reg_ymm7
//! Temporary YMM8 register.
#define TRITON_X86_REG_YMM8     triton::arch::x86::x86_reg_ymm8
//! Temporary YMM9 register.
#define TRITON_X86_REG_YMM9     triton::arch::x86::x86_reg_ymm9
//! Temporary YMM10 register.
#define TRITON_X86_REG_YMM10    triton::arch::x86::x86_reg_ymm10
//! Temporary YMM11 register.
#define TRITON_X86_REG_YMM11    triton::arch::x86::x86_reg_ymm11
//! Temporary YMM12 register.
#define TRITON_X86_REG_YMM12    triton::arch::x86::x86_reg_ymm12
//! Temporary YMM13 register.
#define TRITON_X86_REG_YMM13    triton::arch::x86::x86_reg_ymm13
//! Temporary YMM14 register.
#define TRITON_X86_REG_YMM14    triton::arch::x86::x86_reg_ymm14
//! Temporary YMM15 register.
#define TRITON_X86_REG_YMM15    triton::arch::x86::x86_reg_ymm15
//! Temporary ZMM0 register.
#define TRITON_X86_REG_ZMM0     triton::arch::x86::x86_reg_zmm0
//! Temporary ZMM1 register.
#define TRITON_X86_REG_ZMM1     triton::arch::x86::x86_reg_zmm1
//! Temporary ZMM2 register.
#define TRITON_X86_REG_ZMM2     triton::arch::x86::x86_reg_zmm2
//! Temporary ZMM3 register.
#define TRITON_X86_REG_ZMM3     triton::arch::x86::x86_reg_zmm3
//! Temporary ZMM4 register.
#define TRITON_X86_REG_ZMM4     triton::arch::x86::x86_reg_zmm4
//! Temporary ZMM5 register.
#define TRITON_X86_REG_ZMM5     triton::arch::x86::x86_reg_zmm5
//! Temporary ZMM6 register.
#define TRITON_X86_REG_ZMM6     triton::arch::x86::x86_reg_zmm6
//! Temporary ZMM7 register.
#define TRITON_X86_REG_ZMM7     triton::arch::x86::x86_reg_zmm7
//! Temporary ZMM8 register.
#define TRITON_X86_REG_ZMM8     triton::arch::x86::x86_reg_zmm8
//! Temporary ZMM9 register.
#define TRITON_X86_REG_ZMM9     triton::arch::x86::x86_reg_zmm9
//! Temporary ZMM10 register.
#define TRITON_X86_REG_ZMM10    triton::arch::x86::x86_reg_zmm10
//! Temporary ZMM11 register.
#define TRITON_X86_REG_ZMM11    triton::arch::x86::x86_reg_zmm11
//! Temporary ZMM12 register.
#define TRITON_X86_REG_ZMM12    triton::arch::x86::x86_reg_zmm12
//! Temporary ZMM13 register.
#define TRITON_X86_REG_ZMM13    triton::arch::x86::x86_reg_zmm13
//! Temporary ZMM14 register.
#define TRITON_X86_REG_ZMM14    triton::arch::x86::x86_reg_zmm14
//! Temporary ZMM15 register.
#define TRITON_X86_REG_ZMM15    triton::arch::x86::x86_reg_zmm15
//! Temporary ZMM16 register.
#define TRITON_X86_REG_ZMM16    triton::arch::x86::x86_reg_zmm16
//! Temporary ZMM17 register.
#define TRITON_X86_REG_ZMM17    triton::arch::x86::x86_reg_zmm17
//! Temporary ZMM18 register.
#define TRITON_X86_REG_ZMM18    triton::arch::x86::x86_reg_zmm18
//! Temporary ZMM19 register.
#define TRITON_X86_REG_ZMM19    triton::arch::x86::x86_reg_zmm19
//! Temporary ZMM20 register.
#define TRITON_X86_REG_ZMM20    triton::arch::x86::x86_reg_zmm20
//! Temporary ZMM21 register.
#define TRITON_X86_REG_ZMM21    triton::arch::x86::x86_reg_zmm21
//! Temporary ZMM22 register.
#define TRITON_X86_REG_ZMM22    triton::arch::x86::x86_reg_zmm22
//! Temporary ZMM23 register.
#define TRITON_X86_REG_ZMM23    triton::arch::x86::x86_reg_zmm23
//! Temporary ZMM24 register.
#define TRITON_X86_REG_ZMM24    triton::arch::x86::x86_reg_zmm24
//! Temporary ZMM25 register.
#define TRITON_X86_REG_ZMM25    triton::arch::x86::x86_reg_zmm25
//! Temporary ZMM26 register.
#define TRITON_X86_REG_ZMM26    triton::arch::x86::x86_reg_zmm26
//! Temporary ZMM27 register.
#define TRITON_X86_REG_ZMM27    triton::arch::x86::x86_reg_zmm27
//! Temporary ZMM28 register.
#define TRITON_X86_REG_ZMM28    triton::arch::x86::x86_reg_zmm28
//! Temporary ZMM29 register.
#define TRITON_X86_REG_ZMM29    triton::arch::x86::x86_reg_zmm29
//! Temporary ZMM30 register.
#define TRITON_X86_REG_ZMM30    triton::arch::x86::x86_reg_zmm30
//! Temporary ZMM31 register.
#define TRITON_X86_REG_ZMM31    triton::arch::x86::x86_reg_zmm31
//! Temporary MXCSR register.
#define TRITON_X86_REG_MXCSR    triton::arch::x86::x86_reg_mxcsr
//! Temporary CR0 register.
#define TRITON_X86_REG_CR0     triton::arch::x86::x86_reg_cr0
//! Temporary CR1 register.
#define TRITON_X86_REG_CR1     triton::arch::x86::x86_reg_cr1
//! Temporary CR2 register.
#define TRITON_X86_REG_CR2     triton::arch::x86::x86_reg_cr2
//! Temporary CR3 register.
#define TRITON_X86_REG_CR3     triton::arch::x86::x86_reg_cr3
//! Temporary CR4 register.
#define TRITON_X86_REG_CR4     triton::arch::x86::x86_reg_cr4
//! Temporary CR5 register.
#define TRITON_X86_REG_CR5     triton::arch::x86::x86_reg_cr5
//! Temporary CR6 register.
#define TRITON_X86_REG_CR6     triton::arch::x86::x86_reg_cr6
//! Temporary CR7 register.
#define TRITON_X86_REG_CR7     triton::arch::x86::x86_reg_cr7
//! Temporary CR8 register.
#define TRITON_X86_REG_CR8     triton::arch::x86::x86_reg_cr8
//! Temporary CR9 register.
#define TRITON_X86_REG_CR9     triton::arch::x86::x86_reg_cr9
//! Temporary CR10 register.
#define TRITON_X86_REG_CR10    triton::arch::x86::x86_reg_cr10
//! Temporary CR11 register.
#define TRITON_X86_REG_CR11    triton::arch::x86::x86_reg_cr11
//! Temporary CR12 register.
#define TRITON_X86_REG_CR12    triton::arch::x86::x86_reg_cr12
//! Temporary CR13 register.
#define TRITON_X86_REG_CR13    triton::arch::x86::x86_reg_cr13
//! Temporary CR14 register.
#define TRITON_X86_REG_CR14    triton::arch::x86::x86_reg_cr14
//! Temporary CR15 register.
#define TRITON_X86_REG_CR15    triton::arch::x86::x86_reg_cr15
//! Temporary IE register.
#define TRITON_X86_REG_IE       triton::arch::x86::x86_reg_ie
//! Temporary DE register.
#define TRITON_X86_REG_DE       triton::arch::x86::x86_reg_de
//! Temporary ZE register.
#define TRITON_X86_REG_ZE       triton::arch::x86::x86_reg_ze
//! Temporary OE register.
#define TRITON_X86_REG_OE       triton::arch::x86::x86_reg_oe
//! Temporary UE register.
#define TRITON_X86_REG_UE       triton::arch::x86::x86_reg_ue
//! Temporary PE register.
#define TRITON_X86_REG_PE       triton::arch::x86::x86_reg_pe
//! Temporary DAZ register.
#define TRITON_X86_REG_DAZ      triton::arch::x86::x86_reg_daz
//! Temporary IM register.
#define TRITON_X86_REG_IM       triton::arch::x86::x86_reg_im
//! Temporary DM register.
#define TRITON_X86_REG_DM       triton::arch::x86::x86_reg_dm
//! Temporary ZM register.
#define TRITON_X86_REG_ZM       triton::arch::x86::x86_reg_zm
//! Temporary OM register.
#define TRITON_X86_REG_OM       triton::arch::x86::x86_reg_om
//! Temporary UM register.
#define TRITON_X86_REG_UM       triton::arch::x86::x86_reg_um
//! Temporary PM register.
#define TRITON_X86_REG_PM       triton::arch::x86::x86_reg_pm
//! Temporary RL register.
#define TRITON_X86_REG_RL       triton::arch::x86::x86_reg_rl
//! Temporary RH register.
#define TRITON_X86_REG_RH       triton::arch::x86::x86_reg_rh
//! Temporary FZ register.
#define TRITON_X86_REG_FZ       triton::arch::x86::x86_reg_fz
//! Temporary AF register.
#define TRITON_X86_REG_AF       triton::arch::x86::x86_reg_af
//! Temporary CF register.
#define TRITON_X86_REG_CF       triton::arch::x86::x86_reg_cf
//! Temporary DF register.
#define TRITON_X86_REG_DF       triton::arch::x86::x86_reg_df
//! Temporary IF register.
#define TRITON_X86_REG_IF       triton::arch::x86::x86_reg_if
//! Temporary OF register.
#define TRITON_X86_REG_OF       triton::arch::x86::x86_reg_of
//! Temporary PF register.
#define TRITON_X86_REG_PF       triton::arch::x86::x86_reg_pf
//! Temporary SF register.
#define TRITON_X86_REG_SF       triton::arch::x86::x86_reg_sf
//! Temporary TF register.
#define TRITON_X86_REG_TF       triton::arch::x86::x86_reg_tf
//! Temporary ZF register.
#define TRITON_X86_REG_ZF       triton::arch::x86::x86_reg_zf
//! Temporary CS register.
#define TRITON_X86_REG_CS       triton::arch::x86::x86_reg_cs
//! Temporary DS register.
#define TRITON_X86_REG_DS       triton::arch::x86::x86_reg_ds
//! Temporary ES register.
#define TRITON_X86_REG_ES       triton::arch::x86::x86_reg_es
//! Temporary FS register.
#define TRITON_X86_REG_FS       triton::arch::x86::x86_reg_fs
//! Temporary GS register.
#define TRITON_X86_REG_GS       triton::arch::x86::x86_reg_gs
//! Temporary SS register.
#define TRITON_X86_REG_SS       triton::arch::x86::x86_reg_ss

#endif /* TRITON_X86SPECIFICATIONS_H */
