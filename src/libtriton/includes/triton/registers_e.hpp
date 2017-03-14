#ifndef TRITON_REGISTERS_E_H
#define TRITON_REGISTERS_E_H

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
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

namespace std
{
  template <>
  class hash<triton::arch::registers_e>: public hash<uint64_t>
  {};
}

#endif
