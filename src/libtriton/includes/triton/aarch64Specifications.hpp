//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_AARCH64SPECIFICATIONS_H
#define TRITON_AARCH64SPECIFICATIONS_H

#include <unordered_map>

#include <triton/archEnums.hpp>
#include <triton/architecture.hpp>
#include <triton/triton_export.h>
#include <triton/register.hpp>



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

    //! The AArch64 namespace
    namespace aarch64 {
    /*!
     *  \ingroup arch
     *  \addtogroup aarch64
     *  @{
     */

      //! \class AArch64Specifications
      /*! \brief The AArch64Specifications class defines specifications about the AArch64 CPU */
      class AArch64Specifications {
        protected:
          //! List of registers specification available for this architecture.
          std::unordered_map<triton::arch::register_e, const triton::arch::Register> registers_;

        public:
          //! Constructor.
          TRITON_EXPORT AArch64Specifications(triton::arch::architecture_e);

          //! Converts a capstone's register id to a triton's register id.
          TRITON_EXPORT triton::arch::register_e capstoneRegisterToTritonRegister(triton::uint32 id) const;

          //! Converts a capstone's shift id to a triton's shift id.
          TRITON_EXPORT triton::arch::aarch64::shift_e capstoneShiftToTritonShift(triton::uint32 id) const;

          //! Converts a capstone's extend id to a triton's extend id.
          TRITON_EXPORT triton::arch::aarch64::extend_e capstoneExtendToTritonExtend(triton::uint32 id) const;

          //! Converts a capstone's condition id to a triton's condition id.
          TRITON_EXPORT triton::arch::aarch64::condition_e capstoneConditionToTritonCondition(triton::uint32 id) const;

          //! Converts a capstone's instruction id to a triton's instruction id.
          TRITON_EXPORT triton::uint32 capstoneInstructionToTritonInstruction(triton::uint32 id) const;
      };

      //! The list of opcodes.
      enum instruction_e {
        ID_INS_INVALID = 0, //!< invalid
        ID_INS_ABS, //!< abs
        ID_INS_ADC, //!< adc
        ID_INS_ADDHN, //!< addhn
        ID_INS_ADDHN2, //!< addhn2
        ID_INS_ADDP, //!< addp
        ID_INS_ADD, //!< add
        ID_INS_ADDV, //!< addv
        ID_INS_ADR, //!< adr
        ID_INS_ADRP, //!< adrp
        ID_INS_AESD, //!< aesd
        ID_INS_AESE, //!< aese
        ID_INS_AESIMC, //!< aesimc
        ID_INS_AESMC, //!< aesmc
        ID_INS_AND, //!< and
        ID_INS_ASR, //!< asr
        ID_INS_B, //!< b
        ID_INS_BFM, //!< bfm
        ID_INS_BIC, //!< bic
        ID_INS_BIF, //!< bif
        ID_INS_BIT, //!< bit
        ID_INS_BL, //!< bl
        ID_INS_BLR, //!< blr
        ID_INS_BR, //!< br
        ID_INS_BRK, //!< brk
        ID_INS_BSL, //!< bsl
        ID_INS_CBNZ, //!< cbnz
        ID_INS_CBZ, //!< cbz
        ID_INS_CCMN, //!< ccmn
        ID_INS_CCMP, //!< ccmp
        ID_INS_CLREX, //!< clrex
        ID_INS_CLS, //!< cls
        ID_INS_CLZ, //!< clz
        ID_INS_CMEQ, //!< cmeq
        ID_INS_CMGE, //!< cmge
        ID_INS_CMGT, //!< cmgt
        ID_INS_CMHI, //!< cmhi
        ID_INS_CMHS, //!< cmhs
        ID_INS_CMLE, //!< cmle
        ID_INS_CMLT, //!< cmlt
        ID_INS_CMTST, //!< cmtst
        ID_INS_CNT, //!< cnt
        ID_INS_MOV, //!< mov
        ID_INS_CRC32B, //!< crc32b
        ID_INS_CRC32CB, //!< crc32cb
        ID_INS_CRC32CH, //!< crc32ch
        ID_INS_CRC32CW, //!< crc32cw
        ID_INS_CRC32CX, //!< crc32cx
        ID_INS_CRC32H, //!< crc32h
        ID_INS_CRC32W, //!< crc32w
        ID_INS_CRC32X, //!< crc32x
        ID_INS_CSEL, //!< csel
        ID_INS_CSINC, //!< csinc
        ID_INS_CSINV, //!< csinv
        ID_INS_CSNEG, //!< csneg
        ID_INS_DCPS1, //!< dcps1
        ID_INS_DCPS2, //!< dcps2
        ID_INS_DCPS3, //!< dcps3
        ID_INS_DMB, //!< dmb
        ID_INS_DRPS, //!< drps
        ID_INS_DSB, //!< dsb
        ID_INS_DUP, //!< dup
        ID_INS_EON, //!< eon
        ID_INS_EOR, //!< eor
        ID_INS_ERET, //!< eret
        ID_INS_EXTR, //!< extr
        ID_INS_EXT, //!< ext
        ID_INS_FABD, //!< fabd
        ID_INS_FABS, //!< fabs
        ID_INS_FACGE, //!< facge
        ID_INS_FACGT, //!< facgt
        ID_INS_FADD, //!< fadd
        ID_INS_FADDP, //!< faddp
        ID_INS_FCCMP, //!< fccmp
        ID_INS_FCCMPE, //!< fccmpe
        ID_INS_FCMEQ, //!< fcmeq
        ID_INS_FCMGE, //!< fcmge
        ID_INS_FCMGT, //!< fcmgt
        ID_INS_FCMLE, //!< fcmle
        ID_INS_FCMLT, //!< fcmlt
        ID_INS_FCMP, //!< fcmp
        ID_INS_FCMPE, //!< fcmpe
        ID_INS_FCSEL, //!< fcsel
        ID_INS_FCVTAS, //!< fcvtas
        ID_INS_FCVTAU, //!< fcvtau
        ID_INS_FCVT, //!< fcvt
        ID_INS_FCVTL, //!< fcvtl
        ID_INS_FCVTL2, //!< fcvtl2
        ID_INS_FCVTMS, //!< fcvtms
        ID_INS_FCVTMU, //!< fcvtmu
        ID_INS_FCVTNS, //!< fcvtns
        ID_INS_FCVTNU, //!< fcvtnu
        ID_INS_FCVTN, //!< fcvtn
        ID_INS_FCVTN2, //!< fcvtn2
        ID_INS_FCVTPS, //!< fcvtps
        ID_INS_FCVTPU, //!< fcvtpu
        ID_INS_FCVTXN, //!< fcvtxn
        ID_INS_FCVTXN2, //!< fcvtxn2
        ID_INS_FCVTZS, //!< fcvtzs
        ID_INS_FCVTZU, //!< fcvtzu
        ID_INS_FDIV, //!< fdiv
        ID_INS_FMADD, //!< fmadd
        ID_INS_FMAX, //!< fmax
        ID_INS_FMAXNM, //!< fmaxnm
        ID_INS_FMAXNMP, //!< fmaxnmp
        ID_INS_FMAXNMV, //!< fmaxnmv
        ID_INS_FMAXP, //!< fmaxp
        ID_INS_FMAXV, //!< fmaxv
        ID_INS_FMIN, //!< fmin
        ID_INS_FMINNM, //!< fminnm
        ID_INS_FMINNMP, //!< fminnmp
        ID_INS_FMINNMV, //!< fminnmv
        ID_INS_FMINP, //!< fminp
        ID_INS_FMINV, //!< fminv
        ID_INS_FMLA, //!< fmla
        ID_INS_FMLS, //!< fmls
        ID_INS_FMOV, //!< fmov
        ID_INS_FMSUB, //!< fmsub
        ID_INS_FMUL, //!< fmul
        ID_INS_FMULX, //!< fmulx
        ID_INS_FNEG, //!< fneg
        ID_INS_FNMADD, //!< fnmadd
        ID_INS_FNMSUB, //!< fnmsub
        ID_INS_FNMUL, //!< fnmul
        ID_INS_FRECPE, //!< frecpe
        ID_INS_FRECPS, //!< frecps
        ID_INS_FRECPX, //!< frecpx
        ID_INS_FRINTA, //!< frinta
        ID_INS_FRINTI, //!< frinti
        ID_INS_FRINTM, //!< frintm
        ID_INS_FRINTN, //!< frintn
        ID_INS_FRINTP, //!< frintp
        ID_INS_FRINTX, //!< frintx
        ID_INS_FRINTZ, //!< frintz
        ID_INS_FRSQRTE, //!< frsqrte
        ID_INS_FRSQRTS, //!< frsqrts
        ID_INS_FSQRT, //!< fsqrt
        ID_INS_FSUB, //!< fsub
        ID_INS_HINT, //!< hint
        ID_INS_HLT, //!< hlt
        ID_INS_HVC, //!< hvc
        ID_INS_INS, //!< ins
        ID_INS_ISB, //!< isb
        ID_INS_LD1, //!< ld1
        ID_INS_LD1R, //!< ld1r
        ID_INS_LD2R, //!< ld2r
        ID_INS_LD2, //!< ld2
        ID_INS_LD3R, //!< ld3r
        ID_INS_LD3, //!< ld3
        ID_INS_LD4, //!< ld4
        ID_INS_LD4R, //!< ld4r
        ID_INS_LDARB, //!< ldarb
        ID_INS_LDARH, //!< ldarh
        ID_INS_LDAR, //!< ldar
        ID_INS_LDAXP, //!< ldaxp
        ID_INS_LDAXRB, //!< ldaxrb
        ID_INS_LDAXRH, //!< ldaxrh
        ID_INS_LDAXR, //!< ldaxr
        ID_INS_LDNP, //!< ldnp
        ID_INS_LDP, //!< ldp
        ID_INS_LDPSW, //!< ldpsw
        ID_INS_LDRB, //!< ldrb
        ID_INS_LDR, //!< ldr
        ID_INS_LDRH, //!< ldrh
        ID_INS_LDRSB, //!< ldrsb
        ID_INS_LDRSH, //!< ldrsh
        ID_INS_LDRSW, //!< ldrsw
        ID_INS_LDTRB, //!< ldtrb
        ID_INS_LDTRH, //!< ldtrh
        ID_INS_LDTRSB, //!< ldtrsb
        ID_INS_LDTRSH, //!< ldtrsh
        ID_INS_LDTRSW, //!< ldtrsw
        ID_INS_LDTR, //!< ldtr
        ID_INS_LDURB, //!< ldurb
        ID_INS_LDUR, //!< ldur
        ID_INS_LDURH, //!< ldurh
        ID_INS_LDURSB, //!< ldursb
        ID_INS_LDURSH, //!< ldursh
        ID_INS_LDURSW, //!< ldursw
        ID_INS_LDXP, //!< ldxp
        ID_INS_LDXRB, //!< ldxrb
        ID_INS_LDXRH, //!< ldxrh
        ID_INS_LDXR, //!< ldxr
        ID_INS_LSL, //!< lsl
        ID_INS_LSR, //!< lsr
        ID_INS_MADD, //!< madd
        ID_INS_MLA, //!< mla
        ID_INS_MLS, //!< mls
        ID_INS_MOVI, //!< movi
        ID_INS_MOVK, //!< movk
        ID_INS_MOVN, //!< movn
        ID_INS_MOVZ, //!< movz
        ID_INS_MRS, //!< mrs
        ID_INS_MSR, //!< msr
        ID_INS_MSUB, //!< msub
        ID_INS_MUL, //!< mul
        ID_INS_MVNI, //!< mvni
        ID_INS_NEG, //!< neg
        ID_INS_NOT, //!< not
        ID_INS_ORN, //!< orn
        ID_INS_ORR, //!< orr
        ID_INS_PMULL2, //!< pmull2
        ID_INS_PMULL, //!< pmull
        ID_INS_PMUL, //!< pmul
        ID_INS_PRFM, //!< prfm
        ID_INS_PRFUM, //!< prfum
        ID_INS_RADDHN, //!< raddhn
        ID_INS_RADDHN2, //!< raddhn2
        ID_INS_RBIT, //!< rbit
        ID_INS_RET, //!< ret
        ID_INS_REV16, //!< rev16
        ID_INS_REV32, //!< rev32
        ID_INS_REV64, //!< rev64
        ID_INS_REV, //!< rev
        ID_INS_ROR, //!< ror
        ID_INS_RSHRN2, //!< rshrn2
        ID_INS_RSHRN, //!< rshrn
        ID_INS_RSUBHN, //!< rsubhn
        ID_INS_RSUBHN2, //!< rsubhn2
        ID_INS_SABAL2, //!< sabal2
        ID_INS_SABAL, //!< sabal
        ID_INS_SABA, //!< saba
        ID_INS_SABDL2, //!< sabdl2
        ID_INS_SABDL, //!< sabdl
        ID_INS_SABD, //!< sabd
        ID_INS_SADALP, //!< sadalp
        ID_INS_SADDLP, //!< saddlp
        ID_INS_SADDLV, //!< saddlv
        ID_INS_SADDL2, //!< saddl2
        ID_INS_SADDL, //!< saddl
        ID_INS_SADDW2, //!< saddw2
        ID_INS_SADDW, //!< saddw
        ID_INS_SBC, //!< sbc
        ID_INS_SBFM, //!< sbfm
        ID_INS_SCVTF, //!< scvtf
        ID_INS_SDIV, //!< sdiv
        ID_INS_SHA1C, //!< sha1c
        ID_INS_SHA1H, //!< sha1h
        ID_INS_SHA1M, //!< sha1m
        ID_INS_SHA1P, //!< sha1p
        ID_INS_SHA1SU0, //!< sha1su0
        ID_INS_SHA1SU1, //!< sha1su1
        ID_INS_SHA256H2, //!< sha256h2
        ID_INS_SHA256H, //!< sha256h
        ID_INS_SHA256SU0, //!< sha256su0
        ID_INS_SHA256SU1, //!< sha256su1
        ID_INS_SHADD, //!< shadd
        ID_INS_SHLL2, //!< shll2
        ID_INS_SHLL, //!< shll
        ID_INS_SHL, //!< shl
        ID_INS_SHRN2, //!< shrn2
        ID_INS_SHRN, //!< shrn
        ID_INS_SHSUB, //!< shsub
        ID_INS_SLI, //!< sli
        ID_INS_SMADDL, //!< smaddl
        ID_INS_SMAXP, //!< smaxp
        ID_INS_SMAXV, //!< smaxv
        ID_INS_SMAX, //!< smax
        ID_INS_SMC, //!< smc
        ID_INS_SMINP, //!< sminp
        ID_INS_SMINV, //!< sminv
        ID_INS_SMIN, //!< smin
        ID_INS_SMLAL2, //!< smlal2
        ID_INS_SMLAL, //!< smlal
        ID_INS_SMLSL2, //!< smlsl2
        ID_INS_SMLSL, //!< smlsl
        ID_INS_SMOV, //!< smov
        ID_INS_SMSUBL, //!< smsubl
        ID_INS_SMULH, //!< smulh
        ID_INS_SMULL2, //!< smull2
        ID_INS_SMULL, //!< smull
        ID_INS_SQABS, //!< sqabs
        ID_INS_SQADD, //!< sqadd
        ID_INS_SQDMLAL, //!< sqdmlal
        ID_INS_SQDMLAL2, //!< sqdmlal2
        ID_INS_SQDMLSL, //!< sqdmlsl
        ID_INS_SQDMLSL2, //!< sqdmlsl2
        ID_INS_SQDMULH, //!< sqdmulh
        ID_INS_SQDMULL, //!< sqdmull
        ID_INS_SQDMULL2, //!< sqdmull2
        ID_INS_SQNEG, //!< sqneg
        ID_INS_SQRDMULH, //!< sqrdmulh
        ID_INS_SQRSHL, //!< sqrshl
        ID_INS_SQRSHRN, //!< sqrshrn
        ID_INS_SQRSHRN2, //!< sqrshrn2
        ID_INS_SQRSHRUN, //!< sqrshrun
        ID_INS_SQRSHRUN2, //!< sqrshrun2
        ID_INS_SQSHLU, //!< sqshlu
        ID_INS_SQSHL, //!< sqshl
        ID_INS_SQSHRN, //!< sqshrn
        ID_INS_SQSHRN2, //!< sqshrn2
        ID_INS_SQSHRUN, //!< sqshrun
        ID_INS_SQSHRUN2, //!< sqshrun2
        ID_INS_SQSUB, //!< sqsub
        ID_INS_SQXTN2, //!< sqxtn2
        ID_INS_SQXTN, //!< sqxtn
        ID_INS_SQXTUN2, //!< sqxtun2
        ID_INS_SQXTUN, //!< sqxtun
        ID_INS_SRHADD, //!< srhadd
        ID_INS_SRI, //!< sri
        ID_INS_SRSHL, //!< srshl
        ID_INS_SRSHR, //!< srshr
        ID_INS_SRSRA, //!< srsra
        ID_INS_SSHLL2, //!< sshll2
        ID_INS_SSHLL, //!< sshll
        ID_INS_SSHL, //!< sshl
        ID_INS_SSHR, //!< sshr
        ID_INS_SSRA, //!< ssra
        ID_INS_SSUBL2, //!< ssubl2
        ID_INS_SSUBL, //!< ssubl
        ID_INS_SSUBW2, //!< ssubw2
        ID_INS_SSUBW, //!< ssubw
        ID_INS_ST1, //!< st1
        ID_INS_ST2, //!< st2
        ID_INS_ST3, //!< st3
        ID_INS_ST4, //!< st4
        ID_INS_STLRB, //!< stlrb
        ID_INS_STLRH, //!< stlrh
        ID_INS_STLR, //!< stlr
        ID_INS_STLXP, //!< stlxp
        ID_INS_STLXRB, //!< stlxrb
        ID_INS_STLXRH, //!< stlxrh
        ID_INS_STLXR, //!< stlxr
        ID_INS_STNP, //!< stnp
        ID_INS_STP, //!< stp
        ID_INS_STRB, //!< strb
        ID_INS_STR, //!< str
        ID_INS_STRH, //!< strh
        ID_INS_STTRB, //!< sttrb
        ID_INS_STTRH, //!< sttrh
        ID_INS_STTR, //!< sttr
        ID_INS_STURB, //!< sturb
        ID_INS_STUR, //!< stur
        ID_INS_STURH, //!< sturh
        ID_INS_STXP, //!< stxp
        ID_INS_STXRB, //!< stxrb
        ID_INS_STXRH, //!< stxrh
        ID_INS_STXR, //!< stxr
        ID_INS_SUBHN, //!< subhn
        ID_INS_SUBHN2, //!< subhn2
        ID_INS_SUB, //!< sub
        ID_INS_SUQADD, //!< suqadd
        ID_INS_SVC, //!< svc
        ID_INS_SYSL, //!< sysl
        ID_INS_SYS, //!< sys
        ID_INS_TBL, //!< tbl
        ID_INS_TBNZ, //!< tbnz
        ID_INS_TBX, //!< tbx
        ID_INS_TBZ, //!< tbz
        ID_INS_TRN1, //!< trn1
        ID_INS_TRN2, //!< trn2
        ID_INS_UABAL2, //!< uabal2
        ID_INS_UABAL, //!< uabal
        ID_INS_UABA, //!< uaba
        ID_INS_UABDL2, //!< uabdl2
        ID_INS_UABDL, //!< uabdl
        ID_INS_UABD, //!< uabd
        ID_INS_UADALP, //!< uadalp
        ID_INS_UADDLP, //!< uaddlp
        ID_INS_UADDLV, //!< uaddlv
        ID_INS_UADDL2, //!< uaddl2
        ID_INS_UADDL, //!< uaddl
        ID_INS_UADDW2, //!< uaddw2
        ID_INS_UADDW, //!< uaddw
        ID_INS_UBFM, //!< ubfm
        ID_INS_UCVTF, //!< ucvtf
        ID_INS_UDIV, //!< udiv
        ID_INS_UHADD, //!< uhadd
        ID_INS_UHSUB, //!< uhsub
        ID_INS_UMADDL, //!< umaddl
        ID_INS_UMAXP, //!< umaxp
        ID_INS_UMAXV, //!< umaxv
        ID_INS_UMAX, //!< umax
        ID_INS_UMINP, //!< uminp
        ID_INS_UMINV, //!< uminv
        ID_INS_UMIN, //!< umin
        ID_INS_UMLAL2, //!< umlal2
        ID_INS_UMLAL, //!< umlal
        ID_INS_UMLSL2, //!< umlsl2
        ID_INS_UMLSL, //!< umlsl
        ID_INS_UMOV, //!< umov
        ID_INS_UMSUBL, //!< umsubl
        ID_INS_UMULH, //!< umulh
        ID_INS_UMULL2, //!< umull2
        ID_INS_UMULL, //!< umull
        ID_INS_UQADD, //!< uqadd
        ID_INS_UQRSHL, //!< uqrshl
        ID_INS_UQRSHRN, //!< uqrshrn
        ID_INS_UQRSHRN2, //!< uqrshrn2
        ID_INS_UQSHL, //!< uqshl
        ID_INS_UQSHRN, //!< uqshrn
        ID_INS_UQSHRN2, //!< uqshrn2
        ID_INS_UQSUB, //!< uqsub
        ID_INS_UQXTN2, //!< uqxtn2
        ID_INS_UQXTN, //!< uqxtn
        ID_INS_URECPE, //!< urecpe
        ID_INS_URHADD, //!< urhadd
        ID_INS_URSHL, //!< urshl
        ID_INS_URSHR, //!< urshr
        ID_INS_URSQRTE, //!< ursqrte
        ID_INS_URSRA, //!< ursra
        ID_INS_USHLL2, //!< ushll2
        ID_INS_USHLL, //!< ushll
        ID_INS_USHL, //!< ushl
        ID_INS_USHR, //!< ushr
        ID_INS_USQADD, //!< usqadd
        ID_INS_USRA, //!< usra
        ID_INS_USUBL2, //!< usubl2
        ID_INS_USUBL, //!< usubl
        ID_INS_USUBW2, //!< usubw2
        ID_INS_USUBW, //!< usubw
        ID_INS_UZP1, //!< uzp1
        ID_INS_UZP2, //!< uzp2
        ID_INS_XTN2, //!< xtn2
        ID_INS_XTN, //!< xtn
        ID_INS_ZIP1, //!< zip1
        ID_INS_ZIP2, //!< zip2

        // Alias
        ID_INS_MNEG, //!< mneg
        ID_INS_UMNEGL, //!< umnegl
        ID_INS_SMNEGL, //!< smnegl
        ID_INS_NOP, //!< nop
        ID_INS_YIELD, //!< yield
        ID_INS_WFE, //!< wfe
        ID_INS_WFI, //!< wfi
        ID_INS_SEV, //!< sev
        ID_INS_SEVL, //!< sevl
        ID_INS_NGC, //!< ngc
        ID_INS_SBFIZ, //!< sbfiz
        ID_INS_UBFIZ, //!< ubfiz
        ID_INS_SBFX, //!< sbfx
        ID_INS_UBFX, //!< ubfx
        ID_INS_BFI, //!< bfi
        ID_INS_BFXIL, //!< bfxil
        ID_INS_CMN, //!< cmn
        ID_INS_MVN, //!< mvn
        ID_INS_TST, //!< tst
        ID_INS_CSET, //!< cset
        ID_INS_CINC, //!< cinc
        ID_INS_CSETM, //!< csetm
        ID_INS_CINV, //!< cinv
        ID_INS_CNEG, //!< cneg
        ID_INS_SXTB, //!< sxtb
        ID_INS_SXTH, //!< sxth
        ID_INS_SXTW, //!< sxtw
        ID_INS_CMP, //!< cmp
        ID_INS_UXTB, //!< uxtb
        ID_INS_UXTH, //!< uxth
        ID_INS_UXTW, //!< uxtw
        ID_INS_IC, //!< ic
        ID_INS_DC, //!< dc
        ID_INS_AT, //!< at
        ID_INS_TLBI, //!< tlbi

        /* Must be the last item */
        ID_INS_LAST_ITEM //!< must be the last item
      };

    /*! @} End of x86 namespace */
    };
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_AARCH64SPECIFICATIONS_H */
