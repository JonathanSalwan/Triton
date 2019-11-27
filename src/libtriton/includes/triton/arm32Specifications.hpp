//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ARM32SPECIFICATIONS_H
#define TRITON_ARM32SPECIFICATIONS_H

#include <unordered_map>

#include <triton/archEnums.hpp>
#include <triton/architecture.hpp>
#include <triton/dllexport.hpp>
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

    //! The Arm32 namespace
    namespace arm32 {
    /*!
     *  \ingroup arch
     *  \addtogroup arm32
     *  @{
     */

      //! \class Arm32Specifications
      /*! \brief The Arm32Specifications class defines specifications about the Arm32 CPU */
      class Arm32Specifications {
        protected:
          //! List of registers specification available for this architecture.
          std::unordered_map<triton::arch::register_e, const triton::arch::Register> registers_;

        public:
          //! Constructor.
          TRITON_EXPORT Arm32Specifications(triton::arch::architecture_e);

          //! Converts a capstone's register id to a triton's register id.
          TRITON_EXPORT triton::arch::register_e capstoneRegisterToTritonRegister(triton::uint32 id) const;

          //! Converts a capstone's shift id to a triton's shift id.
          TRITON_EXPORT triton::arch::arm::shift_e capstoneShiftToTritonShift(triton::uint32 id) const;

          //! Converts a capstone's condition id to a triton's condition id.
          TRITON_EXPORT triton::arch::arm::condition_e capstoneConditionToTritonCondition(triton::uint32 id) const;

          //! Converts a capstone's instruction id to a triton's instruction id.
          TRITON_EXPORT triton::uint32 capstoneInstructionToTritonInstruction(triton::uint32 id) const;
      };

      //! The list of opcodes.
      enum instruction_e {
        ID_INS_INVALID = 0, //!< invalid

        ID_INS_ADC, //<! adc
        ID_INS_ADD, //<! add
        ID_INS_ADR, //<! adr
        ID_INS_AESD, //<! aesd
        ID_INS_AESE, //<! aese
        ID_INS_AESIMC, //<! aesimc
        ID_INS_AESMC, //<! aesmc
        ID_INS_AND, //<! and
        ID_INS_BFC, //<! bfc
        ID_INS_BFI, //<! bfi
        ID_INS_BIC, //<! bic
        ID_INS_BKPT, //<! bkpt
        ID_INS_BL, //<! bl
        ID_INS_BLX, //<! blx
        ID_INS_BX, //<! bx
        ID_INS_BXJ, //<! bxj
        ID_INS_B,
        ID_INS_CDP, //<! cdp
        ID_INS_CDP2, //<! cdp2
        ID_INS_CLREX, //<! clrex
        ID_INS_CLZ, //<! clz
        ID_INS_CMN, //<! cmn
        ID_INS_CMP, //<! cmp
        ID_INS_CPS, //<! cps
        ID_INS_CRC32B, //<! crc32b
        ID_INS_CRC32CB, //<! crc32cb
        ID_INS_CRC32CH, //<! crc32ch
        ID_INS_CRC32CW, //<! crc32cw
        ID_INS_CRC32H, //<! crc32h
        ID_INS_CRC32W, //<! crc32w
        ID_INS_DBG, //<! dbg
        ID_INS_DMB, //<! dmb
        ID_INS_DSB, //<! dsb
        ID_INS_EOR, //<! eor
        ID_INS_ERET, //<! eret
        ID_INS_VMOV, //<! vmov
        ID_INS_FLDMDBX, //<! fldmdbx
        ID_INS_FLDMIAX, //<! fldmiax
        ID_INS_VMRS, //<! vmrs
        ID_INS_FSTMDBX, //<! fstmdbx
        ID_INS_FSTMIAX, //<! fstmiax
        ID_INS_HINT, //<! hint
        ID_INS_HLT, //<! hlt
        ID_INS_HVC, //<! hvc
        ID_INS_ISB, //<! isb
        ID_INS_LDA, //<! lda
        ID_INS_LDAB, //<! ldab
        ID_INS_LDAEX, //<! ldaex
        ID_INS_LDAEXB, //<! ldaexb
        ID_INS_LDAEXD, //<! ldaexd
        ID_INS_LDAEXH, //<! ldaexh
        ID_INS_LDAH, //<! ldah
        ID_INS_LDC2L, //<! ldc2l
        ID_INS_LDC2, //<! ldc2
        ID_INS_LDCL, //<! ldcl
        ID_INS_LDC, //<! ldc
        ID_INS_LDMDA, //<! ldmda
        ID_INS_LDMDB, //<! ldmdb
        ID_INS_LDM, //<! ldm
        ID_INS_LDMIB, //<! ldmib
        ID_INS_LDRBT, //<! ldrbt
        ID_INS_LDRB, //<! ldrb
        ID_INS_LDRD, //<! ldrd
        ID_INS_LDREX, //<! ldrex
        ID_INS_LDREXB, //<! ldrexb
        ID_INS_LDREXD, //<! ldrexd
        ID_INS_LDREXH, //<! ldrexh
        ID_INS_LDRH, //<! ldrh
        ID_INS_LDRHT, //<! ldrht
        ID_INS_LDRSB, //<! ldrsb
        ID_INS_LDRSBT, //<! ldrsbt
        ID_INS_LDRSH, //<! ldrsh
        ID_INS_LDRSHT, //<! ldrsht
        ID_INS_LDRT, //<! ldrt
        ID_INS_LDR, //<! ldr
        ID_INS_MCR, //<! mcr
        ID_INS_MCR2, //<! mcr2
        ID_INS_MCRR, //<! mcrr
        ID_INS_MCRR2, //<! mcrr2
        ID_INS_MLA, //<! mla
        ID_INS_MLS, //<! mls
        ID_INS_MOV, //<! mov
        ID_INS_MOVT, //<! movt
        ID_INS_MOVW, //<! movw
        ID_INS_MRC, //<! mrc
        ID_INS_MRC2, //<! mrc2
        ID_INS_MRRC, //<! mrrc
        ID_INS_MRRC2, //<! mrrc2
        ID_INS_MRS, //<! mrs
        ID_INS_MSR, //<! msr
        ID_INS_MUL, //<! mul
        ID_INS_MVN, //<! mvn
        ID_INS_ORR, //<! orr
        ID_INS_PKHBT, //<! pkhbt
        ID_INS_PKHTB, //<! pkhtb
        ID_INS_PLDW, //<! pldw
        ID_INS_PLD, //<! pld
        ID_INS_PLI, //<! pli
        ID_INS_QADD, //<! qadd
        ID_INS_QADD16, //<! qadd16
        ID_INS_QADD8, //<! qadd8
        ID_INS_QASX, //<! qasx
        ID_INS_QDADD, //<! qdadd
        ID_INS_QDSUB, //<! qdsub
        ID_INS_QSAX, //<! qsax
        ID_INS_QSUB, //<! qsub
        ID_INS_QSUB16, //<! qsub16
        ID_INS_QSUB8, //<! qsub8
        ID_INS_RBIT, //<! rbit
        ID_INS_REV, //<! rev
        ID_INS_REV16, //<! rev16
        ID_INS_REVSH, //<! revsh
        ID_INS_RFEDA, //<! rfeda
        ID_INS_RFEDB, //<! rfedb
        ID_INS_RFEIA, //<! rfeia
        ID_INS_RFEIB, //<! rfeib
        ID_INS_RSB, //<! rsb
        ID_INS_RSC, //<! rsc
        ID_INS_SADD16, //<! sadd16
        ID_INS_SADD8, //<! sadd8
        ID_INS_SASX, //<! sasx
        ID_INS_SBC, //<! sbc
        ID_INS_SBFX, //<! sbfx
        ID_INS_SDIV, //<! sdiv
        ID_INS_SEL, //<! sel
        ID_INS_SETEND, //<! setend
        ID_INS_SHA1C, //<! sha1c
        ID_INS_SHA1H, //<! sha1h
        ID_INS_SHA1M, //<! sha1m
        ID_INS_SHA1P, //<! sha1p
        ID_INS_SHA1SU0, //<! sha1su0
        ID_INS_SHA1SU1, //<! sha1su1
        ID_INS_SHA256H, //<! sha256h
        ID_INS_SHA256H2, //<! sha256h2
        ID_INS_SHA256SU0, //<! sha256su0
        ID_INS_SHA256SU1, //<! sha256su1
        ID_INS_SHADD16, //<! shadd16
        ID_INS_SHADD8, //<! shadd8
        ID_INS_SHASX, //<! shasx
        ID_INS_SHSAX, //<! shsax
        ID_INS_SHSUB16, //<! shsub16
        ID_INS_SHSUB8, //<! shsub8
        ID_INS_SMC, //<! smc
        ID_INS_SMLABB, //<! smlabb
        ID_INS_SMLABT, //<! smlabt
        ID_INS_SMLAD, //<! smlad
        ID_INS_SMLADX, //<! smladx
        ID_INS_SMLAL, //<! smlal
        ID_INS_SMLALBB, //<! smlalbb
        ID_INS_SMLALBT, //<! smlalbt
        ID_INS_SMLALD, //<! smlald
        ID_INS_SMLALDX, //<! smlaldx
        ID_INS_SMLALTB, //<! smlaltb
        ID_INS_SMLALTT, //<! smlaltt
        ID_INS_SMLATB, //<! smlatb
        ID_INS_SMLATT, //<! smlatt
        ID_INS_SMLAWB, //<! smlawb
        ID_INS_SMLAWT, //<! smlawt
        ID_INS_SMLSD, //<! smlsd
        ID_INS_SMLSDX, //<! smlsdx
        ID_INS_SMLSLD, //<! smlsld
        ID_INS_SMLSLDX, //<! smlsldx
        ID_INS_SMMLA, //<! smmla
        ID_INS_SMMLAR, //<! smmlar
        ID_INS_SMMLS, //<! smmls
        ID_INS_SMMLSR, //<! smmlsr
        ID_INS_SMMUL, //<! smmul
        ID_INS_SMMULR, //<! smmulr
        ID_INS_SMUAD, //<! smuad
        ID_INS_SMUADX, //<! smuadx
        ID_INS_SMULBB, //<! smulbb
        ID_INS_SMULBT, //<! smulbt
        ID_INS_SMULL, //<! smull
        ID_INS_SMULTB, //<! smultb
        ID_INS_SMULTT, //<! smultt
        ID_INS_SMULWB, //<! smulwb
        ID_INS_SMULWT, //<! smulwt
        ID_INS_SMUSD, //<! smusd
        ID_INS_SMUSDX, //<! smusdx
        ID_INS_SRSDA, //<! srsda
        ID_INS_SRSDB, //<! srsdb
        ID_INS_SRSIA, //<! srsia
        ID_INS_SRSIB, //<! srsib
        ID_INS_SSAT, //<! ssat
        ID_INS_SSAT16, //<! ssat16
        ID_INS_SSAX, //<! ssax
        ID_INS_SSUB16, //<! ssub16
        ID_INS_SSUB8, //<! ssub8
        ID_INS_STC2L, //<! stc2l
        ID_INS_STC2, //<! stc2
        ID_INS_STCL, //<! stcl
        ID_INS_STC, //<! stc
        ID_INS_STL, //<! stl
        ID_INS_STLB, //<! stlb
        ID_INS_STLEX, //<! stlex
        ID_INS_STLEXB, //<! stlexb
        ID_INS_STLEXD, //<! stlexd
        ID_INS_STLEXH, //<! stlexh
        ID_INS_STLH, //<! stlh
        ID_INS_STMDA, //<! stmda
        ID_INS_STMDB, //<! stmdb
        ID_INS_STM, //<! stm
        ID_INS_STMIB, //<! stmib
        ID_INS_STRBT, //<! strbt
        ID_INS_STRB, //<! strb
        ID_INS_STRD, //<! strd
        ID_INS_STREX, //<! strex
        ID_INS_STREXB, //<! strexb
        ID_INS_STREXD, //<! strexd
        ID_INS_STREXH, //<! strexh
        ID_INS_STRH, //<! strh
        ID_INS_STRHT, //<! strht
        ID_INS_STRT, //<! strt
        ID_INS_STR, //<! str
        ID_INS_SUB, //<! sub
        ID_INS_SVC, //<! svc
        ID_INS_SWP, //<! swp
        ID_INS_SWPB, //<! swpb
        ID_INS_SXTAB, //<! sxtab
        ID_INS_SXTAB16, //<! sxtab16
        ID_INS_SXTAH, //<! sxtah
        ID_INS_SXTB, //<! sxtb
        ID_INS_SXTB16, //<! sxtb16
        ID_INS_SXTH, //<! sxth
        ID_INS_TEQ, //<! teq
        ID_INS_TRAP, //<! trap
        ID_INS_TST, //<! tst
        ID_INS_UADD16, //<! uadd16
        ID_INS_UADD8, //<! uadd8
        ID_INS_UASX, //<! uasx
        ID_INS_UBFX, //<! ubfx
        ID_INS_UDF, //<! udf
        ID_INS_UDIV, //<! udiv
        ID_INS_UHADD16, //<! uhadd16
        ID_INS_UHADD8, //<! uhadd8
        ID_INS_UHASX, //<! uhasx
        ID_INS_UHSAX, //<! uhsax
        ID_INS_UHSUB16, //<! uhsub16
        ID_INS_UHSUB8, //<! uhsub8
        ID_INS_UMAAL, //<! umaal
        ID_INS_UMLAL, //<! umlal
        ID_INS_UMULL, //<! umull
        ID_INS_UQADD16, //<! uqadd16
        ID_INS_UQADD8, //<! uqadd8
        ID_INS_UQASX, //<! uqasx
        ID_INS_UQSAX, //<! uqsax
        ID_INS_UQSUB16, //<! uqsub16
        ID_INS_UQSUB8, //<! uqsub8
        ID_INS_USAD8, //<! usad8
        ID_INS_USADA8, //<! usada8
        ID_INS_USAT, //<! usat
        ID_INS_USAT16, //<! usat16
        ID_INS_USAX, //<! usax
        ID_INS_USUB16, //<! usub16
        ID_INS_USUB8, //<! usub8
        ID_INS_UXTAB, //<! uxtab
        ID_INS_UXTAB16, //<! uxtab16
        ID_INS_UXTAH, //<! uxtah
        ID_INS_UXTB, //<! uxtb
        ID_INS_UXTB16, //<! uxtb16
        ID_INS_UXTH, //<! uxth
        ID_INS_VABAL, //<! vabal
        ID_INS_VABA, //<! vaba
        ID_INS_VABDL, //<! vabdl
        ID_INS_VABD, //<! vabd
        ID_INS_VABS, //<! vabs
        ID_INS_VACGE, //<! vacge
        ID_INS_VACGT, //<! vacgt
        ID_INS_VADD, //<! vadd
        ID_INS_VADDHN, //<! vaddhn
        ID_INS_VADDL, //<! vaddl
        ID_INS_VADDW, //<! vaddw
        ID_INS_VAND, //<! vand
        ID_INS_VBIC, //<! vbic
        ID_INS_VBIF, //<! vbif
        ID_INS_VBIT, //<! vbit
        ID_INS_VBSL, //<! vbsl
        ID_INS_VCEQ, //<! vceq
        ID_INS_VCGE, //<! vcge
        ID_INS_VCGT, //<! vcgt
        ID_INS_VCLE, //<! vcle
        ID_INS_VCLS, //<! vcls
        ID_INS_VCLT, //<! vclt
        ID_INS_VCLZ, //<! vclz
        ID_INS_VCMP, //<! vcmp
        ID_INS_VCMPE, //<! vcmpe
        ID_INS_VCNT, //<! vcnt
        ID_INS_VCVTA, //<! vcvta
        ID_INS_VCVTB, //<! vcvtb
        ID_INS_VCVT, //<! vcvt
        ID_INS_VCVTM, //<! vcvtm
        ID_INS_VCVTN, //<! vcvtn
        ID_INS_VCVTP, //<! vcvtp
        ID_INS_VCVTT, //<! vcvtt
        ID_INS_VDIV, //<! vdiv
        ID_INS_VDUP, //<! vdup
        ID_INS_VEOR, //<! veor
        ID_INS_VEXT, //<! vext
        ID_INS_VFMA, //<! vfma
        ID_INS_VFMS, //<! vfms
        ID_INS_VFNMA, //<! vfnma
        ID_INS_VFNMS, //<! vfnms
        ID_INS_VHADD, //<! vhadd
        ID_INS_VHSUB, //<! vhsub
        ID_INS_VLD1, //<! vld1
        ID_INS_VLD2, //<! vld2
        ID_INS_VLD3, //<! vld3
        ID_INS_VLD4, //<! vld4
        ID_INS_VLDMDB, //<! vldmdb
        ID_INS_VLDMIA, //<! vldmia
        ID_INS_VLDR, //<! vldr
        ID_INS_VMAXNM, //<! vmaxnm
        ID_INS_VMAX, //<! vmax
        ID_INS_VMINNM, //<! vminnm
        ID_INS_VMIN, //<! vmin
        ID_INS_VMLA, //<! vmla
        ID_INS_VMLAL, //<! vmlal
        ID_INS_VMLS, //<! vmls
        ID_INS_VMLSL, //<! vmlsl
        ID_INS_VMOVL, //<! vmovl
        ID_INS_VMOVN, //<! vmovn
        ID_INS_VMSR, //<! vmsr
        ID_INS_VMUL, //<! vmul
        ID_INS_VMULL, //<! vmull
        ID_INS_VMVN, //<! vmvn
        ID_INS_VNEG, //<! vneg
        ID_INS_VNMLA, //<! vnmla
        ID_INS_VNMLS, //<! vnmls
        ID_INS_VNMUL, //<! vnmul
        ID_INS_VORN, //<! vorn
        ID_INS_VORR, //<! vorr
        ID_INS_VPADAL, //<! vpadal
        ID_INS_VPADDL, //<! vpaddl
        ID_INS_VPADD, //<! vpadd
        ID_INS_VPMAX, //<! vpmax
        ID_INS_VPMIN, //<! vpmin
        ID_INS_VQABS, //<! vqabs
        ID_INS_VQADD, //<! vqadd
        ID_INS_VQDMLAL, //<! vqdmlal
        ID_INS_VQDMLSL, //<! vqdmlsl
        ID_INS_VQDMULH, //<! vqdmulh
        ID_INS_VQDMULL, //<! vqdmull
        ID_INS_VQMOVUN, //<! vqmovun
        ID_INS_VQMOVN, //<! vqmovn
        ID_INS_VQNEG, //<! vqneg
        ID_INS_VQRDMULH, //<! vqrdmulh
        ID_INS_VQRSHL, //<! vqrshl
        ID_INS_VQRSHRN, //<! vqrshrn
        ID_INS_VQRSHRUN, //<! vqrshrun
        ID_INS_VQSHL, //<! vqshl
        ID_INS_VQSHLU, //<! vqshlu
        ID_INS_VQSHRN, //<! vqshrn
        ID_INS_VQSHRUN, //<! vqshrun
        ID_INS_VQSUB, //<! vqsub
        ID_INS_VRADDHN, //<! vraddhn
        ID_INS_VRECPE, //<! vrecpe
        ID_INS_VRECPS, //<! vrecps
        ID_INS_VREV16, //<! vrev16
        ID_INS_VREV32, //<! vrev32
        ID_INS_VREV64, //<! vrev64
        ID_INS_VRHADD, //<! vrhadd
        ID_INS_VRINTA, //<! vrinta
        ID_INS_VRINTM, //<! vrintm
        ID_INS_VRINTN, //<! vrintn
        ID_INS_VRINTP, //<! vrintp
        ID_INS_VRINTR, //<! vrintr
        ID_INS_VRINTX, //<! vrintx
        ID_INS_VRINTZ, //<! vrintz
        ID_INS_VRSHL, //<! vrshl
        ID_INS_VRSHRN, //<! vrshrn
        ID_INS_VRSHR, //<! vrshr
        ID_INS_VRSQRTE, //<! vrsqrte
        ID_INS_VRSQRTS, //<! vrsqrts
        ID_INS_VRSRA, //<! vrsra
        ID_INS_VRSUBHN, //<! vrsubhn
        ID_INS_VSELEQ, //<! vseleq
        ID_INS_VSELGE, //<! vselge
        ID_INS_VSELGT, //<! vselgt
        ID_INS_VSELVS, //<! vselvs
        ID_INS_VSHLL, //<! vshll
        ID_INS_VSHL, //<! vshl
        ID_INS_VSHRN, //<! vshrn
        ID_INS_VSHR, //<! vshr
        ID_INS_VSLI, //<! vsli
        ID_INS_VSQRT, //<! vsqrt
        ID_INS_VSRA, //<! vsra
        ID_INS_VSRI, //<! vsri
        ID_INS_VST1, //<! vst1
        ID_INS_VST2, //<! vst2
        ID_INS_VST3, //<! vst3
        ID_INS_VST4, //<! vst4
        ID_INS_VSTMDB, //<! vstmdb
        ID_INS_VSTMIA, //<! vstmia
        ID_INS_VSTR, //<! vstr
        ID_INS_VSUB, //<! vsub
        ID_INS_VSUBHN, //<! vsubhn
        ID_INS_VSUBL, //<! vsubl
        ID_INS_VSUBW, //<! vsubw
        ID_INS_VSWP, //<! vswp
        ID_INS_VTBL, //<! vtbl
        ID_INS_VTBX, //<! vtbx
        ID_INS_VCVTR, //<! vcvtr
        ID_INS_VTRN, //<! vtrn
        ID_INS_VTST, //<! vtst
        ID_INS_VUZP, //<! vuzp
        ID_INS_VZIP, //<! vzip
        ID_INS_ADDW, //<! addw
        ID_INS_ASR, //<! asr
        ID_INS_DCPS1, //<! dcps1
        ID_INS_DCPS2, //<! dcps2
        ID_INS_DCPS3, //<! dcps3
        ID_INS_IT, //<! it
        ID_INS_LSL, //<! lsl
        ID_INS_LSR, //<! lsr
        ID_INS_ORN, //<! orn
        ID_INS_ROR, //<! ror
        ID_INS_RRX, //<! rrx
        ID_INS_SUBW, //<! subw
        ID_INS_TBB, //<! tbb
        ID_INS_TBH, //<! tbh
        ID_INS_CBNZ, //<! cbnz
        ID_INS_CBZ, //<! cbz
        ID_INS_POP, //<! pop
        ID_INS_PUSH, //<! push

        // special instructions
        ID_INS_NOP, //<! nop
        ID_INS_YIELD, //<! yield
        ID_INS_WFE, //<! wfe
        ID_INS_WFI, //<! wfi
        ID_INS_SEV, //<! sev
        ID_INS_SEVL, //<! sevl
        ID_INS_VPUSH, //<! vpush
        ID_INS_VPOP, //<! vpop

        /* Must be the last item */
        ID_INS_LAST_ITEM //!< must be the last item
      };

    /*! @} End of arm32 namespace */
    };
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ARM32SPECIFICATIONS_H */
