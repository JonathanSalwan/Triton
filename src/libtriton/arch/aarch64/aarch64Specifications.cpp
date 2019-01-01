//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/aarch64Specifications.hpp>
#include <triton/architecture.hpp>
#include <triton/cpuSize.hpp>
#include <triton/exceptions.hpp>
#include <triton/externalLibs.hpp>



namespace triton {
  namespace arch {
    namespace aarch64 {

      AArch64Specifications::AArch64Specifications(triton::arch::architecture_e arch) {
        if (arch != triton::arch::ARCH_AARCH64)
            throw triton::exceptions::Architecture("AArch64Specifications::AArch64Specifications(): Invalid architecture.");

          // Fill registers_ with those available in AArch64 from spec
          #define REG_SPEC(UPPER_NAME, LOWER_NAME, AARCH64_UPPER, AARCH64_LOWER, AARCH64_PARENT, MUTABLE) \
            registers_.emplace(ID_REG_AARCH64_##UPPER_NAME,                                               \
                               triton::arch::Register(triton::arch::ID_REG_AARCH64_##UPPER_NAME,          \
                                                      #LOWER_NAME,                                        \
                                                      triton::arch::ID_REG_AARCH64_##AARCH64_PARENT,      \
                                                      AARCH64_UPPER,                                      \
                                                      AARCH64_LOWER,                                      \
                                                      MUTABLE)                                            \
                              );
          // Handle register not available in capstone as normal registers
          #define REG_SPEC_NO_CAPSTONE REG_SPEC
          #include "triton/aarch64.spec"
      }


      triton::arch::register_e AArch64Specifications::capstoneRegisterToTritonRegister(triton::uint32 id) const {
        triton::arch::register_e tritonId = triton::arch::ID_REG_INVALID;

        switch (id) {
          // Convert registers from capstone value to triton value
          #define REG_SPEC(UPPER_NAME, _1, _2, _3, _4, _5)        \
          case triton::extlibs::capstone::ARM64_REG_##UPPER_NAME: \
            tritonId = triton::arch::ID_REG_AARCH64_##UPPER_NAME; \
            break;
          // Ignore registers not available in capstone
          #define REG_SPEC_NO_CAPSTONE(_1, _2, _3, _4, _5, _6)
          #include "triton/aarch64.spec"

          default:
            tritonId = triton::arch::ID_REG_INVALID;
            break;
        }

        return tritonId;
      }


      triton::arch::aarch64::shift_e AArch64Specifications::capstoneShiftToTritonShift(triton::uint32 id) const {
        triton::arch::aarch64::shift_e tritonId = triton::arch::aarch64::ID_SHIFT_INVALID;

        switch (id) {
          case triton::extlibs::capstone::ARM64_SFT_INVALID:
            tritonId = triton::arch::aarch64::ID_SHIFT_INVALID;
            break;

          case triton::extlibs::capstone::ARM64_SFT_ASR:
            tritonId = triton::arch::aarch64::ID_SHIFT_ASR;
            break;

          case triton::extlibs::capstone::ARM64_SFT_LSL:
            tritonId = triton::arch::aarch64::ID_SHIFT_LSL;
            break;

          case triton::extlibs::capstone::ARM64_SFT_LSR:
            tritonId = triton::arch::aarch64::ID_SHIFT_LSR;
            break;

          case triton::extlibs::capstone::ARM64_SFT_ROR:
            tritonId = triton::arch::aarch64::ID_SHIFT_ROR;
            break;

          default:
            tritonId = triton::arch::aarch64::ID_SHIFT_INVALID;
            break;
        }

        return tritonId;
      }


      triton::arch::aarch64::extend_e AArch64Specifications::capstoneExtendToTritonExtend(triton::uint32 id) const {
        triton::arch::aarch64::extend_e tritonId = triton::arch::aarch64::ID_EXTEND_INVALID;

        switch (id) {
          case triton::extlibs::capstone::ARM64_EXT_INVALID:
            tritonId = triton::arch::aarch64::ID_EXTEND_INVALID;
            break;

          case triton::extlibs::capstone::ARM64_EXT_UXTB:
            tritonId = triton::arch::aarch64::ID_EXTEND_UXTB;
            break;

          case triton::extlibs::capstone::ARM64_EXT_UXTH:
            tritonId = triton::arch::aarch64::ID_EXTEND_UXTH;
            break;

          case triton::extlibs::capstone::ARM64_EXT_UXTW:
            tritonId = triton::arch::aarch64::ID_EXTEND_UXTW;
            break;

          case triton::extlibs::capstone::ARM64_EXT_UXTX:
            tritonId = triton::arch::aarch64::ID_EXTEND_UXTX;
            break;

          case triton::extlibs::capstone::ARM64_EXT_SXTB:
            tritonId = triton::arch::aarch64::ID_EXTEND_SXTB;
            break;

          case triton::extlibs::capstone::ARM64_EXT_SXTH:
            tritonId = triton::arch::aarch64::ID_EXTEND_SXTH;
            break;

          case triton::extlibs::capstone::ARM64_EXT_SXTW:
            tritonId = triton::arch::aarch64::ID_EXTEND_SXTW;
            break;

          case triton::extlibs::capstone::ARM64_EXT_SXTX:
            tritonId = triton::arch::aarch64::ID_EXTEND_SXTX;
            break;

          default:
            tritonId = triton::arch::aarch64::ID_EXTEND_INVALID;
            break;
        }

        return tritonId;
      }


      triton::arch::aarch64::condition_e AArch64Specifications::capstoneConditionToTritonCondition(triton::uint32 id) const {
        triton::arch::aarch64::condition_e tritonId = triton::arch::aarch64::ID_CONDITION_INVALID;

        switch (id) {
          case triton::extlibs::capstone::ARM64_CC_INVALID:
            tritonId = triton::arch::aarch64::ID_CONDITION_INVALID;
            break;

          case triton::extlibs::capstone::ARM64_CC_AL:
            tritonId = triton::arch::aarch64::ID_CONDITION_AL;
            break;

          case triton::extlibs::capstone::ARM64_CC_EQ:
            tritonId = triton::arch::aarch64::ID_CONDITION_EQ;
            break;

          case triton::extlibs::capstone::ARM64_CC_GE:
            tritonId = triton::arch::aarch64::ID_CONDITION_GE;
            break;

          case triton::extlibs::capstone::ARM64_CC_GT:
            tritonId = triton::arch::aarch64::ID_CONDITION_GT;
            break;

          case triton::extlibs::capstone::ARM64_CC_HI:
            tritonId = triton::arch::aarch64::ID_CONDITION_HI;
            break;

          case triton::extlibs::capstone::ARM64_CC_HS:
            tritonId = triton::arch::aarch64::ID_CONDITION_HS;
            break;

          case triton::extlibs::capstone::ARM64_CC_LE:
            tritonId = triton::arch::aarch64::ID_CONDITION_LE;
            break;

          case triton::extlibs::capstone::ARM64_CC_LO:
            tritonId = triton::arch::aarch64::ID_CONDITION_LO;
            break;

          case triton::extlibs::capstone::ARM64_CC_LS:
            tritonId = triton::arch::aarch64::ID_CONDITION_LS;
            break;

          case triton::extlibs::capstone::ARM64_CC_LT:
            tritonId = triton::arch::aarch64::ID_CONDITION_LT;
            break;

          case triton::extlibs::capstone::ARM64_CC_MI:
            tritonId = triton::arch::aarch64::ID_CONDITION_MI;
            break;

          case triton::extlibs::capstone::ARM64_CC_NE:
            tritonId = triton::arch::aarch64::ID_CONDITION_NE;
            break;

          case triton::extlibs::capstone::ARM64_CC_PL:
            tritonId = triton::arch::aarch64::ID_CONDITION_PL;
            break;

          case triton::extlibs::capstone::ARM64_CC_VC:
            tritonId = triton::arch::aarch64::ID_CONDITION_VC;
            break;

          case triton::extlibs::capstone::ARM64_CC_VS:
            tritonId = triton::arch::aarch64::ID_CONDITION_VS;
            break;

          default:
            tritonId = triton::arch::aarch64::ID_CONDITION_INVALID;
            break;
        }

        return tritonId;
      }


      triton::uint32 AArch64Specifications::capstoneInstructionToTritonInstruction(triton::uint32 id) const {
        triton::uint32 tritonId = triton::arch::aarch64::ID_INS_INVALID;

        switch (id) {
          case triton::extlibs::capstone::ARM64_INS_INVALID:
            tritonId = triton::arch::aarch64::ID_INS_INVALID;
            break;

          case triton::extlibs::capstone::ARM64_INS_ABS:
            tritonId = triton::arch::aarch64::ID_INS_ABS;
            break;

          case triton::extlibs::capstone::ARM64_INS_ADC:
            tritonId = triton::arch::aarch64::ID_INS_ADC;
            break;

          case triton::extlibs::capstone::ARM64_INS_ADDHN:
            tritonId = triton::arch::aarch64::ID_INS_ADDHN;
            break;

          case triton::extlibs::capstone::ARM64_INS_ADDHN2:
            tritonId = triton::arch::aarch64::ID_INS_ADDHN2;
            break;

          case triton::extlibs::capstone::ARM64_INS_ADDP:
            tritonId = triton::arch::aarch64::ID_INS_ADDP;
            break;

          case triton::extlibs::capstone::ARM64_INS_ADD:
            tritonId = triton::arch::aarch64::ID_INS_ADD;
            break;

          case triton::extlibs::capstone::ARM64_INS_ADDV:
            tritonId = triton::arch::aarch64::ID_INS_ADDV;
            break;

          case triton::extlibs::capstone::ARM64_INS_ADR:
            tritonId = triton::arch::aarch64::ID_INS_ADR;
            break;

          case triton::extlibs::capstone::ARM64_INS_ADRP:
            tritonId = triton::arch::aarch64::ID_INS_ADRP;
            break;

          case triton::extlibs::capstone::ARM64_INS_AESD:
            tritonId = triton::arch::aarch64::ID_INS_AESD;
            break;

          case triton::extlibs::capstone::ARM64_INS_AESE:
            tritonId = triton::arch::aarch64::ID_INS_AESE;
            break;

          case triton::extlibs::capstone::ARM64_INS_AESIMC:
            tritonId = triton::arch::aarch64::ID_INS_AESIMC;
            break;

          case triton::extlibs::capstone::ARM64_INS_AESMC:
            tritonId = triton::arch::aarch64::ID_INS_AESMC;
            break;

          case triton::extlibs::capstone::ARM64_INS_AND:
            tritonId = triton::arch::aarch64::ID_INS_AND;
            break;

          case triton::extlibs::capstone::ARM64_INS_ASR:
            tritonId = triton::arch::aarch64::ID_INS_ASR;
            break;

          case triton::extlibs::capstone::ARM64_INS_B:
            tritonId = triton::arch::aarch64::ID_INS_B;
            break;

          case triton::extlibs::capstone::ARM64_INS_BFM:
            tritonId = triton::arch::aarch64::ID_INS_BFM;
            break;

          case triton::extlibs::capstone::ARM64_INS_BIC:
            tritonId = triton::arch::aarch64::ID_INS_BIC;
            break;

          case triton::extlibs::capstone::ARM64_INS_BIF:
            tritonId = triton::arch::aarch64::ID_INS_BIF;
            break;

          case triton::extlibs::capstone::ARM64_INS_BIT:
            tritonId = triton::arch::aarch64::ID_INS_BIT;
            break;

          case triton::extlibs::capstone::ARM64_INS_BL:
            tritonId = triton::arch::aarch64::ID_INS_BL;
            break;

          case triton::extlibs::capstone::ARM64_INS_BLR:
            tritonId = triton::arch::aarch64::ID_INS_BLR;
            break;

          case triton::extlibs::capstone::ARM64_INS_BR:
            tritonId = triton::arch::aarch64::ID_INS_BR;
            break;

          case triton::extlibs::capstone::ARM64_INS_BRK:
            tritonId = triton::arch::aarch64::ID_INS_BRK;
            break;

          case triton::extlibs::capstone::ARM64_INS_BSL:
            tritonId = triton::arch::aarch64::ID_INS_BSL;
            break;

          case triton::extlibs::capstone::ARM64_INS_CBNZ:
            tritonId = triton::arch::aarch64::ID_INS_CBNZ;
            break;

          case triton::extlibs::capstone::ARM64_INS_CBZ:
            tritonId = triton::arch::aarch64::ID_INS_CBZ;
            break;

          case triton::extlibs::capstone::ARM64_INS_CCMN:
            tritonId = triton::arch::aarch64::ID_INS_CCMN;
            break;

          case triton::extlibs::capstone::ARM64_INS_CCMP:
            tritonId = triton::arch::aarch64::ID_INS_CCMP;
            break;

          case triton::extlibs::capstone::ARM64_INS_CLREX:
            tritonId = triton::arch::aarch64::ID_INS_CLREX;
            break;

          case triton::extlibs::capstone::ARM64_INS_CLS:
            tritonId = triton::arch::aarch64::ID_INS_CLS;
            break;

          case triton::extlibs::capstone::ARM64_INS_CLZ:
            tritonId = triton::arch::aarch64::ID_INS_CLZ;
            break;

          case triton::extlibs::capstone::ARM64_INS_CMEQ:
            tritonId = triton::arch::aarch64::ID_INS_CMEQ;
            break;

          case triton::extlibs::capstone::ARM64_INS_CMGE:
            tritonId = triton::arch::aarch64::ID_INS_CMGE;
            break;

          case triton::extlibs::capstone::ARM64_INS_CMGT:
            tritonId = triton::arch::aarch64::ID_INS_CMGT;
            break;

          case triton::extlibs::capstone::ARM64_INS_CMHI:
            tritonId = triton::arch::aarch64::ID_INS_CMHI;
            break;

          case triton::extlibs::capstone::ARM64_INS_CMHS:
            tritonId = triton::arch::aarch64::ID_INS_CMHS;
            break;

          case triton::extlibs::capstone::ARM64_INS_CMLE:
            tritonId = triton::arch::aarch64::ID_INS_CMLE;
            break;

          case triton::extlibs::capstone::ARM64_INS_CMLT:
            tritonId = triton::arch::aarch64::ID_INS_CMLT;
            break;

          case triton::extlibs::capstone::ARM64_INS_CMTST:
            tritonId = triton::arch::aarch64::ID_INS_CMTST;
            break;

          case triton::extlibs::capstone::ARM64_INS_CNT:
            tritonId = triton::arch::aarch64::ID_INS_CNT;
            break;

          case triton::extlibs::capstone::ARM64_INS_MOV:
            tritonId = triton::arch::aarch64::ID_INS_MOV;
            break;

          case triton::extlibs::capstone::ARM64_INS_CRC32B:
            tritonId = triton::arch::aarch64::ID_INS_CRC32B;
            break;

          case triton::extlibs::capstone::ARM64_INS_CRC32CB:
            tritonId = triton::arch::aarch64::ID_INS_CRC32CB;
            break;

          case triton::extlibs::capstone::ARM64_INS_CRC32CH:
            tritonId = triton::arch::aarch64::ID_INS_CRC32CH;
            break;

          case triton::extlibs::capstone::ARM64_INS_CRC32CW:
            tritonId = triton::arch::aarch64::ID_INS_CRC32CW;
            break;

          case triton::extlibs::capstone::ARM64_INS_CRC32CX:
            tritonId = triton::arch::aarch64::ID_INS_CRC32CX;
            break;

          case triton::extlibs::capstone::ARM64_INS_CRC32H:
            tritonId = triton::arch::aarch64::ID_INS_CRC32H;
            break;

          case triton::extlibs::capstone::ARM64_INS_CRC32W:
            tritonId = triton::arch::aarch64::ID_INS_CRC32W;
            break;

          case triton::extlibs::capstone::ARM64_INS_CRC32X:
            tritonId = triton::arch::aarch64::ID_INS_CRC32X;
            break;

          case triton::extlibs::capstone::ARM64_INS_CSEL:
            tritonId = triton::arch::aarch64::ID_INS_CSEL;
            break;

          case triton::extlibs::capstone::ARM64_INS_CSINC:
            tritonId = triton::arch::aarch64::ID_INS_CSINC;
            break;

          case triton::extlibs::capstone::ARM64_INS_CSINV:
            tritonId = triton::arch::aarch64::ID_INS_CSINV;
            break;

          case triton::extlibs::capstone::ARM64_INS_CSNEG:
            tritonId = triton::arch::aarch64::ID_INS_CSNEG;
            break;

          case triton::extlibs::capstone::ARM64_INS_DCPS1:
            tritonId = triton::arch::aarch64::ID_INS_DCPS1;
            break;

          case triton::extlibs::capstone::ARM64_INS_DCPS2:
            tritonId = triton::arch::aarch64::ID_INS_DCPS2;
            break;

          case triton::extlibs::capstone::ARM64_INS_DCPS3:
            tritonId = triton::arch::aarch64::ID_INS_DCPS3;
            break;

          case triton::extlibs::capstone::ARM64_INS_DMB:
            tritonId = triton::arch::aarch64::ID_INS_DMB;
            break;

          case triton::extlibs::capstone::ARM64_INS_DRPS:
            tritonId = triton::arch::aarch64::ID_INS_DRPS;
            break;

          case triton::extlibs::capstone::ARM64_INS_DSB:
            tritonId = triton::arch::aarch64::ID_INS_DSB;
            break;

          case triton::extlibs::capstone::ARM64_INS_DUP:
            tritonId = triton::arch::aarch64::ID_INS_DUP;
            break;

          case triton::extlibs::capstone::ARM64_INS_EON:
            tritonId = triton::arch::aarch64::ID_INS_EON;
            break;

          case triton::extlibs::capstone::ARM64_INS_EOR:
            tritonId = triton::arch::aarch64::ID_INS_EOR;
            break;

          case triton::extlibs::capstone::ARM64_INS_ERET:
            tritonId = triton::arch::aarch64::ID_INS_ERET;
            break;

          case triton::extlibs::capstone::ARM64_INS_EXTR:
            tritonId = triton::arch::aarch64::ID_INS_EXTR;
            break;

          case triton::extlibs::capstone::ARM64_INS_EXT:
            tritonId = triton::arch::aarch64::ID_INS_EXT;
            break;

          case triton::extlibs::capstone::ARM64_INS_FABD:
            tritonId = triton::arch::aarch64::ID_INS_FABD;
            break;

          case triton::extlibs::capstone::ARM64_INS_FABS:
            tritonId = triton::arch::aarch64::ID_INS_FABS;
            break;

          case triton::extlibs::capstone::ARM64_INS_FACGE:
            tritonId = triton::arch::aarch64::ID_INS_FACGE;
            break;

          case triton::extlibs::capstone::ARM64_INS_FACGT:
            tritonId = triton::arch::aarch64::ID_INS_FACGT;
            break;

          case triton::extlibs::capstone::ARM64_INS_FADD:
            tritonId = triton::arch::aarch64::ID_INS_FADD;
            break;

          case triton::extlibs::capstone::ARM64_INS_FADDP:
            tritonId = triton::arch::aarch64::ID_INS_FADDP;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCCMP:
            tritonId = triton::arch::aarch64::ID_INS_FCCMP;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCCMPE:
            tritonId = triton::arch::aarch64::ID_INS_FCCMPE;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCMEQ:
            tritonId = triton::arch::aarch64::ID_INS_FCMEQ;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCMGE:
            tritonId = triton::arch::aarch64::ID_INS_FCMGE;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCMGT:
            tritonId = triton::arch::aarch64::ID_INS_FCMGT;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCMLE:
            tritonId = triton::arch::aarch64::ID_INS_FCMLE;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCMLT:
            tritonId = triton::arch::aarch64::ID_INS_FCMLT;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCMP:
            tritonId = triton::arch::aarch64::ID_INS_FCMP;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCMPE:
            tritonId = triton::arch::aarch64::ID_INS_FCMPE;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCSEL:
            tritonId = triton::arch::aarch64::ID_INS_FCSEL;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCVTAS:
            tritonId = triton::arch::aarch64::ID_INS_FCVTAS;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCVTAU:
            tritonId = triton::arch::aarch64::ID_INS_FCVTAU;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCVT:
            tritonId = triton::arch::aarch64::ID_INS_FCVT;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCVTL:
            tritonId = triton::arch::aarch64::ID_INS_FCVTL;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCVTL2:
            tritonId = triton::arch::aarch64::ID_INS_FCVTL2;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCVTMS:
            tritonId = triton::arch::aarch64::ID_INS_FCVTMS;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCVTMU:
            tritonId = triton::arch::aarch64::ID_INS_FCVTMU;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCVTNS:
            tritonId = triton::arch::aarch64::ID_INS_FCVTNS;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCVTNU:
            tritonId = triton::arch::aarch64::ID_INS_FCVTNU;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCVTN:
            tritonId = triton::arch::aarch64::ID_INS_FCVTN;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCVTN2:
            tritonId = triton::arch::aarch64::ID_INS_FCVTN2;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCVTPS:
            tritonId = triton::arch::aarch64::ID_INS_FCVTPS;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCVTPU:
            tritonId = triton::arch::aarch64::ID_INS_FCVTPU;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCVTXN:
            tritonId = triton::arch::aarch64::ID_INS_FCVTXN;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCVTXN2:
            tritonId = triton::arch::aarch64::ID_INS_FCVTXN2;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCVTZS:
            tritonId = triton::arch::aarch64::ID_INS_FCVTZS;
            break;

          case triton::extlibs::capstone::ARM64_INS_FCVTZU:
            tritonId = triton::arch::aarch64::ID_INS_FCVTZU;
            break;

          case triton::extlibs::capstone::ARM64_INS_FDIV:
            tritonId = triton::arch::aarch64::ID_INS_FDIV;
            break;

          case triton::extlibs::capstone::ARM64_INS_FMADD:
            tritonId = triton::arch::aarch64::ID_INS_FMADD;
            break;

          case triton::extlibs::capstone::ARM64_INS_FMAX:
            tritonId = triton::arch::aarch64::ID_INS_FMAX;
            break;

          case triton::extlibs::capstone::ARM64_INS_FMAXNM:
            tritonId = triton::arch::aarch64::ID_INS_FMAXNM;
            break;

          case triton::extlibs::capstone::ARM64_INS_FMAXNMP:
            tritonId = triton::arch::aarch64::ID_INS_FMAXNMP;
            break;

          case triton::extlibs::capstone::ARM64_INS_FMAXNMV:
            tritonId = triton::arch::aarch64::ID_INS_FMAXNMV;
            break;

          case triton::extlibs::capstone::ARM64_INS_FMAXP:
            tritonId = triton::arch::aarch64::ID_INS_FMAXP;
            break;

          case triton::extlibs::capstone::ARM64_INS_FMAXV:
            tritonId = triton::arch::aarch64::ID_INS_FMAXV;
            break;

          case triton::extlibs::capstone::ARM64_INS_FMIN:
            tritonId = triton::arch::aarch64::ID_INS_FMIN;
            break;

          case triton::extlibs::capstone::ARM64_INS_FMINNM:
            tritonId = triton::arch::aarch64::ID_INS_FMINNM;
            break;

          case triton::extlibs::capstone::ARM64_INS_FMINNMP:
            tritonId = triton::arch::aarch64::ID_INS_FMINNMP;
            break;

          case triton::extlibs::capstone::ARM64_INS_FMINNMV:
            tritonId = triton::arch::aarch64::ID_INS_FMINNMV;
            break;

          case triton::extlibs::capstone::ARM64_INS_FMINP:
            tritonId = triton::arch::aarch64::ID_INS_FMINP;
            break;

          case triton::extlibs::capstone::ARM64_INS_FMINV:
            tritonId = triton::arch::aarch64::ID_INS_FMINV;
            break;

          case triton::extlibs::capstone::ARM64_INS_FMLA:
            tritonId = triton::arch::aarch64::ID_INS_FMLA;
            break;

          case triton::extlibs::capstone::ARM64_INS_FMLS:
            tritonId = triton::arch::aarch64::ID_INS_FMLS;
            break;

          case triton::extlibs::capstone::ARM64_INS_FMOV:
            tritonId = triton::arch::aarch64::ID_INS_FMOV;
            break;

          case triton::extlibs::capstone::ARM64_INS_FMSUB:
            tritonId = triton::arch::aarch64::ID_INS_FMSUB;
            break;

          case triton::extlibs::capstone::ARM64_INS_FMUL:
            tritonId = triton::arch::aarch64::ID_INS_FMUL;
            break;

          case triton::extlibs::capstone::ARM64_INS_FMULX:
            tritonId = triton::arch::aarch64::ID_INS_FMULX;
            break;

          case triton::extlibs::capstone::ARM64_INS_FNEG:
            tritonId = triton::arch::aarch64::ID_INS_FNEG;
            break;

          case triton::extlibs::capstone::ARM64_INS_FNMADD:
            tritonId = triton::arch::aarch64::ID_INS_FNMADD;
            break;

          case triton::extlibs::capstone::ARM64_INS_FNMSUB:
            tritonId = triton::arch::aarch64::ID_INS_FNMSUB;
            break;

          case triton::extlibs::capstone::ARM64_INS_FNMUL:
            tritonId = triton::arch::aarch64::ID_INS_FNMUL;
            break;

          case triton::extlibs::capstone::ARM64_INS_FRECPE:
            tritonId = triton::arch::aarch64::ID_INS_FRECPE;
            break;

          case triton::extlibs::capstone::ARM64_INS_FRECPS:
            tritonId = triton::arch::aarch64::ID_INS_FRECPS;
            break;

          case triton::extlibs::capstone::ARM64_INS_FRECPX:
            tritonId = triton::arch::aarch64::ID_INS_FRECPX;
            break;

          case triton::extlibs::capstone::ARM64_INS_FRINTA:
            tritonId = triton::arch::aarch64::ID_INS_FRINTA;
            break;

          case triton::extlibs::capstone::ARM64_INS_FRINTI:
            tritonId = triton::arch::aarch64::ID_INS_FRINTI;
            break;

          case triton::extlibs::capstone::ARM64_INS_FRINTM:
            tritonId = triton::arch::aarch64::ID_INS_FRINTM;
            break;

          case triton::extlibs::capstone::ARM64_INS_FRINTN:
            tritonId = triton::arch::aarch64::ID_INS_FRINTN;
            break;

          case triton::extlibs::capstone::ARM64_INS_FRINTP:
            tritonId = triton::arch::aarch64::ID_INS_FRINTP;
            break;

          case triton::extlibs::capstone::ARM64_INS_FRINTX:
            tritonId = triton::arch::aarch64::ID_INS_FRINTX;
            break;

          case triton::extlibs::capstone::ARM64_INS_FRINTZ:
            tritonId = triton::arch::aarch64::ID_INS_FRINTZ;
            break;

          case triton::extlibs::capstone::ARM64_INS_FRSQRTE:
            tritonId = triton::arch::aarch64::ID_INS_FRSQRTE;
            break;

          case triton::extlibs::capstone::ARM64_INS_FRSQRTS:
            tritonId = triton::arch::aarch64::ID_INS_FRSQRTS;
            break;

          case triton::extlibs::capstone::ARM64_INS_FSQRT:
            tritonId = triton::arch::aarch64::ID_INS_FSQRT;
            break;

          case triton::extlibs::capstone::ARM64_INS_FSUB:
            tritonId = triton::arch::aarch64::ID_INS_FSUB;
            break;

          case triton::extlibs::capstone::ARM64_INS_HINT:
            tritonId = triton::arch::aarch64::ID_INS_HINT;
            break;

          case triton::extlibs::capstone::ARM64_INS_HLT:
            tritonId = triton::arch::aarch64::ID_INS_HLT;
            break;

          case triton::extlibs::capstone::ARM64_INS_HVC:
            tritonId = triton::arch::aarch64::ID_INS_HVC;
            break;

          case triton::extlibs::capstone::ARM64_INS_INS:
            tritonId = triton::arch::aarch64::ID_INS_INS;
            break;

          case triton::extlibs::capstone::ARM64_INS_ISB:
            tritonId = triton::arch::aarch64::ID_INS_ISB;
            break;

          case triton::extlibs::capstone::ARM64_INS_LD1:
            tritonId = triton::arch::aarch64::ID_INS_LD1;
            break;

          case triton::extlibs::capstone::ARM64_INS_LD1R:
            tritonId = triton::arch::aarch64::ID_INS_LD1R;
            break;

          case triton::extlibs::capstone::ARM64_INS_LD2R:
            tritonId = triton::arch::aarch64::ID_INS_LD2R;
            break;

          case triton::extlibs::capstone::ARM64_INS_LD2:
            tritonId = triton::arch::aarch64::ID_INS_LD2;
            break;

          case triton::extlibs::capstone::ARM64_INS_LD3R:
            tritonId = triton::arch::aarch64::ID_INS_LD3R;
            break;

          case triton::extlibs::capstone::ARM64_INS_LD3:
            tritonId = triton::arch::aarch64::ID_INS_LD3;
            break;

          case triton::extlibs::capstone::ARM64_INS_LD4:
            tritonId = triton::arch::aarch64::ID_INS_LD4;
            break;

          case triton::extlibs::capstone::ARM64_INS_LD4R:
            tritonId = triton::arch::aarch64::ID_INS_LD4R;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDARB:
            tritonId = triton::arch::aarch64::ID_INS_LDARB;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDARH:
            tritonId = triton::arch::aarch64::ID_INS_LDARH;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDAR:
            tritonId = triton::arch::aarch64::ID_INS_LDAR;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDAXP:
            tritonId = triton::arch::aarch64::ID_INS_LDAXP;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDAXRB:
            tritonId = triton::arch::aarch64::ID_INS_LDAXRB;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDAXRH:
            tritonId = triton::arch::aarch64::ID_INS_LDAXRH;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDAXR:
            tritonId = triton::arch::aarch64::ID_INS_LDAXR;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDNP:
            tritonId = triton::arch::aarch64::ID_INS_LDNP;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDP:
            tritonId = triton::arch::aarch64::ID_INS_LDP;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDPSW:
            tritonId = triton::arch::aarch64::ID_INS_LDPSW;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDRB:
            tritonId = triton::arch::aarch64::ID_INS_LDRB;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDR:
            tritonId = triton::arch::aarch64::ID_INS_LDR;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDRH:
            tritonId = triton::arch::aarch64::ID_INS_LDRH;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDRSB:
            tritonId = triton::arch::aarch64::ID_INS_LDRSB;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDRSH:
            tritonId = triton::arch::aarch64::ID_INS_LDRSH;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDRSW:
            tritonId = triton::arch::aarch64::ID_INS_LDRSW;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDTRB:
            tritonId = triton::arch::aarch64::ID_INS_LDTRB;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDTRH:
            tritonId = triton::arch::aarch64::ID_INS_LDTRH;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDTRSB:
            tritonId = triton::arch::aarch64::ID_INS_LDTRSB;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDTRSH:
            tritonId = triton::arch::aarch64::ID_INS_LDTRSH;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDTRSW:
            tritonId = triton::arch::aarch64::ID_INS_LDTRSW;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDTR:
            tritonId = triton::arch::aarch64::ID_INS_LDTR;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDURB:
            tritonId = triton::arch::aarch64::ID_INS_LDURB;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDUR:
            tritonId = triton::arch::aarch64::ID_INS_LDUR;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDURH:
            tritonId = triton::arch::aarch64::ID_INS_LDURH;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDURSB:
            tritonId = triton::arch::aarch64::ID_INS_LDURSB;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDURSH:
            tritonId = triton::arch::aarch64::ID_INS_LDURSH;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDURSW:
            tritonId = triton::arch::aarch64::ID_INS_LDURSW;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDXP:
            tritonId = triton::arch::aarch64::ID_INS_LDXP;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDXRB:
            tritonId = triton::arch::aarch64::ID_INS_LDXRB;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDXRH:
            tritonId = triton::arch::aarch64::ID_INS_LDXRH;
            break;

          case triton::extlibs::capstone::ARM64_INS_LDXR:
            tritonId = triton::arch::aarch64::ID_INS_LDXR;
            break;

          case triton::extlibs::capstone::ARM64_INS_LSL:
            tritonId = triton::arch::aarch64::ID_INS_LSL;
            break;

          case triton::extlibs::capstone::ARM64_INS_LSR:
            tritonId = triton::arch::aarch64::ID_INS_LSR;
            break;

          case triton::extlibs::capstone::ARM64_INS_MADD:
            tritonId = triton::arch::aarch64::ID_INS_MADD;
            break;

          case triton::extlibs::capstone::ARM64_INS_MLA:
            tritonId = triton::arch::aarch64::ID_INS_MLA;
            break;

          case triton::extlibs::capstone::ARM64_INS_MLS:
            tritonId = triton::arch::aarch64::ID_INS_MLS;
            break;

          case triton::extlibs::capstone::ARM64_INS_MOVI:
            tritonId = triton::arch::aarch64::ID_INS_MOVI;
            break;

          case triton::extlibs::capstone::ARM64_INS_MOVK:
            tritonId = triton::arch::aarch64::ID_INS_MOVK;
            break;

          case triton::extlibs::capstone::ARM64_INS_MOVN:
            tritonId = triton::arch::aarch64::ID_INS_MOVN;
            break;

          case triton::extlibs::capstone::ARM64_INS_MOVZ:
            tritonId = triton::arch::aarch64::ID_INS_MOVZ;
            break;

          case triton::extlibs::capstone::ARM64_INS_MRS:
            tritonId = triton::arch::aarch64::ID_INS_MRS;
            break;

          case triton::extlibs::capstone::ARM64_INS_MSR:
            tritonId = triton::arch::aarch64::ID_INS_MSR;
            break;

          case triton::extlibs::capstone::ARM64_INS_MSUB:
            tritonId = triton::arch::aarch64::ID_INS_MSUB;
            break;

          case triton::extlibs::capstone::ARM64_INS_MUL:
            tritonId = triton::arch::aarch64::ID_INS_MUL;
            break;

          case triton::extlibs::capstone::ARM64_INS_MVNI:
            tritonId = triton::arch::aarch64::ID_INS_MVNI;
            break;

          case triton::extlibs::capstone::ARM64_INS_NEG:
            tritonId = triton::arch::aarch64::ID_INS_NEG;
            break;

          case triton::extlibs::capstone::ARM64_INS_NOT:
            tritonId = triton::arch::aarch64::ID_INS_NOT;
            break;

          case triton::extlibs::capstone::ARM64_INS_ORN:
            tritonId = triton::arch::aarch64::ID_INS_ORN;
            break;

          case triton::extlibs::capstone::ARM64_INS_ORR:
            tritonId = triton::arch::aarch64::ID_INS_ORR;
            break;

          case triton::extlibs::capstone::ARM64_INS_PMULL2:
            tritonId = triton::arch::aarch64::ID_INS_PMULL2;
            break;

          case triton::extlibs::capstone::ARM64_INS_PMULL:
            tritonId = triton::arch::aarch64::ID_INS_PMULL;
            break;

          case triton::extlibs::capstone::ARM64_INS_PMUL:
            tritonId = triton::arch::aarch64::ID_INS_PMUL;
            break;

          case triton::extlibs::capstone::ARM64_INS_PRFM:
            tritonId = triton::arch::aarch64::ID_INS_PRFM;
            break;

          case triton::extlibs::capstone::ARM64_INS_PRFUM:
            tritonId = triton::arch::aarch64::ID_INS_PRFUM;
            break;

          case triton::extlibs::capstone::ARM64_INS_RADDHN:
            tritonId = triton::arch::aarch64::ID_INS_RADDHN;
            break;

          case triton::extlibs::capstone::ARM64_INS_RADDHN2:
            tritonId = triton::arch::aarch64::ID_INS_RADDHN2;
            break;

          case triton::extlibs::capstone::ARM64_INS_RBIT:
            tritonId = triton::arch::aarch64::ID_INS_RBIT;
            break;

          case triton::extlibs::capstone::ARM64_INS_RET:
            tritonId = triton::arch::aarch64::ID_INS_RET;
            break;

          case triton::extlibs::capstone::ARM64_INS_REV16:
            tritonId = triton::arch::aarch64::ID_INS_REV16;
            break;

          case triton::extlibs::capstone::ARM64_INS_REV32:
            tritonId = triton::arch::aarch64::ID_INS_REV32;
            break;

          case triton::extlibs::capstone::ARM64_INS_REV64:
            tritonId = triton::arch::aarch64::ID_INS_REV64;
            break;

          case triton::extlibs::capstone::ARM64_INS_REV:
            tritonId = triton::arch::aarch64::ID_INS_REV;
            break;

          case triton::extlibs::capstone::ARM64_INS_ROR:
            tritonId = triton::arch::aarch64::ID_INS_ROR;
            break;

          case triton::extlibs::capstone::ARM64_INS_RSHRN2:
            tritonId = triton::arch::aarch64::ID_INS_RSHRN2;
            break;

          case triton::extlibs::capstone::ARM64_INS_RSHRN:
            tritonId = triton::arch::aarch64::ID_INS_RSHRN;
            break;

          case triton::extlibs::capstone::ARM64_INS_RSUBHN:
            tritonId = triton::arch::aarch64::ID_INS_RSUBHN;
            break;

          case triton::extlibs::capstone::ARM64_INS_RSUBHN2:
            tritonId = triton::arch::aarch64::ID_INS_RSUBHN2;
            break;

          case triton::extlibs::capstone::ARM64_INS_SABAL2:
            tritonId = triton::arch::aarch64::ID_INS_SABAL2;
            break;

          case triton::extlibs::capstone::ARM64_INS_SABAL:
            tritonId = triton::arch::aarch64::ID_INS_SABAL;
            break;

          case triton::extlibs::capstone::ARM64_INS_SABA:
            tritonId = triton::arch::aarch64::ID_INS_SABA;
            break;

          case triton::extlibs::capstone::ARM64_INS_SABDL2:
            tritonId = triton::arch::aarch64::ID_INS_SABDL2;
            break;

          case triton::extlibs::capstone::ARM64_INS_SABDL:
            tritonId = triton::arch::aarch64::ID_INS_SABDL;
            break;

          case triton::extlibs::capstone::ARM64_INS_SABD:
            tritonId = triton::arch::aarch64::ID_INS_SABD;
            break;

          case triton::extlibs::capstone::ARM64_INS_SADALP:
            tritonId = triton::arch::aarch64::ID_INS_SADALP;
            break;

          case triton::extlibs::capstone::ARM64_INS_SADDLP:
            tritonId = triton::arch::aarch64::ID_INS_SADDLP;
            break;

          case triton::extlibs::capstone::ARM64_INS_SADDLV:
            tritonId = triton::arch::aarch64::ID_INS_SADDLV;
            break;

          case triton::extlibs::capstone::ARM64_INS_SADDL2:
            tritonId = triton::arch::aarch64::ID_INS_SADDL2;
            break;

          case triton::extlibs::capstone::ARM64_INS_SADDL:
            tritonId = triton::arch::aarch64::ID_INS_SADDL;
            break;

          case triton::extlibs::capstone::ARM64_INS_SADDW2:
            tritonId = triton::arch::aarch64::ID_INS_SADDW2;
            break;

          case triton::extlibs::capstone::ARM64_INS_SADDW:
            tritonId = triton::arch::aarch64::ID_INS_SADDW;
            break;

          case triton::extlibs::capstone::ARM64_INS_SBC:
            tritonId = triton::arch::aarch64::ID_INS_SBC;
            break;

          case triton::extlibs::capstone::ARM64_INS_SBFM:
            tritonId = triton::arch::aarch64::ID_INS_SBFM;
            break;

          case triton::extlibs::capstone::ARM64_INS_SCVTF:
            tritonId = triton::arch::aarch64::ID_INS_SCVTF;
            break;

          case triton::extlibs::capstone::ARM64_INS_SDIV:
            tritonId = triton::arch::aarch64::ID_INS_SDIV;
            break;

          case triton::extlibs::capstone::ARM64_INS_SHA1C:
            tritonId = triton::arch::aarch64::ID_INS_SHA1C;
            break;

          case triton::extlibs::capstone::ARM64_INS_SHA1H:
            tritonId = triton::arch::aarch64::ID_INS_SHA1H;
            break;

          case triton::extlibs::capstone::ARM64_INS_SHA1M:
            tritonId = triton::arch::aarch64::ID_INS_SHA1M;
            break;

          case triton::extlibs::capstone::ARM64_INS_SHA1P:
            tritonId = triton::arch::aarch64::ID_INS_SHA1P;
            break;

          case triton::extlibs::capstone::ARM64_INS_SHA1SU0:
            tritonId = triton::arch::aarch64::ID_INS_SHA1SU0;
            break;

          case triton::extlibs::capstone::ARM64_INS_SHA1SU1:
            tritonId = triton::arch::aarch64::ID_INS_SHA1SU1;
            break;

          case triton::extlibs::capstone::ARM64_INS_SHA256H2:
            tritonId = triton::arch::aarch64::ID_INS_SHA256H2;
            break;

          case triton::extlibs::capstone::ARM64_INS_SHA256H:
            tritonId = triton::arch::aarch64::ID_INS_SHA256H;
            break;

          case triton::extlibs::capstone::ARM64_INS_SHA256SU0:
            tritonId = triton::arch::aarch64::ID_INS_SHA256SU0;
            break;

          case triton::extlibs::capstone::ARM64_INS_SHA256SU1:
            tritonId = triton::arch::aarch64::ID_INS_SHA256SU1;
            break;

          case triton::extlibs::capstone::ARM64_INS_SHADD:
            tritonId = triton::arch::aarch64::ID_INS_SHADD;
            break;

          case triton::extlibs::capstone::ARM64_INS_SHLL2:
            tritonId = triton::arch::aarch64::ID_INS_SHLL2;
            break;

          case triton::extlibs::capstone::ARM64_INS_SHLL:
            tritonId = triton::arch::aarch64::ID_INS_SHLL;
            break;

          case triton::extlibs::capstone::ARM64_INS_SHL:
            tritonId = triton::arch::aarch64::ID_INS_SHL;
            break;

          case triton::extlibs::capstone::ARM64_INS_SHRN2:
            tritonId = triton::arch::aarch64::ID_INS_SHRN2;
            break;

          case triton::extlibs::capstone::ARM64_INS_SHRN:
            tritonId = triton::arch::aarch64::ID_INS_SHRN;
            break;

          case triton::extlibs::capstone::ARM64_INS_SHSUB:
            tritonId = triton::arch::aarch64::ID_INS_SHSUB;
            break;

          case triton::extlibs::capstone::ARM64_INS_SLI:
            tritonId = triton::arch::aarch64::ID_INS_SLI;
            break;

          case triton::extlibs::capstone::ARM64_INS_SMADDL:
            tritonId = triton::arch::aarch64::ID_INS_SMADDL;
            break;

          case triton::extlibs::capstone::ARM64_INS_SMAXP:
            tritonId = triton::arch::aarch64::ID_INS_SMAXP;
            break;

          case triton::extlibs::capstone::ARM64_INS_SMAXV:
            tritonId = triton::arch::aarch64::ID_INS_SMAXV;
            break;

          case triton::extlibs::capstone::ARM64_INS_SMAX:
            tritonId = triton::arch::aarch64::ID_INS_SMAX;
            break;

          case triton::extlibs::capstone::ARM64_INS_SMC:
            tritonId = triton::arch::aarch64::ID_INS_SMC;
            break;

          case triton::extlibs::capstone::ARM64_INS_SMINP:
            tritonId = triton::arch::aarch64::ID_INS_SMINP;
            break;

          case triton::extlibs::capstone::ARM64_INS_SMINV:
            tritonId = triton::arch::aarch64::ID_INS_SMINV;
            break;

          case triton::extlibs::capstone::ARM64_INS_SMIN:
            tritonId = triton::arch::aarch64::ID_INS_SMIN;
            break;

          case triton::extlibs::capstone::ARM64_INS_SMLAL2:
            tritonId = triton::arch::aarch64::ID_INS_SMLAL2;
            break;

          case triton::extlibs::capstone::ARM64_INS_SMLAL:
            tritonId = triton::arch::aarch64::ID_INS_SMLAL;
            break;

          case triton::extlibs::capstone::ARM64_INS_SMLSL2:
            tritonId = triton::arch::aarch64::ID_INS_SMLSL2;
            break;

          case triton::extlibs::capstone::ARM64_INS_SMLSL:
            tritonId = triton::arch::aarch64::ID_INS_SMLSL;
            break;

          case triton::extlibs::capstone::ARM64_INS_SMOV:
            tritonId = triton::arch::aarch64::ID_INS_SMOV;
            break;

          case triton::extlibs::capstone::ARM64_INS_SMSUBL:
            tritonId = triton::arch::aarch64::ID_INS_SMSUBL;
            break;

          case triton::extlibs::capstone::ARM64_INS_SMULH:
            tritonId = triton::arch::aarch64::ID_INS_SMULH;
            break;

          case triton::extlibs::capstone::ARM64_INS_SMULL2:
            tritonId = triton::arch::aarch64::ID_INS_SMULL2;
            break;

          case triton::extlibs::capstone::ARM64_INS_SMULL:
            tritonId = triton::arch::aarch64::ID_INS_SMULL;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQABS:
            tritonId = triton::arch::aarch64::ID_INS_SQABS;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQADD:
            tritonId = triton::arch::aarch64::ID_INS_SQADD;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQDMLAL:
            tritonId = triton::arch::aarch64::ID_INS_SQDMLAL;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQDMLAL2:
            tritonId = triton::arch::aarch64::ID_INS_SQDMLAL2;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQDMLSL:
            tritonId = triton::arch::aarch64::ID_INS_SQDMLSL;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQDMLSL2:
            tritonId = triton::arch::aarch64::ID_INS_SQDMLSL2;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQDMULH:
            tritonId = triton::arch::aarch64::ID_INS_SQDMULH;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQDMULL:
            tritonId = triton::arch::aarch64::ID_INS_SQDMULL;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQDMULL2:
            tritonId = triton::arch::aarch64::ID_INS_SQDMULL2;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQNEG:
            tritonId = triton::arch::aarch64::ID_INS_SQNEG;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQRDMULH:
            tritonId = triton::arch::aarch64::ID_INS_SQRDMULH;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQRSHL:
            tritonId = triton::arch::aarch64::ID_INS_SQRSHL;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQRSHRN:
            tritonId = triton::arch::aarch64::ID_INS_SQRSHRN;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQRSHRN2:
            tritonId = triton::arch::aarch64::ID_INS_SQRSHRN2;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQRSHRUN:
            tritonId = triton::arch::aarch64::ID_INS_SQRSHRUN;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQRSHRUN2:
            tritonId = triton::arch::aarch64::ID_INS_SQRSHRUN2;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQSHLU:
            tritonId = triton::arch::aarch64::ID_INS_SQSHLU;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQSHL:
            tritonId = triton::arch::aarch64::ID_INS_SQSHL;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQSHRN:
            tritonId = triton::arch::aarch64::ID_INS_SQSHRN;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQSHRN2:
            tritonId = triton::arch::aarch64::ID_INS_SQSHRN2;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQSHRUN:
            tritonId = triton::arch::aarch64::ID_INS_SQSHRUN;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQSHRUN2:
            tritonId = triton::arch::aarch64::ID_INS_SQSHRUN2;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQSUB:
            tritonId = triton::arch::aarch64::ID_INS_SQSUB;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQXTN2:
            tritonId = triton::arch::aarch64::ID_INS_SQXTN2;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQXTN:
            tritonId = triton::arch::aarch64::ID_INS_SQXTN;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQXTUN2:
            tritonId = triton::arch::aarch64::ID_INS_SQXTUN2;
            break;

          case triton::extlibs::capstone::ARM64_INS_SQXTUN:
            tritonId = triton::arch::aarch64::ID_INS_SQXTUN;
            break;

          case triton::extlibs::capstone::ARM64_INS_SRHADD:
            tritonId = triton::arch::aarch64::ID_INS_SRHADD;
            break;

          case triton::extlibs::capstone::ARM64_INS_SRI:
            tritonId = triton::arch::aarch64::ID_INS_SRI;
            break;

          case triton::extlibs::capstone::ARM64_INS_SRSHL:
            tritonId = triton::arch::aarch64::ID_INS_SRSHL;
            break;

          case triton::extlibs::capstone::ARM64_INS_SRSHR:
            tritonId = triton::arch::aarch64::ID_INS_SRSHR;
            break;

          case triton::extlibs::capstone::ARM64_INS_SRSRA:
            tritonId = triton::arch::aarch64::ID_INS_SRSRA;
            break;

          case triton::extlibs::capstone::ARM64_INS_SSHLL2:
            tritonId = triton::arch::aarch64::ID_INS_SSHLL2;
            break;

          case triton::extlibs::capstone::ARM64_INS_SSHLL:
            tritonId = triton::arch::aarch64::ID_INS_SSHLL;
            break;

          case triton::extlibs::capstone::ARM64_INS_SSHL:
            tritonId = triton::arch::aarch64::ID_INS_SSHL;
            break;

          case triton::extlibs::capstone::ARM64_INS_SSHR:
            tritonId = triton::arch::aarch64::ID_INS_SSHR;
            break;

          case triton::extlibs::capstone::ARM64_INS_SSRA:
            tritonId = triton::arch::aarch64::ID_INS_SSRA;
            break;

          case triton::extlibs::capstone::ARM64_INS_SSUBL2:
            tritonId = triton::arch::aarch64::ID_INS_SSUBL2;
            break;

          case triton::extlibs::capstone::ARM64_INS_SSUBL:
            tritonId = triton::arch::aarch64::ID_INS_SSUBL;
            break;

          case triton::extlibs::capstone::ARM64_INS_SSUBW2:
            tritonId = triton::arch::aarch64::ID_INS_SSUBW2;
            break;

          case triton::extlibs::capstone::ARM64_INS_SSUBW:
            tritonId = triton::arch::aarch64::ID_INS_SSUBW;
            break;

          case triton::extlibs::capstone::ARM64_INS_ST1:
            tritonId = triton::arch::aarch64::ID_INS_ST1;
            break;

          case triton::extlibs::capstone::ARM64_INS_ST2:
            tritonId = triton::arch::aarch64::ID_INS_ST2;
            break;

          case triton::extlibs::capstone::ARM64_INS_ST3:
            tritonId = triton::arch::aarch64::ID_INS_ST3;
            break;

          case triton::extlibs::capstone::ARM64_INS_ST4:
            tritonId = triton::arch::aarch64::ID_INS_ST4;
            break;

          case triton::extlibs::capstone::ARM64_INS_STLRB:
            tritonId = triton::arch::aarch64::ID_INS_STLRB;
            break;

          case triton::extlibs::capstone::ARM64_INS_STLRH:
            tritonId = triton::arch::aarch64::ID_INS_STLRH;
            break;

          case triton::extlibs::capstone::ARM64_INS_STLR:
            tritonId = triton::arch::aarch64::ID_INS_STLR;
            break;

          case triton::extlibs::capstone::ARM64_INS_STLXP:
            tritonId = triton::arch::aarch64::ID_INS_STLXP;
            break;

          case triton::extlibs::capstone::ARM64_INS_STLXRB:
            tritonId = triton::arch::aarch64::ID_INS_STLXRB;
            break;

          case triton::extlibs::capstone::ARM64_INS_STLXRH:
            tritonId = triton::arch::aarch64::ID_INS_STLXRH;
            break;

          case triton::extlibs::capstone::ARM64_INS_STLXR:
            tritonId = triton::arch::aarch64::ID_INS_STLXR;
            break;

          case triton::extlibs::capstone::ARM64_INS_STNP:
            tritonId = triton::arch::aarch64::ID_INS_STNP;
            break;

          case triton::extlibs::capstone::ARM64_INS_STP:
            tritonId = triton::arch::aarch64::ID_INS_STP;
            break;

          case triton::extlibs::capstone::ARM64_INS_STRB:
            tritonId = triton::arch::aarch64::ID_INS_STRB;
            break;

          case triton::extlibs::capstone::ARM64_INS_STR:
            tritonId = triton::arch::aarch64::ID_INS_STR;
            break;

          case triton::extlibs::capstone::ARM64_INS_STRH:
            tritonId = triton::arch::aarch64::ID_INS_STRH;
            break;

          case triton::extlibs::capstone::ARM64_INS_STTRB:
            tritonId = triton::arch::aarch64::ID_INS_STTRB;
            break;

          case triton::extlibs::capstone::ARM64_INS_STTRH:
            tritonId = triton::arch::aarch64::ID_INS_STTRH;
            break;

          case triton::extlibs::capstone::ARM64_INS_STTR:
            tritonId = triton::arch::aarch64::ID_INS_STTR;
            break;

          case triton::extlibs::capstone::ARM64_INS_STURB:
            tritonId = triton::arch::aarch64::ID_INS_STURB;
            break;

          case triton::extlibs::capstone::ARM64_INS_STUR:
            tritonId = triton::arch::aarch64::ID_INS_STUR;
            break;

          case triton::extlibs::capstone::ARM64_INS_STURH:
            tritonId = triton::arch::aarch64::ID_INS_STURH;
            break;

          case triton::extlibs::capstone::ARM64_INS_STXP:
            tritonId = triton::arch::aarch64::ID_INS_STXP;
            break;

          case triton::extlibs::capstone::ARM64_INS_STXRB:
            tritonId = triton::arch::aarch64::ID_INS_STXRB;
            break;

          case triton::extlibs::capstone::ARM64_INS_STXRH:
            tritonId = triton::arch::aarch64::ID_INS_STXRH;
            break;

          case triton::extlibs::capstone::ARM64_INS_STXR:
            tritonId = triton::arch::aarch64::ID_INS_STXR;
            break;

          case triton::extlibs::capstone::ARM64_INS_SUBHN:
            tritonId = triton::arch::aarch64::ID_INS_SUBHN;
            break;

          case triton::extlibs::capstone::ARM64_INS_SUBHN2:
            tritonId = triton::arch::aarch64::ID_INS_SUBHN2;
            break;

          case triton::extlibs::capstone::ARM64_INS_SUB:
            tritonId = triton::arch::aarch64::ID_INS_SUB;
            break;

          case triton::extlibs::capstone::ARM64_INS_SUQADD:
            tritonId = triton::arch::aarch64::ID_INS_SUQADD;
            break;

          case triton::extlibs::capstone::ARM64_INS_SVC:
            tritonId = triton::arch::aarch64::ID_INS_SVC;
            break;

          case triton::extlibs::capstone::ARM64_INS_SYSL:
            tritonId = triton::arch::aarch64::ID_INS_SYSL;
            break;

          case triton::extlibs::capstone::ARM64_INS_SYS:
            tritonId = triton::arch::aarch64::ID_INS_SYS;
            break;

          case triton::extlibs::capstone::ARM64_INS_TBL:
            tritonId = triton::arch::aarch64::ID_INS_TBL;
            break;

          case triton::extlibs::capstone::ARM64_INS_TBNZ:
            tritonId = triton::arch::aarch64::ID_INS_TBNZ;
            break;

          case triton::extlibs::capstone::ARM64_INS_TBX:
            tritonId = triton::arch::aarch64::ID_INS_TBX;
            break;

          case triton::extlibs::capstone::ARM64_INS_TBZ:
            tritonId = triton::arch::aarch64::ID_INS_TBZ;
            break;

          case triton::extlibs::capstone::ARM64_INS_TRN1:
            tritonId = triton::arch::aarch64::ID_INS_TRN1;
            break;

          case triton::extlibs::capstone::ARM64_INS_TRN2:
            tritonId = triton::arch::aarch64::ID_INS_TRN2;
            break;

          case triton::extlibs::capstone::ARM64_INS_UABAL2:
            tritonId = triton::arch::aarch64::ID_INS_UABAL2;
            break;

          case triton::extlibs::capstone::ARM64_INS_UABAL:
            tritonId = triton::arch::aarch64::ID_INS_UABAL;
            break;

          case triton::extlibs::capstone::ARM64_INS_UABA:
            tritonId = triton::arch::aarch64::ID_INS_UABA;
            break;

          case triton::extlibs::capstone::ARM64_INS_UABDL2:
            tritonId = triton::arch::aarch64::ID_INS_UABDL2;
            break;

          case triton::extlibs::capstone::ARM64_INS_UABDL:
            tritonId = triton::arch::aarch64::ID_INS_UABDL;
            break;

          case triton::extlibs::capstone::ARM64_INS_UABD:
            tritonId = triton::arch::aarch64::ID_INS_UABD;
            break;

          case triton::extlibs::capstone::ARM64_INS_UADALP:
            tritonId = triton::arch::aarch64::ID_INS_UADALP;
            break;

          case triton::extlibs::capstone::ARM64_INS_UADDLP:
            tritonId = triton::arch::aarch64::ID_INS_UADDLP;
            break;

          case triton::extlibs::capstone::ARM64_INS_UADDLV:
            tritonId = triton::arch::aarch64::ID_INS_UADDLV;
            break;

          case triton::extlibs::capstone::ARM64_INS_UADDL2:
            tritonId = triton::arch::aarch64::ID_INS_UADDL2;
            break;

          case triton::extlibs::capstone::ARM64_INS_UADDL:
            tritonId = triton::arch::aarch64::ID_INS_UADDL;
            break;

          case triton::extlibs::capstone::ARM64_INS_UADDW2:
            tritonId = triton::arch::aarch64::ID_INS_UADDW2;
            break;

          case triton::extlibs::capstone::ARM64_INS_UADDW:
            tritonId = triton::arch::aarch64::ID_INS_UADDW;
            break;

          case triton::extlibs::capstone::ARM64_INS_UBFM:
            tritonId = triton::arch::aarch64::ID_INS_UBFM;
            break;

          case triton::extlibs::capstone::ARM64_INS_UCVTF:
            tritonId = triton::arch::aarch64::ID_INS_UCVTF;
            break;

          case triton::extlibs::capstone::ARM64_INS_UDIV:
            tritonId = triton::arch::aarch64::ID_INS_UDIV;
            break;

          case triton::extlibs::capstone::ARM64_INS_UHADD:
            tritonId = triton::arch::aarch64::ID_INS_UHADD;
            break;

          case triton::extlibs::capstone::ARM64_INS_UHSUB:
            tritonId = triton::arch::aarch64::ID_INS_UHSUB;
            break;

          case triton::extlibs::capstone::ARM64_INS_UMADDL:
            tritonId = triton::arch::aarch64::ID_INS_UMADDL;
            break;

          case triton::extlibs::capstone::ARM64_INS_UMAXP:
            tritonId = triton::arch::aarch64::ID_INS_UMAXP;
            break;

          case triton::extlibs::capstone::ARM64_INS_UMAXV:
            tritonId = triton::arch::aarch64::ID_INS_UMAXV;
            break;

          case triton::extlibs::capstone::ARM64_INS_UMAX:
            tritonId = triton::arch::aarch64::ID_INS_UMAX;
            break;

          case triton::extlibs::capstone::ARM64_INS_UMINP:
            tritonId = triton::arch::aarch64::ID_INS_UMINP;
            break;

          case triton::extlibs::capstone::ARM64_INS_UMINV:
            tritonId = triton::arch::aarch64::ID_INS_UMINV;
            break;

          case triton::extlibs::capstone::ARM64_INS_UMIN:
            tritonId = triton::arch::aarch64::ID_INS_UMIN;
            break;

          case triton::extlibs::capstone::ARM64_INS_UMLAL2:
            tritonId = triton::arch::aarch64::ID_INS_UMLAL2;
            break;

          case triton::extlibs::capstone::ARM64_INS_UMLAL:
            tritonId = triton::arch::aarch64::ID_INS_UMLAL;
            break;

          case triton::extlibs::capstone::ARM64_INS_UMLSL2:
            tritonId = triton::arch::aarch64::ID_INS_UMLSL2;
            break;

          case triton::extlibs::capstone::ARM64_INS_UMLSL:
            tritonId = triton::arch::aarch64::ID_INS_UMLSL;
            break;

          case triton::extlibs::capstone::ARM64_INS_UMOV:
            tritonId = triton::arch::aarch64::ID_INS_UMOV;
            break;

          case triton::extlibs::capstone::ARM64_INS_UMSUBL:
            tritonId = triton::arch::aarch64::ID_INS_UMSUBL;
            break;

          case triton::extlibs::capstone::ARM64_INS_UMULH:
            tritonId = triton::arch::aarch64::ID_INS_UMULH;
            break;

          case triton::extlibs::capstone::ARM64_INS_UMULL2:
            tritonId = triton::arch::aarch64::ID_INS_UMULL2;
            break;

          case triton::extlibs::capstone::ARM64_INS_UMULL:
            tritonId = triton::arch::aarch64::ID_INS_UMULL;
            break;

          case triton::extlibs::capstone::ARM64_INS_UQADD:
            tritonId = triton::arch::aarch64::ID_INS_UQADD;
            break;

          case triton::extlibs::capstone::ARM64_INS_UQRSHL:
            tritonId = triton::arch::aarch64::ID_INS_UQRSHL;
            break;

          case triton::extlibs::capstone::ARM64_INS_UQRSHRN:
            tritonId = triton::arch::aarch64::ID_INS_UQRSHRN;
            break;

          case triton::extlibs::capstone::ARM64_INS_UQRSHRN2:
            tritonId = triton::arch::aarch64::ID_INS_UQRSHRN2;
            break;

          case triton::extlibs::capstone::ARM64_INS_UQSHL:
            tritonId = triton::arch::aarch64::ID_INS_UQSHL;
            break;

          case triton::extlibs::capstone::ARM64_INS_UQSHRN:
            tritonId = triton::arch::aarch64::ID_INS_UQSHRN;
            break;

          case triton::extlibs::capstone::ARM64_INS_UQSHRN2:
            tritonId = triton::arch::aarch64::ID_INS_UQSHRN2;
            break;

          case triton::extlibs::capstone::ARM64_INS_UQSUB:
            tritonId = triton::arch::aarch64::ID_INS_UQSUB;
            break;

          case triton::extlibs::capstone::ARM64_INS_UQXTN2:
            tritonId = triton::arch::aarch64::ID_INS_UQXTN2;
            break;

          case triton::extlibs::capstone::ARM64_INS_UQXTN:
            tritonId = triton::arch::aarch64::ID_INS_UQXTN;
            break;

          case triton::extlibs::capstone::ARM64_INS_URECPE:
            tritonId = triton::arch::aarch64::ID_INS_URECPE;
            break;

          case triton::extlibs::capstone::ARM64_INS_URHADD:
            tritonId = triton::arch::aarch64::ID_INS_URHADD;
            break;

          case triton::extlibs::capstone::ARM64_INS_URSHL:
            tritonId = triton::arch::aarch64::ID_INS_URSHL;
            break;

          case triton::extlibs::capstone::ARM64_INS_URSHR:
            tritonId = triton::arch::aarch64::ID_INS_URSHR;
            break;

          case triton::extlibs::capstone::ARM64_INS_URSQRTE:
            tritonId = triton::arch::aarch64::ID_INS_URSQRTE;
            break;

          case triton::extlibs::capstone::ARM64_INS_URSRA:
            tritonId = triton::arch::aarch64::ID_INS_URSRA;
            break;

          case triton::extlibs::capstone::ARM64_INS_USHLL2:
            tritonId = triton::arch::aarch64::ID_INS_USHLL2;
            break;

          case triton::extlibs::capstone::ARM64_INS_USHLL:
            tritonId = triton::arch::aarch64::ID_INS_USHLL;
            break;

          case triton::extlibs::capstone::ARM64_INS_USHL:
            tritonId = triton::arch::aarch64::ID_INS_USHL;
            break;

          case triton::extlibs::capstone::ARM64_INS_USHR:
            tritonId = triton::arch::aarch64::ID_INS_USHR;
            break;

          case triton::extlibs::capstone::ARM64_INS_USQADD:
            tritonId = triton::arch::aarch64::ID_INS_USQADD;
            break;

          case triton::extlibs::capstone::ARM64_INS_USRA:
            tritonId = triton::arch::aarch64::ID_INS_USRA;
            break;

          case triton::extlibs::capstone::ARM64_INS_USUBL2:
            tritonId = triton::arch::aarch64::ID_INS_USUBL2;
            break;

          case triton::extlibs::capstone::ARM64_INS_USUBL:
            tritonId = triton::arch::aarch64::ID_INS_USUBL;
            break;

          case triton::extlibs::capstone::ARM64_INS_USUBW2:
            tritonId = triton::arch::aarch64::ID_INS_USUBW2;
            break;

          case triton::extlibs::capstone::ARM64_INS_USUBW:
            tritonId = triton::arch::aarch64::ID_INS_USUBW;
            break;

          case triton::extlibs::capstone::ARM64_INS_UZP1:
            tritonId = triton::arch::aarch64::ID_INS_UZP1;
            break;

          case triton::extlibs::capstone::ARM64_INS_UZP2:
            tritonId = triton::arch::aarch64::ID_INS_UZP2;
            break;

          case triton::extlibs::capstone::ARM64_INS_XTN2:
            tritonId = triton::arch::aarch64::ID_INS_XTN2;
            break;

          case triton::extlibs::capstone::ARM64_INS_XTN:
            tritonId = triton::arch::aarch64::ID_INS_XTN;
            break;

          case triton::extlibs::capstone::ARM64_INS_ZIP1:
            tritonId = triton::arch::aarch64::ID_INS_ZIP1;
            break;

          case triton::extlibs::capstone::ARM64_INS_ZIP2:
            tritonId = triton::arch::aarch64::ID_INS_ZIP2;
            break;

          /* From here there are alias but considered as instruction */

          case triton::extlibs::capstone::ARM64_INS_MNEG:
            tritonId = triton::arch::aarch64::ID_INS_MNEG;
            break;

          case triton::extlibs::capstone::ARM64_INS_UMNEGL:
            tritonId = triton::arch::aarch64::ID_INS_UMNEGL;
            break;

          case triton::extlibs::capstone::ARM64_INS_SMNEGL:
            tritonId = triton::arch::aarch64::ID_INS_SMNEGL;
            break;

          case triton::extlibs::capstone::ARM64_INS_NOP:
            tritonId = triton::arch::aarch64::ID_INS_NOP;
            break;

          case triton::extlibs::capstone::ARM64_INS_YIELD:
            tritonId = triton::arch::aarch64::ID_INS_YIELD;
            break;

          case triton::extlibs::capstone::ARM64_INS_WFE:
            tritonId = triton::arch::aarch64::ID_INS_WFE;
            break;

          case triton::extlibs::capstone::ARM64_INS_WFI:
            tritonId = triton::arch::aarch64::ID_INS_WFI;
            break;

          case triton::extlibs::capstone::ARM64_INS_SEV:
            tritonId = triton::arch::aarch64::ID_INS_SEV;
            break;

          case triton::extlibs::capstone::ARM64_INS_SEVL:
            tritonId = triton::arch::aarch64::ID_INS_SEVL;
            break;

          case triton::extlibs::capstone::ARM64_INS_NGC:
            tritonId = triton::arch::aarch64::ID_INS_NGC;
            break;

          case triton::extlibs::capstone::ARM64_INS_SBFIZ:
            tritonId = triton::arch::aarch64::ID_INS_SBFIZ;
            break;

          case triton::extlibs::capstone::ARM64_INS_UBFIZ:
            tritonId = triton::arch::aarch64::ID_INS_UBFIZ;
            break;

          case triton::extlibs::capstone::ARM64_INS_SBFX:
            tritonId = triton::arch::aarch64::ID_INS_SBFX;
            break;

          case triton::extlibs::capstone::ARM64_INS_UBFX:
            tritonId = triton::arch::aarch64::ID_INS_UBFX;
            break;

          case triton::extlibs::capstone::ARM64_INS_BFI:
            tritonId = triton::arch::aarch64::ID_INS_BFI;
            break;

          case triton::extlibs::capstone::ARM64_INS_BFXIL:
            tritonId = triton::arch::aarch64::ID_INS_BFXIL;
            break;

          case triton::extlibs::capstone::ARM64_INS_CMN:
            tritonId = triton::arch::aarch64::ID_INS_CMN;
            break;

          case triton::extlibs::capstone::ARM64_INS_MVN:
            tritonId = triton::arch::aarch64::ID_INS_MVN;
            break;

          case triton::extlibs::capstone::ARM64_INS_TST:
            tritonId = triton::arch::aarch64::ID_INS_TST;
            break;

          case triton::extlibs::capstone::ARM64_INS_CSET:
            tritonId = triton::arch::aarch64::ID_INS_CSET;
            break;

          case triton::extlibs::capstone::ARM64_INS_CINC:
            tritonId = triton::arch::aarch64::ID_INS_CINC;
            break;

          case triton::extlibs::capstone::ARM64_INS_CSETM:
            tritonId = triton::arch::aarch64::ID_INS_CSETM;
            break;

          case triton::extlibs::capstone::ARM64_INS_CINV:
            tritonId = triton::arch::aarch64::ID_INS_CINV;
            break;

          case triton::extlibs::capstone::ARM64_INS_CNEG:
            tritonId = triton::arch::aarch64::ID_INS_CNEG;
            break;

          case triton::extlibs::capstone::ARM64_INS_SXTB:
            tritonId = triton::arch::aarch64::ID_INS_SXTB;
            break;

          case triton::extlibs::capstone::ARM64_INS_SXTH:
            tritonId = triton::arch::aarch64::ID_INS_SXTH;
            break;

          case triton::extlibs::capstone::ARM64_INS_SXTW:
            tritonId = triton::arch::aarch64::ID_INS_SXTW;
            break;

          case triton::extlibs::capstone::ARM64_INS_CMP:
            tritonId = triton::arch::aarch64::ID_INS_CMP;
            break;

          case triton::extlibs::capstone::ARM64_INS_UXTB:
            tritonId = triton::arch::aarch64::ID_INS_UXTB;
            break;

          case triton::extlibs::capstone::ARM64_INS_UXTH:
            tritonId = triton::arch::aarch64::ID_INS_UXTH;
            break;

          case triton::extlibs::capstone::ARM64_INS_UXTW:
            tritonId = triton::arch::aarch64::ID_INS_UXTW;
            break;

          case triton::extlibs::capstone::ARM64_INS_IC:
            tritonId = triton::arch::aarch64::ID_INS_IC;
            break;

          case triton::extlibs::capstone::ARM64_INS_DC:
            tritonId = triton::arch::aarch64::ID_INS_DC;
            break;

          case triton::extlibs::capstone::ARM64_INS_AT:
            tritonId = triton::arch::aarch64::ID_INS_AT;
            break;

          case triton::extlibs::capstone::ARM64_INS_TLBI:
            tritonId = triton::arch::aarch64::ID_INS_TLBI;
            break;

          default:
            tritonId = triton::arch::aarch64::ID_INS_INVALID;
            break;
        }

        return tritonId;
      }

    }; /* aarch64 namespace */
  }; /* arch namespace */
}; /* triton namespace */
