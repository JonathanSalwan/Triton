//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <triton/arm32Specifications.hpp>
#include <triton/architecture.hpp>
#include <triton/cpuSize.hpp>
#include <triton/exceptions.hpp>
#include <triton/externalLibs.hpp>



namespace triton {
  namespace arch {
    namespace arm {
      namespace arm32 {

        Arm32Specifications::Arm32Specifications(triton::arch::architecture_e arch) {
          if (arch != triton::arch::ARCH_ARM32)
              throw triton::exceptions::Architecture("ARM32Specifications::ARM32Specifications(): Invalid architecture.");

            // Fill id2reg and name2id with those available in Arm32 from spec
            #define REG_SPEC(UPPER_NAME, LOWER_NAME, ARM32_UPPER, ARM32_LOWER, ARM32_PARENT, MUTABLE) \
              id2reg.emplace(ID_REG_ARM32_##UPPER_NAME,                                               \
                                 triton::arch::Register(triton::arch::ID_REG_ARM32_##UPPER_NAME,      \
                                                        #LOWER_NAME,                                  \
                                                        triton::arch::ID_REG_ARM32_##ARM32_PARENT,    \
                                                        ARM32_UPPER,                                  \
                                                        ARM32_LOWER,                                  \
                                                        MUTABLE)                                      \
                                );                                                                    \
              name2id.emplace(#LOWER_NAME, ID_REG_ARM32_##UPPER_NAME);
            // Handle register not available in capstone as normal registers
            #define REG_SPEC_NO_CAPSTONE REG_SPEC
            #include "triton/arm32.spec"
        }


        triton::arch::register_e Arm32Specifications::capstoneRegisterToTritonRegister(triton::uint32 id) const {
          triton::arch::register_e tritonId = triton::arch::ID_REG_INVALID;

          switch (id) {
            // Convert registers from capstone value to triton value
            #define REG_SPEC(UPPER_NAME, _1, _2, _3, _4, _5)      \
            case triton::extlibs::capstone::ARM_REG_##UPPER_NAME: \
              tritonId = triton::arch::ID_REG_ARM32_##UPPER_NAME; \
              break;
            // Ignore registers not available in capstone
            #define REG_SPEC_NO_CAPSTONE(_1, _2, _3, _4, _5, _6)
            #include "triton/arm32.spec"

            default:
              tritonId = triton::arch::ID_REG_INVALID;
              break;
          }

          return tritonId;
        }


        triton::arch::arm::shift_e Arm32Specifications::capstoneShiftToTritonShift(triton::uint32 id) const {
          triton::arch::arm::shift_e tritonId = triton::arch::arm::ID_SHIFT_INVALID;

          switch (id) {
            case triton::extlibs::capstone::ARM_SFT_INVALID:
              tritonId = triton::arch::arm::ID_SHIFT_INVALID;
              break;

            case triton::extlibs::capstone::ARM_SFT_ASR:
              tritonId = triton::arch::arm::ID_SHIFT_ASR;
              break;

            case triton::extlibs::capstone::ARM_SFT_LSL:
              tritonId = triton::arch::arm::ID_SHIFT_LSL;
              break;

            case triton::extlibs::capstone::ARM_SFT_LSR:
              tritonId = triton::arch::arm::ID_SHIFT_LSR;
              break;

            case triton::extlibs::capstone::ARM_SFT_ROR:
              tritonId = triton::arch::arm::ID_SHIFT_ROR;
              break;

            case triton::extlibs::capstone::ARM_SFT_RRX:
              tritonId = triton::arch::arm::ID_SHIFT_RRX;
              break;

            case triton::extlibs::capstone::ARM_SFT_ASR_REG:
              tritonId = triton::arch::arm::ID_SHIFT_ASR_REG;
              break;

            case triton::extlibs::capstone::ARM_SFT_LSL_REG:
              tritonId = triton::arch::arm::ID_SHIFT_LSL_REG;
              break;

            case triton::extlibs::capstone::ARM_SFT_LSR_REG:
              tritonId = triton::arch::arm::ID_SHIFT_LSR_REG;
              break;

            case triton::extlibs::capstone::ARM_SFT_ROR_REG:
              tritonId = triton::arch::arm::ID_SHIFT_ROR_REG;
              break;

            case triton::extlibs::capstone::ARM_SFT_RRX_REG:
              tritonId = triton::arch::arm::ID_SHIFT_RRX_REG;
              break;

            default:
              tritonId = triton::arch::arm::ID_SHIFT_INVALID;
              break;
          }

          return tritonId;
        }


        triton::arch::arm::condition_e Arm32Specifications::capstoneConditionToTritonCondition(triton::uint32 id) const {
          triton::arch::arm::condition_e tritonId = triton::arch::arm::ID_CONDITION_INVALID;

          switch (id) {
            case triton::extlibs::capstone::ARM_CC_INVALID:
              tritonId = triton::arch::arm::ID_CONDITION_INVALID;
              break;

            case triton::extlibs::capstone::ARM_CC_AL:
              tritonId = triton::arch::arm::ID_CONDITION_AL;
              break;

            case triton::extlibs::capstone::ARM_CC_EQ:
              tritonId = triton::arch::arm::ID_CONDITION_EQ;
              break;

            case triton::extlibs::capstone::ARM_CC_GE:
              tritonId = triton::arch::arm::ID_CONDITION_GE;
              break;

            case triton::extlibs::capstone::ARM_CC_GT:
              tritonId = triton::arch::arm::ID_CONDITION_GT;
              break;

            case triton::extlibs::capstone::ARM_CC_HI:
              tritonId = triton::arch::arm::ID_CONDITION_HI;
              break;

            case triton::extlibs::capstone::ARM_CC_HS:
              tritonId = triton::arch::arm::ID_CONDITION_HS;
              break;

            case triton::extlibs::capstone::ARM_CC_LE:
              tritonId = triton::arch::arm::ID_CONDITION_LE;
              break;

            case triton::extlibs::capstone::ARM_CC_LO:
              tritonId = triton::arch::arm::ID_CONDITION_LO;
              break;

            case triton::extlibs::capstone::ARM_CC_LS:
              tritonId = triton::arch::arm::ID_CONDITION_LS;
              break;

            case triton::extlibs::capstone::ARM_CC_LT:
              tritonId = triton::arch::arm::ID_CONDITION_LT;
              break;

            case triton::extlibs::capstone::ARM_CC_MI:
              tritonId = triton::arch::arm::ID_CONDITION_MI;
              break;

            case triton::extlibs::capstone::ARM_CC_NE:
              tritonId = triton::arch::arm::ID_CONDITION_NE;
              break;

            case triton::extlibs::capstone::ARM_CC_PL:
              tritonId = triton::arch::arm::ID_CONDITION_PL;
              break;

            case triton::extlibs::capstone::ARM_CC_VC:
              tritonId = triton::arch::arm::ID_CONDITION_VC;
              break;

            case triton::extlibs::capstone::ARM_CC_VS:
              tritonId = triton::arch::arm::ID_CONDITION_VS;
              break;

            default:
              tritonId = triton::arch::arm::ID_CONDITION_INVALID;
              break;
          }

          return tritonId;
        }


        triton::uint32 Arm32Specifications::capstoneInstructionToTritonInstruction(triton::uint32 id) const {
          triton::uint32 tritonId = triton::arch::arm::arm32::ID_INS_INVALID;

          switch (id) {
            case triton::extlibs::capstone::ARM_INS_INVALID:
              tritonId = triton::arch::arm::arm32::ID_INS_INVALID;
              break;

            case triton::extlibs::capstone::ARM_INS_ADC:
              tritonId = triton::arch::arm::arm32::ID_INS_ADC;
              break;

            case triton::extlibs::capstone::ARM_INS_ADD:
              tritonId = triton::arch::arm::arm32::ID_INS_ADD;
              break;

            case triton::extlibs::capstone::ARM_INS_ADR:
              tritonId = triton::arch::arm::arm32::ID_INS_ADR;
              break;

            case triton::extlibs::capstone::ARM_INS_AESD:
              tritonId = triton::arch::arm::arm32::ID_INS_AESD;
              break;

            case triton::extlibs::capstone::ARM_INS_AESE:
              tritonId = triton::arch::arm::arm32::ID_INS_AESE;
              break;

            case triton::extlibs::capstone::ARM_INS_AESIMC:
              tritonId = triton::arch::arm::arm32::ID_INS_AESIMC;
              break;

            case triton::extlibs::capstone::ARM_INS_AESMC:
              tritonId = triton::arch::arm::arm32::ID_INS_AESMC;
              break;

            case triton::extlibs::capstone::ARM_INS_AND:
              tritonId = triton::arch::arm::arm32::ID_INS_AND;
              break;

            case triton::extlibs::capstone::ARM_INS_BFC:
              tritonId = triton::arch::arm::arm32::ID_INS_BFC;
              break;

            case triton::extlibs::capstone::ARM_INS_BFI:
              tritonId = triton::arch::arm::arm32::ID_INS_BFI;
              break;

            case triton::extlibs::capstone::ARM_INS_BIC:
              tritonId = triton::arch::arm::arm32::ID_INS_BIC;
              break;

            case triton::extlibs::capstone::ARM_INS_BKPT:
              tritonId = triton::arch::arm::arm32::ID_INS_BKPT;
              break;

            case triton::extlibs::capstone::ARM_INS_BL:
              tritonId = triton::arch::arm::arm32::ID_INS_BL;
              break;

            case triton::extlibs::capstone::ARM_INS_BLX:
              tritonId = triton::arch::arm::arm32::ID_INS_BLX;
              break;

            case triton::extlibs::capstone::ARM_INS_BX:
              tritonId = triton::arch::arm::arm32::ID_INS_BX;
              break;

            case triton::extlibs::capstone::ARM_INS_BXJ:
              tritonId = triton::arch::arm::arm32::ID_INS_BXJ;
              break;

            case triton::extlibs::capstone::ARM_INS_B:
              tritonId = triton::arch::arm::arm32::ID_INS_B;
              break;

            case triton::extlibs::capstone::ARM_INS_CDP:
              tritonId = triton::arch::arm::arm32::ID_INS_CDP;
              break;

            case triton::extlibs::capstone::ARM_INS_CDP2:
              tritonId = triton::arch::arm::arm32::ID_INS_CDP2;
              break;

            case triton::extlibs::capstone::ARM_INS_CLREX:
              tritonId = triton::arch::arm::arm32::ID_INS_CLREX;
              break;

            case triton::extlibs::capstone::ARM_INS_CLZ:
              tritonId = triton::arch::arm::arm32::ID_INS_CLZ;
              break;

            case triton::extlibs::capstone::ARM_INS_CMN:
              tritonId = triton::arch::arm::arm32::ID_INS_CMN;
              break;

            case triton::extlibs::capstone::ARM_INS_CMP:
              tritonId = triton::arch::arm::arm32::ID_INS_CMP;
              break;

            case triton::extlibs::capstone::ARM_INS_CPS:
              tritonId = triton::arch::arm::arm32::ID_INS_CPS;
              break;

            case triton::extlibs::capstone::ARM_INS_CRC32B:
              tritonId = triton::arch::arm::arm32::ID_INS_CRC32B;
              break;

            case triton::extlibs::capstone::ARM_INS_CRC32CB:
              tritonId = triton::arch::arm::arm32::ID_INS_CRC32CB;
              break;

            case triton::extlibs::capstone::ARM_INS_CRC32CH:
              tritonId = triton::arch::arm::arm32::ID_INS_CRC32CH;
              break;

            case triton::extlibs::capstone::ARM_INS_CRC32CW:
              tritonId = triton::arch::arm::arm32::ID_INS_CRC32CW;
              break;

            case triton::extlibs::capstone::ARM_INS_CRC32H:
              tritonId = triton::arch::arm::arm32::ID_INS_CRC32H;
              break;

            case triton::extlibs::capstone::ARM_INS_CRC32W:
              tritonId = triton::arch::arm::arm32::ID_INS_CRC32W;
              break;

            case triton::extlibs::capstone::ARM_INS_DBG:
              tritonId = triton::arch::arm::arm32::ID_INS_DBG;
              break;

            case triton::extlibs::capstone::ARM_INS_DMB:
              tritonId = triton::arch::arm::arm32::ID_INS_DMB;
              break;

            case triton::extlibs::capstone::ARM_INS_DSB:
              tritonId = triton::arch::arm::arm32::ID_INS_DSB;
              break;

            case triton::extlibs::capstone::ARM_INS_EOR:
              tritonId = triton::arch::arm::arm32::ID_INS_EOR;
              break;

            case triton::extlibs::capstone::ARM_INS_ERET:
              tritonId = triton::arch::arm::arm32::ID_INS_ERET;
              break;

            case triton::extlibs::capstone::ARM_INS_VMOV:
              tritonId = triton::arch::arm::arm32::ID_INS_VMOV;
              break;

            case triton::extlibs::capstone::ARM_INS_FLDMDBX:
              tritonId = triton::arch::arm::arm32::ID_INS_FLDMDBX;
              break;

            case triton::extlibs::capstone::ARM_INS_FLDMIAX:
              tritonId = triton::arch::arm::arm32::ID_INS_FLDMIAX;
              break;

            case triton::extlibs::capstone::ARM_INS_VMRS:
              tritonId = triton::arch::arm::arm32::ID_INS_VMRS;
              break;

            case triton::extlibs::capstone::ARM_INS_FSTMDBX:
              tritonId = triton::arch::arm::arm32::ID_INS_FSTMDBX;
              break;

            case triton::extlibs::capstone::ARM_INS_FSTMIAX:
              tritonId = triton::arch::arm::arm32::ID_INS_FSTMIAX;
              break;

            case triton::extlibs::capstone::ARM_INS_HINT:
              tritonId = triton::arch::arm::arm32::ID_INS_HINT;
              break;

            case triton::extlibs::capstone::ARM_INS_HLT:
              tritonId = triton::arch::arm::arm32::ID_INS_HLT;
              break;

            case triton::extlibs::capstone::ARM_INS_HVC:
              tritonId = triton::arch::arm::arm32::ID_INS_HVC;
              break;

            case triton::extlibs::capstone::ARM_INS_ISB:
              tritonId = triton::arch::arm::arm32::ID_INS_ISB;
              break;

            case triton::extlibs::capstone::ARM_INS_LDA:
              tritonId = triton::arch::arm::arm32::ID_INS_LDA;
              break;

            case triton::extlibs::capstone::ARM_INS_LDAB:
              tritonId = triton::arch::arm::arm32::ID_INS_LDAB;
              break;

            case triton::extlibs::capstone::ARM_INS_LDAEX:
              tritonId = triton::arch::arm::arm32::ID_INS_LDAEX;
              break;

            case triton::extlibs::capstone::ARM_INS_LDAEXB:
              tritonId = triton::arch::arm::arm32::ID_INS_LDAEXB;
              break;

            case triton::extlibs::capstone::ARM_INS_LDAEXD:
              tritonId = triton::arch::arm::arm32::ID_INS_LDAEXD;
              break;

            case triton::extlibs::capstone::ARM_INS_LDAEXH:
              tritonId = triton::arch::arm::arm32::ID_INS_LDAEXH;
              break;

            case triton::extlibs::capstone::ARM_INS_LDAH:
              tritonId = triton::arch::arm::arm32::ID_INS_LDAH;
              break;

            case triton::extlibs::capstone::ARM_INS_LDC2L:
              tritonId = triton::arch::arm::arm32::ID_INS_LDC2L;
              break;

            case triton::extlibs::capstone::ARM_INS_LDC2:
              tritonId = triton::arch::arm::arm32::ID_INS_LDC2;
              break;

            case triton::extlibs::capstone::ARM_INS_LDCL:
              tritonId = triton::arch::arm::arm32::ID_INS_LDCL;
              break;

            case triton::extlibs::capstone::ARM_INS_LDC:
              tritonId = triton::arch::arm::arm32::ID_INS_LDC;
              break;

            case triton::extlibs::capstone::ARM_INS_LDMDA:
              tritonId = triton::arch::arm::arm32::ID_INS_LDMDA;
              break;

            case triton::extlibs::capstone::ARM_INS_LDMDB:
              tritonId = triton::arch::arm::arm32::ID_INS_LDMDB;
              break;

            case triton::extlibs::capstone::ARM_INS_LDM:
              tritonId = triton::arch::arm::arm32::ID_INS_LDM;
              break;

            case triton::extlibs::capstone::ARM_INS_LDMIB:
              tritonId = triton::arch::arm::arm32::ID_INS_LDMIB;
              break;

            case triton::extlibs::capstone::ARM_INS_LDRBT:
              tritonId = triton::arch::arm::arm32::ID_INS_LDRBT;
              break;

            case triton::extlibs::capstone::ARM_INS_LDRB:
              tritonId = triton::arch::arm::arm32::ID_INS_LDRB;
              break;

            case triton::extlibs::capstone::ARM_INS_LDRD:
              tritonId = triton::arch::arm::arm32::ID_INS_LDRD;
              break;

            case triton::extlibs::capstone::ARM_INS_LDREX:
              tritonId = triton::arch::arm::arm32::ID_INS_LDREX;
              break;

            case triton::extlibs::capstone::ARM_INS_LDREXB:
              tritonId = triton::arch::arm::arm32::ID_INS_LDREXB;
              break;

            case triton::extlibs::capstone::ARM_INS_LDREXD:
              tritonId = triton::arch::arm::arm32::ID_INS_LDREXD;
              break;

            case triton::extlibs::capstone::ARM_INS_LDREXH:
              tritonId = triton::arch::arm::arm32::ID_INS_LDREXH;
              break;

            case triton::extlibs::capstone::ARM_INS_LDRH:
              tritonId = triton::arch::arm::arm32::ID_INS_LDRH;
              break;

            case triton::extlibs::capstone::ARM_INS_LDRHT:
              tritonId = triton::arch::arm::arm32::ID_INS_LDRHT;
              break;

            case triton::extlibs::capstone::ARM_INS_LDRSB:
              tritonId = triton::arch::arm::arm32::ID_INS_LDRSB;
              break;

            case triton::extlibs::capstone::ARM_INS_LDRSBT:
              tritonId = triton::arch::arm::arm32::ID_INS_LDRSBT;
              break;

            case triton::extlibs::capstone::ARM_INS_LDRSH:
              tritonId = triton::arch::arm::arm32::ID_INS_LDRSH;
              break;

            case triton::extlibs::capstone::ARM_INS_LDRSHT:
              tritonId = triton::arch::arm::arm32::ID_INS_LDRSHT;
              break;

            case triton::extlibs::capstone::ARM_INS_LDRT:
              tritonId = triton::arch::arm::arm32::ID_INS_LDRT;
              break;

            case triton::extlibs::capstone::ARM_INS_LDR:
              tritonId = triton::arch::arm::arm32::ID_INS_LDR;
              break;

            case triton::extlibs::capstone::ARM_INS_MCR:
              tritonId = triton::arch::arm::arm32::ID_INS_MCR;
              break;

            case triton::extlibs::capstone::ARM_INS_MCR2:
              tritonId = triton::arch::arm::arm32::ID_INS_MCR2;
              break;

            case triton::extlibs::capstone::ARM_INS_MCRR:
              tritonId = triton::arch::arm::arm32::ID_INS_MCRR;
              break;

            case triton::extlibs::capstone::ARM_INS_MCRR2:
              tritonId = triton::arch::arm::arm32::ID_INS_MCRR2;
              break;

            case triton::extlibs::capstone::ARM_INS_MLA:
              tritonId = triton::arch::arm::arm32::ID_INS_MLA;
              break;

            case triton::extlibs::capstone::ARM_INS_MLS:
              tritonId = triton::arch::arm::arm32::ID_INS_MLS;
              break;

            case triton::extlibs::capstone::ARM_INS_MOV:
              tritonId = triton::arch::arm::arm32::ID_INS_MOV;
              break;

            #if CS_API_MAJOR >= 5
            case triton::extlibs::capstone::ARM_INS_MOVS:
              tritonId = triton::arch::arm::arm32::ID_INS_MOV;
              break;
            #endif

            case triton::extlibs::capstone::ARM_INS_MOVT:
              tritonId = triton::arch::arm::arm32::ID_INS_MOVT;
              break;

            case triton::extlibs::capstone::ARM_INS_MOVW:
              tritonId = triton::arch::arm::arm32::ID_INS_MOVW;
              break;

            case triton::extlibs::capstone::ARM_INS_MRC:
              tritonId = triton::arch::arm::arm32::ID_INS_MRC;
              break;

            case triton::extlibs::capstone::ARM_INS_MRC2:
              tritonId = triton::arch::arm::arm32::ID_INS_MRC2;
              break;

            case triton::extlibs::capstone::ARM_INS_MRRC:
              tritonId = triton::arch::arm::arm32::ID_INS_MRRC;
              break;

            case triton::extlibs::capstone::ARM_INS_MRRC2:
              tritonId = triton::arch::arm::arm32::ID_INS_MRRC2;
              break;

            case triton::extlibs::capstone::ARM_INS_MRS:
              tritonId = triton::arch::arm::arm32::ID_INS_MRS;
              break;

            case triton::extlibs::capstone::ARM_INS_MSR:
              tritonId = triton::arch::arm::arm32::ID_INS_MSR;
              break;

            case triton::extlibs::capstone::ARM_INS_MUL:
              tritonId = triton::arch::arm::arm32::ID_INS_MUL;
              break;

            case triton::extlibs::capstone::ARM_INS_MVN:
              tritonId = triton::arch::arm::arm32::ID_INS_MVN;
              break;

            case triton::extlibs::capstone::ARM_INS_ORR:
              tritonId = triton::arch::arm::arm32::ID_INS_ORR;
              break;

            case triton::extlibs::capstone::ARM_INS_PKHBT:
              tritonId = triton::arch::arm::arm32::ID_INS_PKHBT;
              break;

            case triton::extlibs::capstone::ARM_INS_PKHTB:
              tritonId = triton::arch::arm::arm32::ID_INS_PKHTB;
              break;

            case triton::extlibs::capstone::ARM_INS_PLDW:
              tritonId = triton::arch::arm::arm32::ID_INS_PLDW;
              break;

            case triton::extlibs::capstone::ARM_INS_PLD:
              tritonId = triton::arch::arm::arm32::ID_INS_PLD;
              break;

            case triton::extlibs::capstone::ARM_INS_PLI:
              tritonId = triton::arch::arm::arm32::ID_INS_PLI;
              break;

            case triton::extlibs::capstone::ARM_INS_QADD:
              tritonId = triton::arch::arm::arm32::ID_INS_QADD;
              break;

            case triton::extlibs::capstone::ARM_INS_QADD16:
              tritonId = triton::arch::arm::arm32::ID_INS_QADD16;
              break;

            case triton::extlibs::capstone::ARM_INS_QADD8:
              tritonId = triton::arch::arm::arm32::ID_INS_QADD8;
              break;

            case triton::extlibs::capstone::ARM_INS_QASX:
              tritonId = triton::arch::arm::arm32::ID_INS_QASX;
              break;

            case triton::extlibs::capstone::ARM_INS_QDADD:
              tritonId = triton::arch::arm::arm32::ID_INS_QDADD;
              break;

            case triton::extlibs::capstone::ARM_INS_QDSUB:
              tritonId = triton::arch::arm::arm32::ID_INS_QDSUB;
              break;

            case triton::extlibs::capstone::ARM_INS_QSAX:
              tritonId = triton::arch::arm::arm32::ID_INS_QSAX;
              break;

            case triton::extlibs::capstone::ARM_INS_QSUB:
              tritonId = triton::arch::arm::arm32::ID_INS_QSUB;
              break;

            case triton::extlibs::capstone::ARM_INS_QSUB16:
              tritonId = triton::arch::arm::arm32::ID_INS_QSUB16;
              break;

            case triton::extlibs::capstone::ARM_INS_QSUB8:
              tritonId = triton::arch::arm::arm32::ID_INS_QSUB8;
              break;

            case triton::extlibs::capstone::ARM_INS_RBIT:
              tritonId = triton::arch::arm::arm32::ID_INS_RBIT;
              break;

            case triton::extlibs::capstone::ARM_INS_REV:
              tritonId = triton::arch::arm::arm32::ID_INS_REV;
              break;

            case triton::extlibs::capstone::ARM_INS_REV16:
              tritonId = triton::arch::arm::arm32::ID_INS_REV16;
              break;

            case triton::extlibs::capstone::ARM_INS_REVSH:
              tritonId = triton::arch::arm::arm32::ID_INS_REVSH;
              break;

            case triton::extlibs::capstone::ARM_INS_RFEDA:
              tritonId = triton::arch::arm::arm32::ID_INS_RFEDA;
              break;

            case triton::extlibs::capstone::ARM_INS_RFEDB:
              tritonId = triton::arch::arm::arm32::ID_INS_RFEDB;
              break;

            case triton::extlibs::capstone::ARM_INS_RFEIA:
              tritonId = triton::arch::arm::arm32::ID_INS_RFEIA;
              break;

            case triton::extlibs::capstone::ARM_INS_RFEIB:
              tritonId = triton::arch::arm::arm32::ID_INS_RFEIB;
              break;

            case triton::extlibs::capstone::ARM_INS_RSB:
              tritonId = triton::arch::arm::arm32::ID_INS_RSB;
              break;

            case triton::extlibs::capstone::ARM_INS_RSC:
              tritonId = triton::arch::arm::arm32::ID_INS_RSC;
              break;

            case triton::extlibs::capstone::ARM_INS_SADD16:
              tritonId = triton::arch::arm::arm32::ID_INS_SADD16;
              break;

            case triton::extlibs::capstone::ARM_INS_SADD8:
              tritonId = triton::arch::arm::arm32::ID_INS_SADD8;
              break;

            case triton::extlibs::capstone::ARM_INS_SASX:
              tritonId = triton::arch::arm::arm32::ID_INS_SASX;
              break;

            case triton::extlibs::capstone::ARM_INS_SBC:
              tritonId = triton::arch::arm::arm32::ID_INS_SBC;
              break;

            case triton::extlibs::capstone::ARM_INS_SBFX:
              tritonId = triton::arch::arm::arm32::ID_INS_SBFX;
              break;

            case triton::extlibs::capstone::ARM_INS_SDIV:
              tritonId = triton::arch::arm::arm32::ID_INS_SDIV;
              break;

            case triton::extlibs::capstone::ARM_INS_SEL:
              tritonId = triton::arch::arm::arm32::ID_INS_SEL;
              break;

            case triton::extlibs::capstone::ARM_INS_SETEND:
              tritonId = triton::arch::arm::arm32::ID_INS_SETEND;
              break;

            case triton::extlibs::capstone::ARM_INS_SHA1C:
              tritonId = triton::arch::arm::arm32::ID_INS_SHA1C;
              break;

            case triton::extlibs::capstone::ARM_INS_SHA1H:
              tritonId = triton::arch::arm::arm32::ID_INS_SHA1H;
              break;

            case triton::extlibs::capstone::ARM_INS_SHA1M:
              tritonId = triton::arch::arm::arm32::ID_INS_SHA1M;
              break;

            case triton::extlibs::capstone::ARM_INS_SHA1P:
              tritonId = triton::arch::arm::arm32::ID_INS_SHA1P;
              break;

            case triton::extlibs::capstone::ARM_INS_SHA1SU0:
              tritonId = triton::arch::arm::arm32::ID_INS_SHA1SU0;
              break;

            case triton::extlibs::capstone::ARM_INS_SHA1SU1:
              tritonId = triton::arch::arm::arm32::ID_INS_SHA1SU1;
              break;

            case triton::extlibs::capstone::ARM_INS_SHA256H:
              tritonId = triton::arch::arm::arm32::ID_INS_SHA256H;
              break;

            case triton::extlibs::capstone::ARM_INS_SHA256H2:
              tritonId = triton::arch::arm::arm32::ID_INS_SHA256H2;
              break;

            case triton::extlibs::capstone::ARM_INS_SHA256SU0:
              tritonId = triton::arch::arm::arm32::ID_INS_SHA256SU0;
              break;

            case triton::extlibs::capstone::ARM_INS_SHA256SU1:
              tritonId = triton::arch::arm::arm32::ID_INS_SHA256SU1;
              break;

            case triton::extlibs::capstone::ARM_INS_SHADD16:
              tritonId = triton::arch::arm::arm32::ID_INS_SHADD16;
              break;

            case triton::extlibs::capstone::ARM_INS_SHADD8:
              tritonId = triton::arch::arm::arm32::ID_INS_SHADD8;
              break;

            case triton::extlibs::capstone::ARM_INS_SHASX:
              tritonId = triton::arch::arm::arm32::ID_INS_SHASX;
              break;

            case triton::extlibs::capstone::ARM_INS_SHSAX:
              tritonId = triton::arch::arm::arm32::ID_INS_SHSAX;
              break;

            case triton::extlibs::capstone::ARM_INS_SHSUB16:
              tritonId = triton::arch::arm::arm32::ID_INS_SHSUB16;
              break;

            case triton::extlibs::capstone::ARM_INS_SHSUB8:
              tritonId = triton::arch::arm::arm32::ID_INS_SHSUB8;
              break;

            case triton::extlibs::capstone::ARM_INS_SMC:
              tritonId = triton::arch::arm::arm32::ID_INS_SMC;
              break;

            case triton::extlibs::capstone::ARM_INS_SMLABB:
              tritonId = triton::arch::arm::arm32::ID_INS_SMLABB;
              break;

            case triton::extlibs::capstone::ARM_INS_SMLABT:
              tritonId = triton::arch::arm::arm32::ID_INS_SMLABT;
              break;

            case triton::extlibs::capstone::ARM_INS_SMLAD:
              tritonId = triton::arch::arm::arm32::ID_INS_SMLAD;
              break;

            case triton::extlibs::capstone::ARM_INS_SMLADX:
              tritonId = triton::arch::arm::arm32::ID_INS_SMLADX;
              break;

            case triton::extlibs::capstone::ARM_INS_SMLAL:
              tritonId = triton::arch::arm::arm32::ID_INS_SMLAL;
              break;

            case triton::extlibs::capstone::ARM_INS_SMLALBB:
              tritonId = triton::arch::arm::arm32::ID_INS_SMLALBB;
              break;

            case triton::extlibs::capstone::ARM_INS_SMLALBT:
              tritonId = triton::arch::arm::arm32::ID_INS_SMLALBT;
              break;

            case triton::extlibs::capstone::ARM_INS_SMLALD:
              tritonId = triton::arch::arm::arm32::ID_INS_SMLALD;
              break;

            case triton::extlibs::capstone::ARM_INS_SMLALDX:
              tritonId = triton::arch::arm::arm32::ID_INS_SMLALDX;
              break;

            case triton::extlibs::capstone::ARM_INS_SMLALTB:
              tritonId = triton::arch::arm::arm32::ID_INS_SMLALTB;
              break;

            case triton::extlibs::capstone::ARM_INS_SMLALTT:
              tritonId = triton::arch::arm::arm32::ID_INS_SMLALTT;
              break;

            case triton::extlibs::capstone::ARM_INS_SMLATB:
              tritonId = triton::arch::arm::arm32::ID_INS_SMLATB;
              break;

            case triton::extlibs::capstone::ARM_INS_SMLATT:
              tritonId = triton::arch::arm::arm32::ID_INS_SMLATT;
              break;

            case triton::extlibs::capstone::ARM_INS_SMLAWB:
              tritonId = triton::arch::arm::arm32::ID_INS_SMLAWB;
              break;

            case triton::extlibs::capstone::ARM_INS_SMLAWT:
              tritonId = triton::arch::arm::arm32::ID_INS_SMLAWT;
              break;

            case triton::extlibs::capstone::ARM_INS_SMLSD:
              tritonId = triton::arch::arm::arm32::ID_INS_SMLSD;
              break;

            case triton::extlibs::capstone::ARM_INS_SMLSDX:
              tritonId = triton::arch::arm::arm32::ID_INS_SMLSDX;
              break;

            case triton::extlibs::capstone::ARM_INS_SMLSLD:
              tritonId = triton::arch::arm::arm32::ID_INS_SMLSLD;
              break;

            case triton::extlibs::capstone::ARM_INS_SMLSLDX:
              tritonId = triton::arch::arm::arm32::ID_INS_SMLSLDX;
              break;

            case triton::extlibs::capstone::ARM_INS_SMMLA:
              tritonId = triton::arch::arm::arm32::ID_INS_SMMLA;
              break;

            case triton::extlibs::capstone::ARM_INS_SMMLAR:
              tritonId = triton::arch::arm::arm32::ID_INS_SMMLAR;
              break;

            case triton::extlibs::capstone::ARM_INS_SMMLS:
              tritonId = triton::arch::arm::arm32::ID_INS_SMMLS;
              break;

            case triton::extlibs::capstone::ARM_INS_SMMLSR:
              tritonId = triton::arch::arm::arm32::ID_INS_SMMLSR;
              break;

            case triton::extlibs::capstone::ARM_INS_SMMUL:
              tritonId = triton::arch::arm::arm32::ID_INS_SMMUL;
              break;

            case triton::extlibs::capstone::ARM_INS_SMMULR:
              tritonId = triton::arch::arm::arm32::ID_INS_SMMULR;
              break;

            case triton::extlibs::capstone::ARM_INS_SMUAD:
              tritonId = triton::arch::arm::arm32::ID_INS_SMUAD;
              break;

            case triton::extlibs::capstone::ARM_INS_SMUADX:
              tritonId = triton::arch::arm::arm32::ID_INS_SMUADX;
              break;

            case triton::extlibs::capstone::ARM_INS_SMULBB:
              tritonId = triton::arch::arm::arm32::ID_INS_SMULBB;
              break;

            case triton::extlibs::capstone::ARM_INS_SMULBT:
              tritonId = triton::arch::arm::arm32::ID_INS_SMULBT;
              break;

            case triton::extlibs::capstone::ARM_INS_SMULL:
              tritonId = triton::arch::arm::arm32::ID_INS_SMULL;
              break;

            case triton::extlibs::capstone::ARM_INS_SMULTB:
              tritonId = triton::arch::arm::arm32::ID_INS_SMULTB;
              break;

            case triton::extlibs::capstone::ARM_INS_SMULTT:
              tritonId = triton::arch::arm::arm32::ID_INS_SMULTT;
              break;

            case triton::extlibs::capstone::ARM_INS_SMULWB:
              tritonId = triton::arch::arm::arm32::ID_INS_SMULWB;
              break;

            case triton::extlibs::capstone::ARM_INS_SMULWT:
              tritonId = triton::arch::arm::arm32::ID_INS_SMULWT;
              break;

            case triton::extlibs::capstone::ARM_INS_SMUSD:
              tritonId = triton::arch::arm::arm32::ID_INS_SMUSD;
              break;

            case triton::extlibs::capstone::ARM_INS_SMUSDX:
              tritonId = triton::arch::arm::arm32::ID_INS_SMUSDX;
              break;

            case triton::extlibs::capstone::ARM_INS_SRSDA:
              tritonId = triton::arch::arm::arm32::ID_INS_SRSDA;
              break;

            case triton::extlibs::capstone::ARM_INS_SRSDB:
              tritonId = triton::arch::arm::arm32::ID_INS_SRSDB;
              break;

            case triton::extlibs::capstone::ARM_INS_SRSIA:
              tritonId = triton::arch::arm::arm32::ID_INS_SRSIA;
              break;

            case triton::extlibs::capstone::ARM_INS_SRSIB:
              tritonId = triton::arch::arm::arm32::ID_INS_SRSIB;
              break;

            case triton::extlibs::capstone::ARM_INS_SSAT:
              tritonId = triton::arch::arm::arm32::ID_INS_SSAT;
              break;

            case triton::extlibs::capstone::ARM_INS_SSAT16:
              tritonId = triton::arch::arm::arm32::ID_INS_SSAT16;
              break;

            case triton::extlibs::capstone::ARM_INS_SSAX:
              tritonId = triton::arch::arm::arm32::ID_INS_SSAX;
              break;

            case triton::extlibs::capstone::ARM_INS_SSUB16:
              tritonId = triton::arch::arm::arm32::ID_INS_SSUB16;
              break;

            case triton::extlibs::capstone::ARM_INS_SSUB8:
              tritonId = triton::arch::arm::arm32::ID_INS_SSUB8;
              break;

            case triton::extlibs::capstone::ARM_INS_STC2L:
              tritonId = triton::arch::arm::arm32::ID_INS_STC2L;
              break;

            case triton::extlibs::capstone::ARM_INS_STC2:
              tritonId = triton::arch::arm::arm32::ID_INS_STC2;
              break;

            case triton::extlibs::capstone::ARM_INS_STCL:
              tritonId = triton::arch::arm::arm32::ID_INS_STCL;
              break;

            case triton::extlibs::capstone::ARM_INS_STC:
              tritonId = triton::arch::arm::arm32::ID_INS_STC;
              break;

            case triton::extlibs::capstone::ARM_INS_STL:
              tritonId = triton::arch::arm::arm32::ID_INS_STL;
              break;

            case triton::extlibs::capstone::ARM_INS_STLB:
              tritonId = triton::arch::arm::arm32::ID_INS_STLB;
              break;

            case triton::extlibs::capstone::ARM_INS_STLEX:
              tritonId = triton::arch::arm::arm32::ID_INS_STLEX;
              break;

            case triton::extlibs::capstone::ARM_INS_STLEXB:
              tritonId = triton::arch::arm::arm32::ID_INS_STLEXB;
              break;

            case triton::extlibs::capstone::ARM_INS_STLEXD:
              tritonId = triton::arch::arm::arm32::ID_INS_STLEXD;
              break;

            case triton::extlibs::capstone::ARM_INS_STLEXH:
              tritonId = triton::arch::arm::arm32::ID_INS_STLEXH;
              break;

            case triton::extlibs::capstone::ARM_INS_STLH:
              tritonId = triton::arch::arm::arm32::ID_INS_STLH;
              break;

            case triton::extlibs::capstone::ARM_INS_STMDA:
              tritonId = triton::arch::arm::arm32::ID_INS_STMDA;
              break;

            case triton::extlibs::capstone::ARM_INS_STMDB:
              tritonId = triton::arch::arm::arm32::ID_INS_STMDB;
              break;

            case triton::extlibs::capstone::ARM_INS_STM:
              tritonId = triton::arch::arm::arm32::ID_INS_STM;
              break;

            case triton::extlibs::capstone::ARM_INS_STMIB:
              tritonId = triton::arch::arm::arm32::ID_INS_STMIB;
              break;

            case triton::extlibs::capstone::ARM_INS_STRBT:
              tritonId = triton::arch::arm::arm32::ID_INS_STRBT;
              break;

            case triton::extlibs::capstone::ARM_INS_STRB:
              tritonId = triton::arch::arm::arm32::ID_INS_STRB;
              break;

            case triton::extlibs::capstone::ARM_INS_STRD:
              tritonId = triton::arch::arm::arm32::ID_INS_STRD;
              break;

            case triton::extlibs::capstone::ARM_INS_STREX:
              tritonId = triton::arch::arm::arm32::ID_INS_STREX;
              break;

            case triton::extlibs::capstone::ARM_INS_STREXB:
              tritonId = triton::arch::arm::arm32::ID_INS_STREXB;
              break;

            case triton::extlibs::capstone::ARM_INS_STREXD:
              tritonId = triton::arch::arm::arm32::ID_INS_STREXD;
              break;

            case triton::extlibs::capstone::ARM_INS_STREXH:
              tritonId = triton::arch::arm::arm32::ID_INS_STREXH;
              break;

            case triton::extlibs::capstone::ARM_INS_STRH:
              tritonId = triton::arch::arm::arm32::ID_INS_STRH;
              break;

            case triton::extlibs::capstone::ARM_INS_STRHT:
              tritonId = triton::arch::arm::arm32::ID_INS_STRHT;
              break;

            case triton::extlibs::capstone::ARM_INS_STRT:
              tritonId = triton::arch::arm::arm32::ID_INS_STRT;
              break;

            case triton::extlibs::capstone::ARM_INS_STR:
              tritonId = triton::arch::arm::arm32::ID_INS_STR;
              break;

            case triton::extlibs::capstone::ARM_INS_SUB:
              tritonId = triton::arch::arm::arm32::ID_INS_SUB;
              break;

            case triton::extlibs::capstone::ARM_INS_SVC:
              tritonId = triton::arch::arm::arm32::ID_INS_SVC;
              break;

            case triton::extlibs::capstone::ARM_INS_SWP:
              tritonId = triton::arch::arm::arm32::ID_INS_SWP;
              break;

            case triton::extlibs::capstone::ARM_INS_SWPB:
              tritonId = triton::arch::arm::arm32::ID_INS_SWPB;
              break;

            case triton::extlibs::capstone::ARM_INS_SXTAB:
              tritonId = triton::arch::arm::arm32::ID_INS_SXTAB;
              break;

            case triton::extlibs::capstone::ARM_INS_SXTAB16:
              tritonId = triton::arch::arm::arm32::ID_INS_SXTAB16;
              break;

            case triton::extlibs::capstone::ARM_INS_SXTAH:
              tritonId = triton::arch::arm::arm32::ID_INS_SXTAH;
              break;

            case triton::extlibs::capstone::ARM_INS_SXTB:
              tritonId = triton::arch::arm::arm32::ID_INS_SXTB;
              break;

            case triton::extlibs::capstone::ARM_INS_SXTB16:
              tritonId = triton::arch::arm::arm32::ID_INS_SXTB16;
              break;

            case triton::extlibs::capstone::ARM_INS_SXTH:
              tritonId = triton::arch::arm::arm32::ID_INS_SXTH;
              break;

            case triton::extlibs::capstone::ARM_INS_TEQ:
              tritonId = triton::arch::arm::arm32::ID_INS_TEQ;
              break;

            case triton::extlibs::capstone::ARM_INS_TRAP:
              tritonId = triton::arch::arm::arm32::ID_INS_TRAP;
              break;

            case triton::extlibs::capstone::ARM_INS_TST:
              tritonId = triton::arch::arm::arm32::ID_INS_TST;
              break;

            case triton::extlibs::capstone::ARM_INS_UADD16:
              tritonId = triton::arch::arm::arm32::ID_INS_UADD16;
              break;

            case triton::extlibs::capstone::ARM_INS_UADD8:
              tritonId = triton::arch::arm::arm32::ID_INS_UADD8;
              break;

            case triton::extlibs::capstone::ARM_INS_UASX:
              tritonId = triton::arch::arm::arm32::ID_INS_UASX;
              break;

            case triton::extlibs::capstone::ARM_INS_UBFX:
              tritonId = triton::arch::arm::arm32::ID_INS_UBFX;
              break;

            case triton::extlibs::capstone::ARM_INS_UDF:
              tritonId = triton::arch::arm::arm32::ID_INS_UDF;
              break;

            case triton::extlibs::capstone::ARM_INS_UDIV:
              tritonId = triton::arch::arm::arm32::ID_INS_UDIV;
              break;

            case triton::extlibs::capstone::ARM_INS_UHADD16:
              tritonId = triton::arch::arm::arm32::ID_INS_UHADD16;
              break;

            case triton::extlibs::capstone::ARM_INS_UHADD8:
              tritonId = triton::arch::arm::arm32::ID_INS_UHADD8;
              break;

            case triton::extlibs::capstone::ARM_INS_UHASX:
              tritonId = triton::arch::arm::arm32::ID_INS_UHASX;
              break;

            case triton::extlibs::capstone::ARM_INS_UHSAX:
              tritonId = triton::arch::arm::arm32::ID_INS_UHSAX;
              break;

            case triton::extlibs::capstone::ARM_INS_UHSUB16:
              tritonId = triton::arch::arm::arm32::ID_INS_UHSUB16;
              break;

            case triton::extlibs::capstone::ARM_INS_UHSUB8:
              tritonId = triton::arch::arm::arm32::ID_INS_UHSUB8;
              break;

            case triton::extlibs::capstone::ARM_INS_UMAAL:
              tritonId = triton::arch::arm::arm32::ID_INS_UMAAL;
              break;

            case triton::extlibs::capstone::ARM_INS_UMLAL:
              tritonId = triton::arch::arm::arm32::ID_INS_UMLAL;
              break;

            case triton::extlibs::capstone::ARM_INS_UMULL:
              tritonId = triton::arch::arm::arm32::ID_INS_UMULL;
              break;

            case triton::extlibs::capstone::ARM_INS_UQADD16:
              tritonId = triton::arch::arm::arm32::ID_INS_UQADD16;
              break;

            case triton::extlibs::capstone::ARM_INS_UQADD8:
              tritonId = triton::arch::arm::arm32::ID_INS_UQADD8;
              break;

            case triton::extlibs::capstone::ARM_INS_UQASX:
              tritonId = triton::arch::arm::arm32::ID_INS_UQASX;
              break;

            case triton::extlibs::capstone::ARM_INS_UQSAX:
              tritonId = triton::arch::arm::arm32::ID_INS_UQSAX;
              break;

            case triton::extlibs::capstone::ARM_INS_UQSUB16:
              tritonId = triton::arch::arm::arm32::ID_INS_UQSUB16;
              break;

            case triton::extlibs::capstone::ARM_INS_UQSUB8:
              tritonId = triton::arch::arm::arm32::ID_INS_UQSUB8;
              break;

            case triton::extlibs::capstone::ARM_INS_USAD8:
              tritonId = triton::arch::arm::arm32::ID_INS_USAD8;
              break;

            case triton::extlibs::capstone::ARM_INS_USADA8:
              tritonId = triton::arch::arm::arm32::ID_INS_USADA8;
              break;

            case triton::extlibs::capstone::ARM_INS_USAT:
              tritonId = triton::arch::arm::arm32::ID_INS_USAT;
              break;

            case triton::extlibs::capstone::ARM_INS_USAT16:
              tritonId = triton::arch::arm::arm32::ID_INS_USAT16;
              break;

            case triton::extlibs::capstone::ARM_INS_USAX:
              tritonId = triton::arch::arm::arm32::ID_INS_USAX;
              break;

            case triton::extlibs::capstone::ARM_INS_USUB16:
              tritonId = triton::arch::arm::arm32::ID_INS_USUB16;
              break;

            case triton::extlibs::capstone::ARM_INS_USUB8:
              tritonId = triton::arch::arm::arm32::ID_INS_USUB8;
              break;

            case triton::extlibs::capstone::ARM_INS_UXTAB:
              tritonId = triton::arch::arm::arm32::ID_INS_UXTAB;
              break;

            case triton::extlibs::capstone::ARM_INS_UXTAB16:
              tritonId = triton::arch::arm::arm32::ID_INS_UXTAB16;
              break;

            case triton::extlibs::capstone::ARM_INS_UXTAH:
              tritonId = triton::arch::arm::arm32::ID_INS_UXTAH;
              break;

            case triton::extlibs::capstone::ARM_INS_UXTB:
              tritonId = triton::arch::arm::arm32::ID_INS_UXTB;
              break;

            case triton::extlibs::capstone::ARM_INS_UXTB16:
              tritonId = triton::arch::arm::arm32::ID_INS_UXTB16;
              break;

            case triton::extlibs::capstone::ARM_INS_UXTH:
              tritonId = triton::arch::arm::arm32::ID_INS_UXTH;
              break;

            case triton::extlibs::capstone::ARM_INS_VABAL:
              tritonId = triton::arch::arm::arm32::ID_INS_VABAL;
              break;

            case triton::extlibs::capstone::ARM_INS_VABA:
              tritonId = triton::arch::arm::arm32::ID_INS_VABA;
              break;

            case triton::extlibs::capstone::ARM_INS_VABDL:
              tritonId = triton::arch::arm::arm32::ID_INS_VABDL;
              break;

            case triton::extlibs::capstone::ARM_INS_VABD:
              tritonId = triton::arch::arm::arm32::ID_INS_VABD;
              break;

            case triton::extlibs::capstone::ARM_INS_VABS:
              tritonId = triton::arch::arm::arm32::ID_INS_VABS;
              break;

            case triton::extlibs::capstone::ARM_INS_VACGE:
              tritonId = triton::arch::arm::arm32::ID_INS_VACGE;
              break;

            case triton::extlibs::capstone::ARM_INS_VACGT:
              tritonId = triton::arch::arm::arm32::ID_INS_VACGT;
              break;

            case triton::extlibs::capstone::ARM_INS_VADD:
              tritonId = triton::arch::arm::arm32::ID_INS_VADD;
              break;

            case triton::extlibs::capstone::ARM_INS_VADDHN:
              tritonId = triton::arch::arm::arm32::ID_INS_VADDHN;
              break;

            case triton::extlibs::capstone::ARM_INS_VADDL:
              tritonId = triton::arch::arm::arm32::ID_INS_VADDL;
              break;

            case triton::extlibs::capstone::ARM_INS_VADDW:
              tritonId = triton::arch::arm::arm32::ID_INS_VADDW;
              break;

            case triton::extlibs::capstone::ARM_INS_VAND:
              tritonId = triton::arch::arm::arm32::ID_INS_VAND;
              break;

            case triton::extlibs::capstone::ARM_INS_VBIC:
              tritonId = triton::arch::arm::arm32::ID_INS_VBIC;
              break;

            case triton::extlibs::capstone::ARM_INS_VBIF:
              tritonId = triton::arch::arm::arm32::ID_INS_VBIF;
              break;

            case triton::extlibs::capstone::ARM_INS_VBIT:
              tritonId = triton::arch::arm::arm32::ID_INS_VBIT;
              break;

            case triton::extlibs::capstone::ARM_INS_VBSL:
              tritonId = triton::arch::arm::arm32::ID_INS_VBSL;
              break;

            case triton::extlibs::capstone::ARM_INS_VCEQ:
              tritonId = triton::arch::arm::arm32::ID_INS_VCEQ;
              break;

            case triton::extlibs::capstone::ARM_INS_VCGE:
              tritonId = triton::arch::arm::arm32::ID_INS_VCGE;
              break;

            case triton::extlibs::capstone::ARM_INS_VCGT:
              tritonId = triton::arch::arm::arm32::ID_INS_VCGT;
              break;

            case triton::extlibs::capstone::ARM_INS_VCLE:
              tritonId = triton::arch::arm::arm32::ID_INS_VCLE;
              break;

            case triton::extlibs::capstone::ARM_INS_VCLS:
              tritonId = triton::arch::arm::arm32::ID_INS_VCLS;
              break;

            case triton::extlibs::capstone::ARM_INS_VCLT:
              tritonId = triton::arch::arm::arm32::ID_INS_VCLT;
              break;

            case triton::extlibs::capstone::ARM_INS_VCLZ:
              tritonId = triton::arch::arm::arm32::ID_INS_VCLZ;
              break;

            case triton::extlibs::capstone::ARM_INS_VCMP:
              tritonId = triton::arch::arm::arm32::ID_INS_VCMP;
              break;

            case triton::extlibs::capstone::ARM_INS_VCMPE:
              tritonId = triton::arch::arm::arm32::ID_INS_VCMPE;
              break;

            case triton::extlibs::capstone::ARM_INS_VCNT:
              tritonId = triton::arch::arm::arm32::ID_INS_VCNT;
              break;

            case triton::extlibs::capstone::ARM_INS_VCVTA:
              tritonId = triton::arch::arm::arm32::ID_INS_VCVTA;
              break;

            case triton::extlibs::capstone::ARM_INS_VCVTB:
              tritonId = triton::arch::arm::arm32::ID_INS_VCVTB;
              break;

            case triton::extlibs::capstone::ARM_INS_VCVT:
              tritonId = triton::arch::arm::arm32::ID_INS_VCVT;
              break;

            case triton::extlibs::capstone::ARM_INS_VCVTM:
              tritonId = triton::arch::arm::arm32::ID_INS_VCVTM;
              break;

            case triton::extlibs::capstone::ARM_INS_VCVTN:
              tritonId = triton::arch::arm::arm32::ID_INS_VCVTN;
              break;

            case triton::extlibs::capstone::ARM_INS_VCVTP:
              tritonId = triton::arch::arm::arm32::ID_INS_VCVTP;
              break;

            case triton::extlibs::capstone::ARM_INS_VCVTT:
              tritonId = triton::arch::arm::arm32::ID_INS_VCVTT;
              break;

            case triton::extlibs::capstone::ARM_INS_VDIV:
              tritonId = triton::arch::arm::arm32::ID_INS_VDIV;
              break;

            case triton::extlibs::capstone::ARM_INS_VDUP:
              tritonId = triton::arch::arm::arm32::ID_INS_VDUP;
              break;

            case triton::extlibs::capstone::ARM_INS_VEOR:
              tritonId = triton::arch::arm::arm32::ID_INS_VEOR;
              break;

            case triton::extlibs::capstone::ARM_INS_VEXT:
              tritonId = triton::arch::arm::arm32::ID_INS_VEXT;
              break;

            case triton::extlibs::capstone::ARM_INS_VFMA:
              tritonId = triton::arch::arm::arm32::ID_INS_VFMA;
              break;

            case triton::extlibs::capstone::ARM_INS_VFMS:
              tritonId = triton::arch::arm::arm32::ID_INS_VFMS;
              break;

            case triton::extlibs::capstone::ARM_INS_VFNMA:
              tritonId = triton::arch::arm::arm32::ID_INS_VFNMA;
              break;

            case triton::extlibs::capstone::ARM_INS_VFNMS:
              tritonId = triton::arch::arm::arm32::ID_INS_VFNMS;
              break;

            case triton::extlibs::capstone::ARM_INS_VHADD:
              tritonId = triton::arch::arm::arm32::ID_INS_VHADD;
              break;

            case triton::extlibs::capstone::ARM_INS_VHSUB:
              tritonId = triton::arch::arm::arm32::ID_INS_VHSUB;
              break;

            case triton::extlibs::capstone::ARM_INS_VLD1:
              tritonId = triton::arch::arm::arm32::ID_INS_VLD1;
              break;

            case triton::extlibs::capstone::ARM_INS_VLD2:
              tritonId = triton::arch::arm::arm32::ID_INS_VLD2;
              break;

            case triton::extlibs::capstone::ARM_INS_VLD3:
              tritonId = triton::arch::arm::arm32::ID_INS_VLD3;
              break;

            case triton::extlibs::capstone::ARM_INS_VLD4:
              tritonId = triton::arch::arm::arm32::ID_INS_VLD4;
              break;

            case triton::extlibs::capstone::ARM_INS_VLDMDB:
              tritonId = triton::arch::arm::arm32::ID_INS_VLDMDB;
              break;

            case triton::extlibs::capstone::ARM_INS_VLDMIA:
              tritonId = triton::arch::arm::arm32::ID_INS_VLDMIA;
              break;

            case triton::extlibs::capstone::ARM_INS_VLDR:
              tritonId = triton::arch::arm::arm32::ID_INS_VLDR;
              break;

            case triton::extlibs::capstone::ARM_INS_VMAXNM:
              tritonId = triton::arch::arm::arm32::ID_INS_VMAXNM;
              break;

            case triton::extlibs::capstone::ARM_INS_VMAX:
              tritonId = triton::arch::arm::arm32::ID_INS_VMAX;
              break;

            case triton::extlibs::capstone::ARM_INS_VMINNM:
              tritonId = triton::arch::arm::arm32::ID_INS_VMINNM;
              break;

            case triton::extlibs::capstone::ARM_INS_VMIN:
              tritonId = triton::arch::arm::arm32::ID_INS_VMIN;
              break;

            case triton::extlibs::capstone::ARM_INS_VMLA:
              tritonId = triton::arch::arm::arm32::ID_INS_VMLA;
              break;

            case triton::extlibs::capstone::ARM_INS_VMLAL:
              tritonId = triton::arch::arm::arm32::ID_INS_VMLAL;
              break;

            case triton::extlibs::capstone::ARM_INS_VMLS:
              tritonId = triton::arch::arm::arm32::ID_INS_VMLS;
              break;

            case triton::extlibs::capstone::ARM_INS_VMLSL:
              tritonId = triton::arch::arm::arm32::ID_INS_VMLSL;
              break;

            case triton::extlibs::capstone::ARM_INS_VMOVL:
              tritonId = triton::arch::arm::arm32::ID_INS_VMOVL;
              break;

            case triton::extlibs::capstone::ARM_INS_VMOVN:
              tritonId = triton::arch::arm::arm32::ID_INS_VMOVN;
              break;

            case triton::extlibs::capstone::ARM_INS_VMSR:
              tritonId = triton::arch::arm::arm32::ID_INS_VMSR;
              break;

            case triton::extlibs::capstone::ARM_INS_VMUL:
              tritonId = triton::arch::arm::arm32::ID_INS_VMUL;
              break;

            case triton::extlibs::capstone::ARM_INS_VMULL:
              tritonId = triton::arch::arm::arm32::ID_INS_VMULL;
              break;

            case triton::extlibs::capstone::ARM_INS_VMVN:
              tritonId = triton::arch::arm::arm32::ID_INS_VMVN;
              break;

            case triton::extlibs::capstone::ARM_INS_VNEG:
              tritonId = triton::arch::arm::arm32::ID_INS_VNEG;
              break;

            case triton::extlibs::capstone::ARM_INS_VNMLA:
              tritonId = triton::arch::arm::arm32::ID_INS_VNMLA;
              break;

            case triton::extlibs::capstone::ARM_INS_VNMLS:
              tritonId = triton::arch::arm::arm32::ID_INS_VNMLS;
              break;

            case triton::extlibs::capstone::ARM_INS_VNMUL:
              tritonId = triton::arch::arm::arm32::ID_INS_VNMUL;
              break;

            case triton::extlibs::capstone::ARM_INS_VORN:
              tritonId = triton::arch::arm::arm32::ID_INS_VORN;
              break;

            case triton::extlibs::capstone::ARM_INS_VORR:
              tritonId = triton::arch::arm::arm32::ID_INS_VORR;
              break;

            case triton::extlibs::capstone::ARM_INS_VPADAL:
              tritonId = triton::arch::arm::arm32::ID_INS_VPADAL;
              break;

            case triton::extlibs::capstone::ARM_INS_VPADDL:
              tritonId = triton::arch::arm::arm32::ID_INS_VPADDL;
              break;

            case triton::extlibs::capstone::ARM_INS_VPADD:
              tritonId = triton::arch::arm::arm32::ID_INS_VPADD;
              break;

            case triton::extlibs::capstone::ARM_INS_VPMAX:
              tritonId = triton::arch::arm::arm32::ID_INS_VPMAX;
              break;

            case triton::extlibs::capstone::ARM_INS_VPMIN:
              tritonId = triton::arch::arm::arm32::ID_INS_VPMIN;
              break;

            case triton::extlibs::capstone::ARM_INS_VQABS:
              tritonId = triton::arch::arm::arm32::ID_INS_VQABS;
              break;

            case triton::extlibs::capstone::ARM_INS_VQADD:
              tritonId = triton::arch::arm::arm32::ID_INS_VQADD;
              break;

            case triton::extlibs::capstone::ARM_INS_VQDMLAL:
              tritonId = triton::arch::arm::arm32::ID_INS_VQDMLAL;
              break;

            case triton::extlibs::capstone::ARM_INS_VQDMLSL:
              tritonId = triton::arch::arm::arm32::ID_INS_VQDMLSL;
              break;

            case triton::extlibs::capstone::ARM_INS_VQDMULH:
              tritonId = triton::arch::arm::arm32::ID_INS_VQDMULH;
              break;

            case triton::extlibs::capstone::ARM_INS_VQDMULL:
              tritonId = triton::arch::arm::arm32::ID_INS_VQDMULL;
              break;

            case triton::extlibs::capstone::ARM_INS_VQMOVUN:
              tritonId = triton::arch::arm::arm32::ID_INS_VQMOVUN;
              break;

            case triton::extlibs::capstone::ARM_INS_VQMOVN:
              tritonId = triton::arch::arm::arm32::ID_INS_VQMOVN;
              break;

            case triton::extlibs::capstone::ARM_INS_VQNEG:
              tritonId = triton::arch::arm::arm32::ID_INS_VQNEG;
              break;

            case triton::extlibs::capstone::ARM_INS_VQRDMULH:
              tritonId = triton::arch::arm::arm32::ID_INS_VQRDMULH;
              break;

            case triton::extlibs::capstone::ARM_INS_VQRSHL:
              tritonId = triton::arch::arm::arm32::ID_INS_VQRSHL;
              break;

            case triton::extlibs::capstone::ARM_INS_VQRSHRN:
              tritonId = triton::arch::arm::arm32::ID_INS_VQRSHRN;
              break;

            case triton::extlibs::capstone::ARM_INS_VQRSHRUN:
              tritonId = triton::arch::arm::arm32::ID_INS_VQRSHRUN;
              break;

            case triton::extlibs::capstone::ARM_INS_VQSHL:
              tritonId = triton::arch::arm::arm32::ID_INS_VQSHL;
              break;

            case triton::extlibs::capstone::ARM_INS_VQSHLU:
              tritonId = triton::arch::arm::arm32::ID_INS_VQSHLU;
              break;

            case triton::extlibs::capstone::ARM_INS_VQSHRN:
              tritonId = triton::arch::arm::arm32::ID_INS_VQSHRN;
              break;

            case triton::extlibs::capstone::ARM_INS_VQSHRUN:
              tritonId = triton::arch::arm::arm32::ID_INS_VQSHRUN;
              break;

            case triton::extlibs::capstone::ARM_INS_VQSUB:
              tritonId = triton::arch::arm::arm32::ID_INS_VQSUB;
              break;

            case triton::extlibs::capstone::ARM_INS_VRADDHN:
              tritonId = triton::arch::arm::arm32::ID_INS_VRADDHN;
              break;

            case triton::extlibs::capstone::ARM_INS_VRECPE:
              tritonId = triton::arch::arm::arm32::ID_INS_VRECPE;
              break;

            case triton::extlibs::capstone::ARM_INS_VRECPS:
              tritonId = triton::arch::arm::arm32::ID_INS_VRECPS;
              break;

            case triton::extlibs::capstone::ARM_INS_VREV16:
              tritonId = triton::arch::arm::arm32::ID_INS_VREV16;
              break;

            case triton::extlibs::capstone::ARM_INS_VREV32:
              tritonId = triton::arch::arm::arm32::ID_INS_VREV32;
              break;

            case triton::extlibs::capstone::ARM_INS_VREV64:
              tritonId = triton::arch::arm::arm32::ID_INS_VREV64;
              break;

            case triton::extlibs::capstone::ARM_INS_VRHADD:
              tritonId = triton::arch::arm::arm32::ID_INS_VRHADD;
              break;

            case triton::extlibs::capstone::ARM_INS_VRINTA:
              tritonId = triton::arch::arm::arm32::ID_INS_VRINTA;
              break;

            case triton::extlibs::capstone::ARM_INS_VRINTM:
              tritonId = triton::arch::arm::arm32::ID_INS_VRINTM;
              break;

            case triton::extlibs::capstone::ARM_INS_VRINTN:
              tritonId = triton::arch::arm::arm32::ID_INS_VRINTN;
              break;

            case triton::extlibs::capstone::ARM_INS_VRINTP:
              tritonId = triton::arch::arm::arm32::ID_INS_VRINTP;
              break;

            case triton::extlibs::capstone::ARM_INS_VRINTR:
              tritonId = triton::arch::arm::arm32::ID_INS_VRINTR;
              break;

            case triton::extlibs::capstone::ARM_INS_VRINTX:
              tritonId = triton::arch::arm::arm32::ID_INS_VRINTX;
              break;

            case triton::extlibs::capstone::ARM_INS_VRINTZ:
              tritonId = triton::arch::arm::arm32::ID_INS_VRINTZ;
              break;

            case triton::extlibs::capstone::ARM_INS_VRSHL:
              tritonId = triton::arch::arm::arm32::ID_INS_VRSHL;
              break;

            case triton::extlibs::capstone::ARM_INS_VRSHRN:
              tritonId = triton::arch::arm::arm32::ID_INS_VRSHRN;
              break;

            case triton::extlibs::capstone::ARM_INS_VRSHR:
              tritonId = triton::arch::arm::arm32::ID_INS_VRSHR;
              break;

            case triton::extlibs::capstone::ARM_INS_VRSQRTE:
              tritonId = triton::arch::arm::arm32::ID_INS_VRSQRTE;
              break;

            case triton::extlibs::capstone::ARM_INS_VRSQRTS:
              tritonId = triton::arch::arm::arm32::ID_INS_VRSQRTS;
              break;

            case triton::extlibs::capstone::ARM_INS_VRSRA:
              tritonId = triton::arch::arm::arm32::ID_INS_VRSRA;
              break;

            case triton::extlibs::capstone::ARM_INS_VRSUBHN:
              tritonId = triton::arch::arm::arm32::ID_INS_VRSUBHN;
              break;

            case triton::extlibs::capstone::ARM_INS_VSELEQ:
              tritonId = triton::arch::arm::arm32::ID_INS_VSELEQ;
              break;

            case triton::extlibs::capstone::ARM_INS_VSELGE:
              tritonId = triton::arch::arm::arm32::ID_INS_VSELGE;
              break;

            case triton::extlibs::capstone::ARM_INS_VSELGT:
              tritonId = triton::arch::arm::arm32::ID_INS_VSELGT;
              break;

            case triton::extlibs::capstone::ARM_INS_VSELVS:
              tritonId = triton::arch::arm::arm32::ID_INS_VSELVS;
              break;

            case triton::extlibs::capstone::ARM_INS_VSHLL:
              tritonId = triton::arch::arm::arm32::ID_INS_VSHLL;
              break;

            case triton::extlibs::capstone::ARM_INS_VSHL:
              tritonId = triton::arch::arm::arm32::ID_INS_VSHL;
              break;

            case triton::extlibs::capstone::ARM_INS_VSHRN:
              tritonId = triton::arch::arm::arm32::ID_INS_VSHRN;
              break;

            case triton::extlibs::capstone::ARM_INS_VSHR:
              tritonId = triton::arch::arm::arm32::ID_INS_VSHR;
              break;

            case triton::extlibs::capstone::ARM_INS_VSLI:
              tritonId = triton::arch::arm::arm32::ID_INS_VSLI;
              break;

            case triton::extlibs::capstone::ARM_INS_VSQRT:
              tritonId = triton::arch::arm::arm32::ID_INS_VSQRT;
              break;

            case triton::extlibs::capstone::ARM_INS_VSRA:
              tritonId = triton::arch::arm::arm32::ID_INS_VSRA;
              break;

            case triton::extlibs::capstone::ARM_INS_VSRI:
              tritonId = triton::arch::arm::arm32::ID_INS_VSRI;
              break;

            case triton::extlibs::capstone::ARM_INS_VST1:
              tritonId = triton::arch::arm::arm32::ID_INS_VST1;
              break;

            case triton::extlibs::capstone::ARM_INS_VST2:
              tritonId = triton::arch::arm::arm32::ID_INS_VST2;
              break;

            case triton::extlibs::capstone::ARM_INS_VST3:
              tritonId = triton::arch::arm::arm32::ID_INS_VST3;
              break;

            case triton::extlibs::capstone::ARM_INS_VST4:
              tritonId = triton::arch::arm::arm32::ID_INS_VST4;
              break;

            case triton::extlibs::capstone::ARM_INS_VSTMDB:
              tritonId = triton::arch::arm::arm32::ID_INS_VSTMDB;
              break;

            case triton::extlibs::capstone::ARM_INS_VSTMIA:
              tritonId = triton::arch::arm::arm32::ID_INS_VSTMIA;
              break;

            case triton::extlibs::capstone::ARM_INS_VSTR:
              tritonId = triton::arch::arm::arm32::ID_INS_VSTR;
              break;

            case triton::extlibs::capstone::ARM_INS_VSUB:
              tritonId = triton::arch::arm::arm32::ID_INS_VSUB;
              break;

            case triton::extlibs::capstone::ARM_INS_VSUBHN:
              tritonId = triton::arch::arm::arm32::ID_INS_VSUBHN;
              break;

            case triton::extlibs::capstone::ARM_INS_VSUBL:
              tritonId = triton::arch::arm::arm32::ID_INS_VSUBL;
              break;

            case triton::extlibs::capstone::ARM_INS_VSUBW:
              tritonId = triton::arch::arm::arm32::ID_INS_VSUBW;
              break;

            case triton::extlibs::capstone::ARM_INS_VSWP:
              tritonId = triton::arch::arm::arm32::ID_INS_VSWP;
              break;

            case triton::extlibs::capstone::ARM_INS_VTBL:
              tritonId = triton::arch::arm::arm32::ID_INS_VTBL;
              break;

            case triton::extlibs::capstone::ARM_INS_VTBX:
              tritonId = triton::arch::arm::arm32::ID_INS_VTBX;
              break;

            case triton::extlibs::capstone::ARM_INS_VCVTR:
              tritonId = triton::arch::arm::arm32::ID_INS_VCVTR;
              break;

            case triton::extlibs::capstone::ARM_INS_VTRN:
              tritonId = triton::arch::arm::arm32::ID_INS_VTRN;
              break;

            case triton::extlibs::capstone::ARM_INS_VTST:
              tritonId = triton::arch::arm::arm32::ID_INS_VTST;
              break;

            case triton::extlibs::capstone::ARM_INS_VUZP:
              tritonId = triton::arch::arm::arm32::ID_INS_VUZP;
              break;

            case triton::extlibs::capstone::ARM_INS_VZIP:
              tritonId = triton::arch::arm::arm32::ID_INS_VZIP;
              break;

            case triton::extlibs::capstone::ARM_INS_ADDW:
              tritonId = triton::arch::arm::arm32::ID_INS_ADDW;
              break;

            case triton::extlibs::capstone::ARM_INS_ASR:
              tritonId = triton::arch::arm::arm32::ID_INS_ASR;
              break;

            case triton::extlibs::capstone::ARM_INS_DCPS1:
              tritonId = triton::arch::arm::arm32::ID_INS_DCPS1;
              break;

            case triton::extlibs::capstone::ARM_INS_DCPS2:
              tritonId = triton::arch::arm::arm32::ID_INS_DCPS2;
              break;

            case triton::extlibs::capstone::ARM_INS_DCPS3:
              tritonId = triton::arch::arm::arm32::ID_INS_DCPS3;
              break;

            case triton::extlibs::capstone::ARM_INS_IT:
              tritonId = triton::arch::arm::arm32::ID_INS_IT;
              break;

            case triton::extlibs::capstone::ARM_INS_LSL:
              tritonId = triton::arch::arm::arm32::ID_INS_LSL;
              break;

            case triton::extlibs::capstone::ARM_INS_LSR:
              tritonId = triton::arch::arm::arm32::ID_INS_LSR;
              break;

            case triton::extlibs::capstone::ARM_INS_ORN:
              tritonId = triton::arch::arm::arm32::ID_INS_ORN;
              break;

            case triton::extlibs::capstone::ARM_INS_ROR:
              tritonId = triton::arch::arm::arm32::ID_INS_ROR;
              break;

            case triton::extlibs::capstone::ARM_INS_RRX:
              tritonId = triton::arch::arm::arm32::ID_INS_RRX;
              break;

            case triton::extlibs::capstone::ARM_INS_SUBW:
              tritonId = triton::arch::arm::arm32::ID_INS_SUBW;
              break;

            case triton::extlibs::capstone::ARM_INS_TBB:
              tritonId = triton::arch::arm::arm32::ID_INS_TBB;
              break;

            case triton::extlibs::capstone::ARM_INS_TBH:
              tritonId = triton::arch::arm::arm32::ID_INS_TBH;
              break;

            case triton::extlibs::capstone::ARM_INS_CBNZ:
              tritonId = triton::arch::arm::arm32::ID_INS_CBNZ;
              break;

            case triton::extlibs::capstone::ARM_INS_CBZ:
              tritonId = triton::arch::arm::arm32::ID_INS_CBZ;
              break;

            case triton::extlibs::capstone::ARM_INS_POP:
              tritonId = triton::arch::arm::arm32::ID_INS_POP;
              break;

            case triton::extlibs::capstone::ARM_INS_PUSH:
              tritonId = triton::arch::arm::arm32::ID_INS_PUSH;
              break;

            // special instructions
            case triton::extlibs::capstone::ARM_INS_NOP:
              tritonId = triton::arch::arm::arm32::ID_INS_NOP;
              break;

            case triton::extlibs::capstone::ARM_INS_YIELD:
              tritonId = triton::arch::arm::arm32::ID_INS_YIELD;
              break;

            case triton::extlibs::capstone::ARM_INS_WFE:
              tritonId = triton::arch::arm::arm32::ID_INS_WFE;
              break;

            case triton::extlibs::capstone::ARM_INS_WFI:
              tritonId = triton::arch::arm::arm32::ID_INS_WFI;
              break;

            case triton::extlibs::capstone::ARM_INS_SEV:
              tritonId = triton::arch::arm::arm32::ID_INS_SEV;
              break;

            case triton::extlibs::capstone::ARM_INS_SEVL:
              tritonId = triton::arch::arm::arm32::ID_INS_SEVL;
              break;

            case triton::extlibs::capstone::ARM_INS_VPUSH:
              tritonId = triton::arch::arm::arm32::ID_INS_VPUSH;
              break;

            case triton::extlibs::capstone::ARM_INS_VPOP:
              tritonId = triton::arch::arm::arm32::ID_INS_VPOP;
              break;

            default:
              tritonId = triton::arch::arm::arm32::ID_INS_INVALID;
              break;
          }

          return tritonId;
        }


        triton::uint32 Arm32Specifications::getMemoryOperandSpecialSize(triton::uint32 id) const {
          switch (id) {
            case ID_INS_LDRB:
            case ID_INS_LDRSB:
            case ID_INS_STRB:
            case ID_INS_TBB:
              return 1;
            case ID_INS_LDRH:
            case ID_INS_LDRSH:
            case ID_INS_STRH:
              return 2;
            default:
              return 0;
          }
        }

      }; /* arm32 namespace */
    }; /* arm namespace */
  }; /* arch namespace */
}; /* triton namespace */
