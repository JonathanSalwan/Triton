//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <cassert>

#include <triton/architecture.hpp>
#include <triton/cpuSize.hpp>
#include <triton/exceptions.hpp>
#include <triton/externalLibs.hpp>
#include <triton/riscvSpecifications.hpp>



namespace triton {
  namespace arch {
    namespace riscv {

      riscvSpecifications::riscvSpecifications(triton::arch::architecture_e arch) {
        if (arch != triton::arch::ARCH_RV64 && arch != triton::arch::ARCH_RV32)
          throw triton::exceptions::Architecture("riscvSpecifications::riscvSpecifications(): Invalid architecture.");

        if (arch == triton::arch::ARCH_RV64) {
          // Fill id2reg and name2id with those available in riscv from spec
          #define REG_SPEC(CS_UPPER_NAME, UPPER_NAME, LOWER_NAME, ABI_NAME, RISCV_UPPER, RISCV_LOWER, MUTABLE) \
            id2reg.emplace(ID_REG_RV64_##UPPER_NAME,                                                           \
                               triton::arch::Register(triton::arch::ID_REG_RV64_##UPPER_NAME,                  \
                                                      #LOWER_NAME,                                             \
                                                      triton::arch::ID_REG_RV64_##UPPER_NAME,                  \
                                                      RISCV_UPPER,                                             \
                                                      RISCV_LOWER,                                             \
                                                      true)                                                    \
                              );                                                                               \
            name2id.emplace(#LOWER_NAME, ID_REG_RV64_##UPPER_NAME);                                            \
            name2id.emplace(#ABI_NAME,   ID_REG_RV64_##UPPER_NAME);
          // Handle register not available in capstone as normal registers
          #define REG_SPEC_NO_CAPSTONE REG_SPEC
          #include "triton/riscv64.spec"
        }
        else { // RV32
          // Fill id2reg and name2id with those available in riscv32 from spec
          #define REG_SPEC(CS_UPPER_NAME, UPPER_NAME, LOWER_NAME, ABI_NAME, RISCV_UPPER, RISCV_LOWER, MUTABLE) \
            id2reg.emplace(ID_REG_RV32_##UPPER_NAME,                                                           \
                               triton::arch::Register(triton::arch::ID_REG_RV32_##UPPER_NAME,                  \
                                                      #LOWER_NAME,                                             \
                                                      triton::arch::ID_REG_RV32_##UPPER_NAME,                  \
                                                      RISCV_UPPER,                                             \
                                                      RISCV_LOWER,                                             \
                                                      true)                                                    \
                              );                                                                               \
            name2id.emplace(#LOWER_NAME, ID_REG_RV32_##UPPER_NAME);                                            \
            name2id.emplace(#ABI_NAME,   ID_REG_RV32_##UPPER_NAME);
          // Handle register not available in capstone as normal registers
          #define REG_SPEC_NO_CAPSTONE REG_SPEC
          #include "triton/riscv32.spec"
        }
      }


      triton::arch::register_e riscvSpecifications::capstoneRegisterToTritonRegister64(triton::uint32 id) const {
        triton::arch::register_e tritonId = triton::arch::ID_REG_INVALID;
        switch (id) {
          // Convert registers from capstone value to triton value
         #define REG_SPEC(CS_UPPER_NAME, UPPER_NAME, _1, _2, _3, _4, _5) \
          case triton::extlibs::capstone::RISCV_REG_##CS_UPPER_NAME:     \
            tritonId = triton::arch::ID_REG_RV64_##UPPER_NAME;           \
            break;
          // Ignore registers not available in capstone
          #define REG_SPEC_NO_CAPSTONE(_1, _2, _3, _4, _5, _6, _7)
          #include "triton/riscv64.spec"

          default:
            tritonId = triton::arch::ID_REG_INVALID;
            break;

        }
        return tritonId;
      }


      triton::arch::register_e riscvSpecifications::capstoneRegisterToTritonRegister32(triton::uint32 id) const {
        triton::arch::register_e tritonId = triton::arch::ID_REG_INVALID;
        switch (id) {
          // Convert registers from capstone value to triton value
         #define REG_SPEC(CS_UPPER_NAME, UPPER_NAME, _1, _2, _3, _4, _5) \
          case triton::extlibs::capstone::RISCV_REG_##CS_UPPER_NAME:     \
            tritonId = triton::arch::ID_REG_RV32_##UPPER_NAME;           \
            break;
          // Ignore registers not available in capstone
          #define REG_SPEC_NO_CAPSTONE(_1, _2, _3, _4, _5, _6, _7)
          #include "triton/riscv32.spec"

          default:
            tritonId = triton::arch::ID_REG_INVALID;
            break;

        }
        return tritonId;
      }


      triton::uint32 riscvSpecifications::capstoneInstructionToTritonInstruction(triton::uint32 id) const {
        triton::uint32 tritonId = triton::arch::riscv::ID_INS_INVALID;

        switch (id) {
          case triton::extlibs::capstone::RISCV_INS_INVALID:
            tritonId = triton::arch::riscv::ID_INS_INVALID;
            break;

          case triton::extlibs::capstone::RISCV_INS_ADD:
            tritonId = triton::arch::riscv::ID_INS_ADD;
            break;

          case triton::extlibs::capstone::RISCV_INS_ADDI:
            tritonId = triton::arch::riscv::ID_INS_ADDI;
            break;

          case triton::extlibs::capstone::RISCV_INS_ADDIW:
            tritonId = triton::arch::riscv::ID_INS_ADDIW;
            break;

          case triton::extlibs::capstone::RISCV_INS_ADDW:
            tritonId = triton::arch::riscv::ID_INS_ADDW;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOADD_D:
            tritonId = triton::arch::riscv::ID_INS_AMOADD_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOADD_D_AQ:
            tritonId = triton::arch::riscv::ID_INS_AMOADD_D_AQ;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOADD_D_AQ_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOADD_D_AQ_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOADD_D_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOADD_D_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOADD_W:
            tritonId = triton::arch::riscv::ID_INS_AMOADD_W;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOADD_W_AQ:
            tritonId = triton::arch::riscv::ID_INS_AMOADD_W_AQ;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOADD_W_AQ_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOADD_W_AQ_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOADD_W_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOADD_W_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOAND_D:
            tritonId = triton::arch::riscv::ID_INS_AMOAND_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOAND_D_AQ:
            tritonId = triton::arch::riscv::ID_INS_AMOAND_D_AQ;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOAND_D_AQ_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOAND_D_AQ_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOAND_D_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOAND_D_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOAND_W:
            tritonId = triton::arch::riscv::ID_INS_AMOAND_W;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOAND_W_AQ:
            tritonId = triton::arch::riscv::ID_INS_AMOAND_W_AQ;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOAND_W_AQ_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOAND_W_AQ_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOAND_W_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOAND_W_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMAXU_D:
            tritonId = triton::arch::riscv::ID_INS_AMOMAXU_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMAXU_D_AQ:
            tritonId = triton::arch::riscv::ID_INS_AMOMAXU_D_AQ;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMAXU_D_AQ_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOMAXU_D_AQ_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMAXU_D_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOMAXU_D_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMAXU_W:
            tritonId = triton::arch::riscv::ID_INS_AMOMAXU_W;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMAXU_W_AQ:
            tritonId = triton::arch::riscv::ID_INS_AMOMAXU_W_AQ;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMAXU_W_AQ_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOMAXU_W_AQ_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMAXU_W_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOMAXU_W_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMAX_D:
            tritonId = triton::arch::riscv::ID_INS_AMOMAX_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMAX_D_AQ:
            tritonId = triton::arch::riscv::ID_INS_AMOMAX_D_AQ;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMAX_D_AQ_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOMAX_D_AQ_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMAX_D_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOMAX_D_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMAX_W:
            tritonId = triton::arch::riscv::ID_INS_AMOMAX_W;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMAX_W_AQ:
            tritonId = triton::arch::riscv::ID_INS_AMOMAX_W_AQ;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMAX_W_AQ_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOMAX_W_AQ_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMAX_W_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOMAX_W_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMINU_D:
            tritonId = triton::arch::riscv::ID_INS_AMOMINU_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMINU_D_AQ:
            tritonId = triton::arch::riscv::ID_INS_AMOMINU_D_AQ;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMINU_D_AQ_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOMINU_D_AQ_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMINU_D_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOMINU_D_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMINU_W:
            tritonId = triton::arch::riscv::ID_INS_AMOMINU_W;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMINU_W_AQ:
            tritonId = triton::arch::riscv::ID_INS_AMOMINU_W_AQ;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMINU_W_AQ_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOMINU_W_AQ_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMINU_W_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOMINU_W_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMIN_D:
            tritonId = triton::arch::riscv::ID_INS_AMOMIN_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMIN_D_AQ:
            tritonId = triton::arch::riscv::ID_INS_AMOMIN_D_AQ;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMIN_D_AQ_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOMIN_D_AQ_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMIN_D_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOMIN_D_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMIN_W:
            tritonId = triton::arch::riscv::ID_INS_AMOMIN_W;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMIN_W_AQ:
            tritonId = triton::arch::riscv::ID_INS_AMOMIN_W_AQ;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMIN_W_AQ_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOMIN_W_AQ_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOMIN_W_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOMIN_W_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOOR_D:
            tritonId = triton::arch::riscv::ID_INS_AMOOR_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOOR_D_AQ:
            tritonId = triton::arch::riscv::ID_INS_AMOOR_D_AQ;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOOR_D_AQ_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOOR_D_AQ_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOOR_D_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOOR_D_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOOR_W:
            tritonId = triton::arch::riscv::ID_INS_AMOOR_W;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOOR_W_AQ:
            tritonId = triton::arch::riscv::ID_INS_AMOOR_W_AQ;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOOR_W_AQ_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOOR_W_AQ_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOOR_W_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOOR_W_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOSWAP_D:
            tritonId = triton::arch::riscv::ID_INS_AMOSWAP_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOSWAP_D_AQ:
            tritonId = triton::arch::riscv::ID_INS_AMOSWAP_D_AQ;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOSWAP_D_AQ_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOSWAP_D_AQ_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOSWAP_D_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOSWAP_D_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOSWAP_W:
            tritonId = triton::arch::riscv::ID_INS_AMOSWAP_W;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOSWAP_W_AQ:
            tritonId = triton::arch::riscv::ID_INS_AMOSWAP_W_AQ;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOSWAP_W_AQ_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOSWAP_W_AQ_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOSWAP_W_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOSWAP_W_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOXOR_D:
            tritonId = triton::arch::riscv::ID_INS_AMOXOR_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOXOR_D_AQ:
            tritonId = triton::arch::riscv::ID_INS_AMOXOR_D_AQ;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOXOR_D_AQ_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOXOR_D_AQ_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOXOR_D_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOXOR_D_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOXOR_W:
            tritonId = triton::arch::riscv::ID_INS_AMOXOR_W;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOXOR_W_AQ:
            tritonId = triton::arch::riscv::ID_INS_AMOXOR_W_AQ;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOXOR_W_AQ_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOXOR_W_AQ_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AMOXOR_W_RL:
            tritonId = triton::arch::riscv::ID_INS_AMOXOR_W_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_AND:
            tritonId = triton::arch::riscv::ID_INS_AND;
            break;

          case triton::extlibs::capstone::RISCV_INS_ANDI:
            tritonId = triton::arch::riscv::ID_INS_ANDI;
            break;

          case triton::extlibs::capstone::RISCV_INS_AUIPC:
            tritonId = triton::arch::riscv::ID_INS_AUIPC;
            break;

          case triton::extlibs::capstone::RISCV_INS_BEQ:
            tritonId = triton::arch::riscv::ID_INS_BEQ;
            break;

          case triton::extlibs::capstone::RISCV_INS_BGE:
            tritonId = triton::arch::riscv::ID_INS_BGE;
            break;

          case triton::extlibs::capstone::RISCV_INS_BGEU:
            tritonId = triton::arch::riscv::ID_INS_BGEU;
            break;

          case triton::extlibs::capstone::RISCV_INS_BLT:
            tritonId = triton::arch::riscv::ID_INS_BLT;
            break;

          case triton::extlibs::capstone::RISCV_INS_BLTU:
            tritonId = triton::arch::riscv::ID_INS_BLTU;
            break;

          case triton::extlibs::capstone::RISCV_INS_BNE:
            tritonId = triton::arch::riscv::ID_INS_BNE;
            break;

          case triton::extlibs::capstone::RISCV_INS_CSRRC:
            tritonId = triton::arch::riscv::ID_INS_CSRRC;
            break;

          case triton::extlibs::capstone::RISCV_INS_CSRRCI:
            tritonId = triton::arch::riscv::ID_INS_CSRRCI;
            break;

          case triton::extlibs::capstone::RISCV_INS_CSRRS:
            tritonId = triton::arch::riscv::ID_INS_CSRRS;
            break;

          case triton::extlibs::capstone::RISCV_INS_CSRRSI:
            tritonId = triton::arch::riscv::ID_INS_CSRRSI;
            break;

          case triton::extlibs::capstone::RISCV_INS_CSRRW:
            tritonId = triton::arch::riscv::ID_INS_CSRRW;
            break;

          case triton::extlibs::capstone::RISCV_INS_CSRRWI:
            tritonId = triton::arch::riscv::ID_INS_CSRRWI;
            break;
          /* Compressed instructions */
          case triton::extlibs::capstone::RISCV_INS_C_ADD:
            tritonId = triton::arch::riscv::ID_INS_C_ADD;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_ADDI:
            tritonId = triton::arch::riscv::ID_INS_C_ADDI;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_ADDI16SP:
            tritonId = triton::arch::riscv::ID_INS_C_ADDI16SP;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_ADDI4SPN:
            tritonId = triton::arch::riscv::ID_INS_C_ADDI4SPN;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_ADDIW:
            tritonId = triton::arch::riscv::ID_INS_C_ADDIW;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_ADDW:
            tritonId = triton::arch::riscv::ID_INS_C_ADDW;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_AND:
            tritonId = triton::arch::riscv::ID_INS_C_AND;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_ANDI:
            tritonId = triton::arch::riscv::ID_INS_C_ANDI;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_BEQZ:
            tritonId = triton::arch::riscv::ID_INS_C_BEQZ;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_BNEZ:
            tritonId = triton::arch::riscv::ID_INS_C_BNEZ;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_EBREAK:
            tritonId = triton::arch::riscv::ID_INS_C_EBREAK;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_FLD:
            tritonId = triton::arch::riscv::ID_INS_C_FLD;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_FLDSP:
            tritonId = triton::arch::riscv::ID_INS_C_FLDSP;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_FLW:
            tritonId = triton::arch::riscv::ID_INS_C_FLW;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_FLWSP:
            tritonId = triton::arch::riscv::ID_INS_C_FLWSP;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_FSD:
            tritonId = triton::arch::riscv::ID_INS_C_FSD;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_FSDSP:
            tritonId = triton::arch::riscv::ID_INS_C_FSDSP;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_FSW:
            tritonId = triton::arch::riscv::ID_INS_C_FSW;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_FSWSP:
            tritonId = triton::arch::riscv::ID_INS_C_FSWSP;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_J:
            tritonId = triton::arch::riscv::ID_INS_C_J;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_JAL:
            tritonId = triton::arch::riscv::ID_INS_C_JAL;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_JALR:
            tritonId = triton::arch::riscv::ID_INS_C_JALR;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_JR:
            tritonId = triton::arch::riscv::ID_INS_C_JR;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_LD:
            tritonId = triton::arch::riscv::ID_INS_C_LD;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_LDSP:
            tritonId = triton::arch::riscv::ID_INS_C_LDSP;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_LI:
            tritonId = triton::arch::riscv::ID_INS_C_LI;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_LUI:
            tritonId = triton::arch::riscv::ID_INS_C_LUI;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_LW:
            tritonId = triton::arch::riscv::ID_INS_C_LW;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_LWSP:
            tritonId = triton::arch::riscv::ID_INS_C_LWSP;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_MV:
            tritonId = triton::arch::riscv::ID_INS_C_MV;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_NOP:
            tritonId = triton::arch::riscv::ID_INS_C_NOP;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_OR:
            tritonId = triton::arch::riscv::ID_INS_C_OR;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_SD:
            tritonId = triton::arch::riscv::ID_INS_C_SD;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_SDSP:
            tritonId = triton::arch::riscv::ID_INS_C_SDSP;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_SLLI:
            tritonId = triton::arch::riscv::ID_INS_C_SLLI;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_SRAI:
            tritonId = triton::arch::riscv::ID_INS_C_SRAI;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_SRLI:
            tritonId = triton::arch::riscv::ID_INS_C_SRLI;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_SUB:
            tritonId = triton::arch::riscv::ID_INS_C_SUB;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_SUBW:
            tritonId = triton::arch::riscv::ID_INS_C_SUBW;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_SW:
            tritonId = triton::arch::riscv::ID_INS_C_SW;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_SWSP:
            tritonId = triton::arch::riscv::ID_INS_C_SWSP;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_UNIMP:
            tritonId = triton::arch::riscv::ID_INS_C_UNIMP;
            break;

          case triton::extlibs::capstone::RISCV_INS_C_XOR:
            tritonId = triton::arch::riscv::ID_INS_C_XOR;
            break;
          /* End of compressed instructions */
          case triton::extlibs::capstone::RISCV_INS_DIV:
            tritonId = triton::arch::riscv::ID_INS_DIV;
            break;

          case triton::extlibs::capstone::RISCV_INS_DIVU:
            tritonId = triton::arch::riscv::ID_INS_DIVU;
            break;

          case triton::extlibs::capstone::RISCV_INS_DIVUW:
            tritonId = triton::arch::riscv::ID_INS_DIVUW;
            break;

          case triton::extlibs::capstone::RISCV_INS_DIVW:
            tritonId = triton::arch::riscv::ID_INS_DIVW;
            break;

          case triton::extlibs::capstone::RISCV_INS_EBREAK:
            tritonId = triton::arch::riscv::ID_INS_EBREAK;
            break;

          case triton::extlibs::capstone::RISCV_INS_ECALL:
            tritonId = triton::arch::riscv::ID_INS_ECALL;
            break;

          case triton::extlibs::capstone::RISCV_INS_FADD_D:
            tritonId = triton::arch::riscv::ID_INS_FADD_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_FADD_S:
            tritonId = triton::arch::riscv::ID_INS_FADD_S;
            break;

          case triton::extlibs::capstone::RISCV_INS_FCLASS_D:
            tritonId = triton::arch::riscv::ID_INS_FCLASS_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_FCLASS_S:
            tritonId = triton::arch::riscv::ID_INS_FCLASS_S;
            break;

          case triton::extlibs::capstone::RISCV_INS_FCVT_D_L:
            tritonId = triton::arch::riscv::ID_INS_FCVT_D_L;
            break;

          case triton::extlibs::capstone::RISCV_INS_FCVT_D_LU:
            tritonId = triton::arch::riscv::ID_INS_FCVT_D_LU;
            break;

          case triton::extlibs::capstone::RISCV_INS_FCVT_D_S:
            tritonId = triton::arch::riscv::ID_INS_FCVT_D_S;
            break;

          case triton::extlibs::capstone::RISCV_INS_FCVT_D_W:
            tritonId = triton::arch::riscv::ID_INS_FCVT_D_W;
            break;

          case triton::extlibs::capstone::RISCV_INS_FCVT_D_WU:
            tritonId = triton::arch::riscv::ID_INS_FCVT_D_WU;
            break;

          case triton::extlibs::capstone::RISCV_INS_FCVT_LU_D:
            tritonId = triton::arch::riscv::ID_INS_FCVT_LU_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_FCVT_LU_S:
            tritonId = triton::arch::riscv::ID_INS_FCVT_LU_S;
            break;

          case triton::extlibs::capstone::RISCV_INS_FCVT_L_D:
            tritonId = triton::arch::riscv::ID_INS_FCVT_L_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_FCVT_L_S:
            tritonId = triton::arch::riscv::ID_INS_FCVT_L_S;
            break;

          case triton::extlibs::capstone::RISCV_INS_FCVT_S_D:
            tritonId = triton::arch::riscv::ID_INS_FCVT_S_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_FCVT_S_L:
            tritonId = triton::arch::riscv::ID_INS_FCVT_S_L;
            break;

          case triton::extlibs::capstone::RISCV_INS_FCVT_S_LU:
            tritonId = triton::arch::riscv::ID_INS_FCVT_S_LU;
            break;

          case triton::extlibs::capstone::RISCV_INS_FCVT_S_W:
            tritonId = triton::arch::riscv::ID_INS_FCVT_S_W;
            break;

          case triton::extlibs::capstone::RISCV_INS_FCVT_S_WU:
            tritonId = triton::arch::riscv::ID_INS_FCVT_S_WU;
            break;

          case triton::extlibs::capstone::RISCV_INS_FCVT_WU_D:
            tritonId = triton::arch::riscv::ID_INS_FCVT_WU_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_FCVT_WU_S:
            tritonId = triton::arch::riscv::ID_INS_FCVT_WU_S;
            break;

          case triton::extlibs::capstone::RISCV_INS_FCVT_W_D:
            tritonId = triton::arch::riscv::ID_INS_FCVT_W_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_FCVT_W_S:
            tritonId = triton::arch::riscv::ID_INS_FCVT_W_S;
            break;

          case triton::extlibs::capstone::RISCV_INS_FDIV_D:
            tritonId = triton::arch::riscv::ID_INS_FDIV_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_FDIV_S:
            tritonId = triton::arch::riscv::ID_INS_FDIV_S;
            break;

          case triton::extlibs::capstone::RISCV_INS_FENCE:
            tritonId = triton::arch::riscv::ID_INS_FENCE;
            break;

          case triton::extlibs::capstone::RISCV_INS_FENCE_I:
            tritonId = triton::arch::riscv::ID_INS_FENCE_I;
            break;

          case triton::extlibs::capstone::RISCV_INS_FENCE_TSO:
            tritonId = triton::arch::riscv::ID_INS_FENCE_TSO;
            break;

          case triton::extlibs::capstone::RISCV_INS_FEQ_D:
            tritonId = triton::arch::riscv::ID_INS_FEQ_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_FEQ_S:
            tritonId = triton::arch::riscv::ID_INS_FEQ_S;
            break;

          case triton::extlibs::capstone::RISCV_INS_FLD:
            tritonId = triton::arch::riscv::ID_INS_FLD;
            break;

          case triton::extlibs::capstone::RISCV_INS_FLE_D:
            tritonId = triton::arch::riscv::ID_INS_FLE_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_FLE_S:
            tritonId = triton::arch::riscv::ID_INS_FLE_S;
            break;

          case triton::extlibs::capstone::RISCV_INS_FLT_D:
            tritonId = triton::arch::riscv::ID_INS_FLT_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_FLT_S:
            tritonId = triton::arch::riscv::ID_INS_FLT_S;
            break;

          case triton::extlibs::capstone::RISCV_INS_FLW:
            tritonId = triton::arch::riscv::ID_INS_FLW;
            break;

          case triton::extlibs::capstone::RISCV_INS_FMADD_D:
            tritonId = triton::arch::riscv::ID_INS_FMADD_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_FMADD_S:
            tritonId = triton::arch::riscv::ID_INS_FMADD_S;
            break;

          case triton::extlibs::capstone::RISCV_INS_FMAX_D:
            tritonId = triton::arch::riscv::ID_INS_FMAX_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_FMAX_S:
            tritonId = triton::arch::riscv::ID_INS_FMAX_S;
            break;

          case triton::extlibs::capstone::RISCV_INS_FMIN_D:
            tritonId = triton::arch::riscv::ID_INS_FMIN_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_FMIN_S:
            tritonId = triton::arch::riscv::ID_INS_FMIN_S;
            break;

          case triton::extlibs::capstone::RISCV_INS_FMSUB_D:
            tritonId = triton::arch::riscv::ID_INS_FMSUB_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_FMSUB_S:
            tritonId = triton::arch::riscv::ID_INS_FMSUB_S;
            break;

          case triton::extlibs::capstone::RISCV_INS_FMUL_D:
            tritonId = triton::arch::riscv::ID_INS_FMUL_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_FMUL_S:
            tritonId = triton::arch::riscv::ID_INS_FMUL_S;
            break;

          case triton::extlibs::capstone::RISCV_INS_FMV_D_X:
            tritonId = triton::arch::riscv::ID_INS_FMV_D_X;
            break;

          case triton::extlibs::capstone::RISCV_INS_FMV_W_X:
            tritonId = triton::arch::riscv::ID_INS_FMV_W_X;
            break;

          case triton::extlibs::capstone::RISCV_INS_FMV_X_D:
            tritonId = triton::arch::riscv::ID_INS_FMV_X_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_FMV_X_W:
            tritonId = triton::arch::riscv::ID_INS_FMV_X_W;
            break;

          case triton::extlibs::capstone::RISCV_INS_FNMADD_D:
            tritonId = triton::arch::riscv::ID_INS_FNMADD_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_FNMADD_S:
            tritonId = triton::arch::riscv::ID_INS_FNMADD_S;
            break;

          case triton::extlibs::capstone::RISCV_INS_FNMSUB_D:
            tritonId = triton::arch::riscv::ID_INS_FNMSUB_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_FNMSUB_S:
            tritonId = triton::arch::riscv::ID_INS_FNMSUB_S;
            break;

          case triton::extlibs::capstone::RISCV_INS_FSD:
            tritonId = triton::arch::riscv::ID_INS_FSD;
            break;

          case triton::extlibs::capstone::RISCV_INS_FSGNJN_D:
            tritonId = triton::arch::riscv::ID_INS_FSGNJN_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_FSGNJN_S:
            tritonId = triton::arch::riscv::ID_INS_FSGNJN_S;
            break;

          case triton::extlibs::capstone::RISCV_INS_FSGNJX_D:
            tritonId = triton::arch::riscv::ID_INS_FSGNJX_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_FSGNJX_S:
            tritonId = triton::arch::riscv::ID_INS_FSGNJX_S;
            break;

          case triton::extlibs::capstone::RISCV_INS_FSGNJ_D:
            tritonId = triton::arch::riscv::ID_INS_FSGNJ_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_FSGNJ_S:
            tritonId = triton::arch::riscv::ID_INS_FSGNJ_S;
            break;

          case triton::extlibs::capstone::RISCV_INS_FSQRT_D:
            tritonId = triton::arch::riscv::ID_INS_FSQRT_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_FSQRT_S:
            tritonId = triton::arch::riscv::ID_INS_FSQRT_S;
            break;

          case triton::extlibs::capstone::RISCV_INS_FSUB_D:
            tritonId = triton::arch::riscv::ID_INS_FSUB_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_FSUB_S:
            tritonId = triton::arch::riscv::ID_INS_FSUB_S;
            break;

          case triton::extlibs::capstone::RISCV_INS_FSW:
            tritonId = triton::arch::riscv::ID_INS_FSW;
            break;

          case triton::extlibs::capstone::RISCV_INS_JAL:
            tritonId = triton::arch::riscv::ID_INS_JAL;
            break;

          case triton::extlibs::capstone::RISCV_INS_JALR:
            tritonId = triton::arch::riscv::ID_INS_JALR;
            break;

          case triton::extlibs::capstone::RISCV_INS_LB:
            tritonId = triton::arch::riscv::ID_INS_LB;
            break;

          case triton::extlibs::capstone::RISCV_INS_LBU:
            tritonId = triton::arch::riscv::ID_INS_LBU;
            break;

          case triton::extlibs::capstone::RISCV_INS_LD:
            tritonId = triton::arch::riscv::ID_INS_LD;
            break;

          case triton::extlibs::capstone::RISCV_INS_LH:
            tritonId = triton::arch::riscv::ID_INS_LH;
            break;

          case triton::extlibs::capstone::RISCV_INS_LHU:
            tritonId = triton::arch::riscv::ID_INS_LHU;
            break;

          case triton::extlibs::capstone::RISCV_INS_LR_D:
            tritonId = triton::arch::riscv::ID_INS_LR_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_LR_D_AQ:
            tritonId = triton::arch::riscv::ID_INS_LR_D_AQ;
            break;

          case triton::extlibs::capstone::RISCV_INS_LR_D_AQ_RL:
            tritonId = triton::arch::riscv::ID_INS_LR_D_AQ_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_LR_D_RL:
            tritonId = triton::arch::riscv::ID_INS_LR_D_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_LR_W:
            tritonId = triton::arch::riscv::ID_INS_LR_W;
            break;

          case triton::extlibs::capstone::RISCV_INS_LR_W_AQ:
            tritonId = triton::arch::riscv::ID_INS_LR_W_AQ;
            break;

          case triton::extlibs::capstone::RISCV_INS_LR_W_AQ_RL:
            tritonId = triton::arch::riscv::ID_INS_LR_W_AQ_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_LR_W_RL:
            tritonId = triton::arch::riscv::ID_INS_LR_W_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_LUI:
            tritonId = triton::arch::riscv::ID_INS_LUI;
            break;

          case triton::extlibs::capstone::RISCV_INS_LW:
            tritonId = triton::arch::riscv::ID_INS_LW;
            break;

          case triton::extlibs::capstone::RISCV_INS_LWU:
            tritonId = triton::arch::riscv::ID_INS_LWU;
            break;

          case triton::extlibs::capstone::RISCV_INS_MRET:
            tritonId = triton::arch::riscv::ID_INS_MRET;
            break;

          case triton::extlibs::capstone::RISCV_INS_MUL:
            tritonId = triton::arch::riscv::ID_INS_MUL;
            break;

          case triton::extlibs::capstone::RISCV_INS_MULH:
            tritonId = triton::arch::riscv::ID_INS_MULH;
            break;

          case triton::extlibs::capstone::RISCV_INS_MULHSU:
            tritonId = triton::arch::riscv::ID_INS_MULHSU;
            break;

          case triton::extlibs::capstone::RISCV_INS_MULHU:
            tritonId = triton::arch::riscv::ID_INS_MULHU;
            break;

          case triton::extlibs::capstone::RISCV_INS_MULW:
            tritonId = triton::arch::riscv::ID_INS_MULW;
            break;

          case triton::extlibs::capstone::RISCV_INS_OR:
            tritonId = triton::arch::riscv::ID_INS_OR;
            break;

          case triton::extlibs::capstone::RISCV_INS_ORI:
            tritonId = triton::arch::riscv::ID_INS_ORI;
            break;

          case triton::extlibs::capstone::RISCV_INS_REM:
            tritonId = triton::arch::riscv::ID_INS_REM;
            break;

          case triton::extlibs::capstone::RISCV_INS_REMU:
            tritonId = triton::arch::riscv::ID_INS_REMU;
            break;

          case triton::extlibs::capstone::RISCV_INS_REMUW:
            tritonId = triton::arch::riscv::ID_INS_REMUW;
            break;

          case triton::extlibs::capstone::RISCV_INS_REMW:
            tritonId = triton::arch::riscv::ID_INS_REMW;
            break;

          case triton::extlibs::capstone::RISCV_INS_SB:
            tritonId = triton::arch::riscv::ID_INS_SB;
            break;

          case triton::extlibs::capstone::RISCV_INS_SC_D:
            tritonId = triton::arch::riscv::ID_INS_SC_D;
            break;

          case triton::extlibs::capstone::RISCV_INS_SC_D_AQ:
            tritonId = triton::arch::riscv::ID_INS_SC_D_AQ;
            break;

          case triton::extlibs::capstone::RISCV_INS_SC_D_AQ_RL:
            tritonId = triton::arch::riscv::ID_INS_SC_D_AQ_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_SC_D_RL:
            tritonId = triton::arch::riscv::ID_INS_SC_D_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_SC_W:
            tritonId = triton::arch::riscv::ID_INS_SC_W;
            break;

          case triton::extlibs::capstone::RISCV_INS_SC_W_AQ:
            tritonId = triton::arch::riscv::ID_INS_SC_W_AQ;
            break;

          case triton::extlibs::capstone::RISCV_INS_SC_W_AQ_RL:
            tritonId = triton::arch::riscv::ID_INS_SC_W_AQ_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_SC_W_RL:
            tritonId = triton::arch::riscv::ID_INS_SC_W_RL;
            break;

          case triton::extlibs::capstone::RISCV_INS_SD:
            tritonId = triton::arch::riscv::ID_INS_SD;
            break;

          case triton::extlibs::capstone::RISCV_INS_SFENCE_VMA:
            tritonId = triton::arch::riscv::ID_INS_SFENCE_VMA;
            break;

          case triton::extlibs::capstone::RISCV_INS_SH:
            tritonId = triton::arch::riscv::ID_INS_SH;
            break;

          case triton::extlibs::capstone::RISCV_INS_SLL:
            tritonId = triton::arch::riscv::ID_INS_SLL;
            break;

          case triton::extlibs::capstone::RISCV_INS_SLLI:
            tritonId = triton::arch::riscv::ID_INS_SLLI;
            break;

          case triton::extlibs::capstone::RISCV_INS_SLLIW:
            tritonId = triton::arch::riscv::ID_INS_SLLIW;
            break;

          case triton::extlibs::capstone::RISCV_INS_SLLW:
            tritonId = triton::arch::riscv::ID_INS_SLLW;
            break;

          case triton::extlibs::capstone::RISCV_INS_SLT:
            tritonId = triton::arch::riscv::ID_INS_SLT;
            break;

          case triton::extlibs::capstone::RISCV_INS_SLTI:
            tritonId = triton::arch::riscv::ID_INS_SLTI;
            break;

          case triton::extlibs::capstone::RISCV_INS_SLTIU:
            tritonId = triton::arch::riscv::ID_INS_SLTIU;
            break;

          case triton::extlibs::capstone::RISCV_INS_SLTU:
            tritonId = triton::arch::riscv::ID_INS_SLTU;
            break;

          case triton::extlibs::capstone::RISCV_INS_SRA:
            tritonId = triton::arch::riscv::ID_INS_SRA;
            break;

          case triton::extlibs::capstone::RISCV_INS_SRAI:
            tritonId = triton::arch::riscv::ID_INS_SRAI;
            break;

          case triton::extlibs::capstone::RISCV_INS_SRAIW:
            tritonId = triton::arch::riscv::ID_INS_SRAIW;
            break;

          case triton::extlibs::capstone::RISCV_INS_SRAW:
            tritonId = triton::arch::riscv::ID_INS_SRAW;
            break;

          case triton::extlibs::capstone::RISCV_INS_SRET:
            tritonId = triton::arch::riscv::ID_INS_SRET;
            break;

          case triton::extlibs::capstone::RISCV_INS_SRL:
            tritonId = triton::arch::riscv::ID_INS_SRL;
            break;

          case triton::extlibs::capstone::RISCV_INS_SRLI:
            tritonId = triton::arch::riscv::ID_INS_SRLI;
            break;

          case triton::extlibs::capstone::RISCV_INS_SRLIW:
            tritonId = triton::arch::riscv::ID_INS_SRLIW;
            break;

          case triton::extlibs::capstone::RISCV_INS_SRLW:
            tritonId = triton::arch::riscv::ID_INS_SRLW;
            break;

          case triton::extlibs::capstone::RISCV_INS_SUB:
            tritonId = triton::arch::riscv::ID_INS_SUB;
            break;

          case triton::extlibs::capstone::RISCV_INS_SUBW:
            tritonId = triton::arch::riscv::ID_INS_SUBW;
            break;

          case triton::extlibs::capstone::RISCV_INS_SW:
            tritonId = triton::arch::riscv::ID_INS_SW;
            break;

          case triton::extlibs::capstone::RISCV_INS_UNIMP:
            tritonId = ID_INS_UNIMP;
            break;

          case triton::extlibs::capstone::RISCV_INS_URET:
            tritonId = ID_INS_URET;
            break;

          case triton::extlibs::capstone::RISCV_INS_WFI:
            tritonId = ID_INS_WFI;
            break;

          case triton::extlibs::capstone::RISCV_INS_XOR:
            tritonId = ID_INS_XOR;
            break;

          case triton::extlibs::capstone::RISCV_INS_XORI:
            tritonId = ID_INS_XORI;
            break;
          default:
            tritonId = triton::arch::riscv::ID_INS_INVALID;
            break;
        }

        return tritonId;
      }


      triton::uint32 riscvSpecifications::getMemoryOperandSpecialSize(triton::uint32 id) const {
        switch (id) {
          case ID_INS_LB:
          case ID_INS_LBU:
          case ID_INS_SB:
            return 1;
          case ID_INS_LH:
          case ID_INS_LHU:
          case ID_INS_SH:
            return 2;
          case ID_INS_LW:
          case ID_INS_LWU:
          case ID_INS_SW:
            return 4;
          case ID_INS_LD:
          case ID_INS_SD:
            return 8;
          default:
            return 0;
        }
      }

    }; /* riscv namespace */
  }; /* arch namespace */
}; /* triton namespace */
