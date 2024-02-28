//
//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_RISCVSPECIFICATIONS_H
#define TRITON_RISCVSPECIFICATIONS_H

#include <unordered_map>
#include <string>

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

    //! The RISCV namespace
    namespace riscv {
    /*!
     *  \ingroup arch
     *  \addtogroup riscv
     *  @{
     */

      //! \class riscvSpecifications
      /*! \brief The riscvSpecifications class defines specifications about the RV32 and RV64 CPU */
      class riscvSpecifications {
        protected:
          //! List of registers specification available for this architecture.
          std::unordered_map<triton::arch::register_e, const triton::arch::Register> id2reg;
          std::unordered_map<std::string, triton::arch::register_e> name2id;

        public:
          //! Constructor.
          TRITON_EXPORT riscvSpecifications(triton::arch::architecture_e);

          //! Converts a capstone's register id to a triton's register id for RV64.
          TRITON_EXPORT triton::arch::register_e capstoneRegisterToTritonRegister64(triton::uint32 id) const;

          //! Converts a capstone's register id to a triton's register id for RV32.
          TRITON_EXPORT triton::arch::register_e capstoneRegisterToTritonRegister32(triton::uint32 id) const;

          //! Converts a capstone's instruction id to a triton's instruction id.
          TRITON_EXPORT triton::uint32 capstoneInstructionToTritonInstruction(triton::uint32 id) const;

          //! Converts a capstone's group id to a triton's group id.
          TRITON_EXPORT triton::arch::riscv::insn_group_e capstoneGroupToTritonGroup(triton::uint32 id) const;

          //! Returns memory access size if it is specified by instruction.
          TRITON_EXPORT triton::uint32 getMemoryOperandSpecialSize(triton::uint32 id) const;
      };

      //! RISCV NOP instruction -- ADDI x0, x0, 0
      const triton::arch::Instruction nop = triton::arch::Instruction("\x13\x00\x00\x00", 4);

      //! The list of opcodes.
      enum instruction_e {
        ID_INS_INVALID = 0,

        ID_INS_ADD,
        ID_INS_ADDI,
        ID_INS_ADDIW,
        ID_INS_ADDW,
        ID_INS_AMOADD_D,
        ID_INS_AMOADD_D_AQ,
        ID_INS_AMOADD_D_AQ_RL,
        ID_INS_AMOADD_D_RL,
        ID_INS_AMOADD_W,
        ID_INS_AMOADD_W_AQ,
        ID_INS_AMOADD_W_AQ_RL,
        ID_INS_AMOADD_W_RL,
        ID_INS_AMOAND_D,
        ID_INS_AMOAND_D_AQ,
        ID_INS_AMOAND_D_AQ_RL,
        ID_INS_AMOAND_D_RL,
        ID_INS_AMOAND_W,
        ID_INS_AMOAND_W_AQ,
        ID_INS_AMOAND_W_AQ_RL,
        ID_INS_AMOAND_W_RL,
        ID_INS_AMOMAXU_D,
        ID_INS_AMOMAXU_D_AQ,
        ID_INS_AMOMAXU_D_AQ_RL,
        ID_INS_AMOMAXU_D_RL,
        ID_INS_AMOMAXU_W,
        ID_INS_AMOMAXU_W_AQ,
        ID_INS_AMOMAXU_W_AQ_RL,
        ID_INS_AMOMAXU_W_RL,
        ID_INS_AMOMAX_D,
        ID_INS_AMOMAX_D_AQ,
        ID_INS_AMOMAX_D_AQ_RL,
        ID_INS_AMOMAX_D_RL,
        ID_INS_AMOMAX_W,
        ID_INS_AMOMAX_W_AQ,
        ID_INS_AMOMAX_W_AQ_RL,
        ID_INS_AMOMAX_W_RL,
        ID_INS_AMOMINU_D,
        ID_INS_AMOMINU_D_AQ,
        ID_INS_AMOMINU_D_AQ_RL,
        ID_INS_AMOMINU_D_RL,
        ID_INS_AMOMINU_W,
        ID_INS_AMOMINU_W_AQ,
        ID_INS_AMOMINU_W_AQ_RL,
        ID_INS_AMOMINU_W_RL,
        ID_INS_AMOMIN_D,
        ID_INS_AMOMIN_D_AQ,
        ID_INS_AMOMIN_D_AQ_RL,
        ID_INS_AMOMIN_D_RL,
        ID_INS_AMOMIN_W,
        ID_INS_AMOMIN_W_AQ,
        ID_INS_AMOMIN_W_AQ_RL,
        ID_INS_AMOMIN_W_RL,
        ID_INS_AMOOR_D,
        ID_INS_AMOOR_D_AQ,
        ID_INS_AMOOR_D_AQ_RL,
        ID_INS_AMOOR_D_RL,
        ID_INS_AMOOR_W,
        ID_INS_AMOOR_W_AQ,
        ID_INS_AMOOR_W_AQ_RL,
        ID_INS_AMOOR_W_RL,
        ID_INS_AMOSWAP_D,
        ID_INS_AMOSWAP_D_AQ,
        ID_INS_AMOSWAP_D_AQ_RL,
        ID_INS_AMOSWAP_D_RL,
        ID_INS_AMOSWAP_W,
        ID_INS_AMOSWAP_W_AQ,
        ID_INS_AMOSWAP_W_AQ_RL,
        ID_INS_AMOSWAP_W_RL,
        ID_INS_AMOXOR_D,
        ID_INS_AMOXOR_D_AQ,
        ID_INS_AMOXOR_D_AQ_RL,
        ID_INS_AMOXOR_D_RL,
        ID_INS_AMOXOR_W,
        ID_INS_AMOXOR_W_AQ,
        ID_INS_AMOXOR_W_AQ_RL,
        ID_INS_AMOXOR_W_RL,
        ID_INS_AND,
        ID_INS_ANDI,
        ID_INS_AUIPC,
        ID_INS_BEQ,
        ID_INS_BGE,
        ID_INS_BGEU,
        ID_INS_BLT,
        ID_INS_BLTU,
        ID_INS_BNE,
        ID_INS_CSRRC,
        ID_INS_CSRRCI,
        ID_INS_CSRRS,
        ID_INS_CSRRSI,
        ID_INS_CSRRW,
        ID_INS_CSRRWI,
        /* Compressed instructions */
        ID_INS_C_ADD,
        ID_INS_C_ADDI,
        ID_INS_C_ADDI16SP,
        ID_INS_C_ADDI4SPN,
        ID_INS_C_ADDIW,
        ID_INS_C_ADDW,
        ID_INS_C_AND,
        ID_INS_C_ANDI,
        ID_INS_C_BEQZ,
        ID_INS_C_BNEZ,
        ID_INS_C_EBREAK,
        ID_INS_C_FLD,
        ID_INS_C_FLDSP,
        ID_INS_C_FLW,
        ID_INS_C_FLWSP,
        ID_INS_C_FSD,
        ID_INS_C_FSDSP,
        ID_INS_C_FSW,
        ID_INS_C_FSWSP,
        ID_INS_C_J,
        ID_INS_C_JAL,
        ID_INS_C_JALR,
        ID_INS_C_JR,
        ID_INS_C_LD,
        ID_INS_C_LDSP,
        ID_INS_C_LI,
        ID_INS_C_LUI,
        ID_INS_C_LW,
        ID_INS_C_LWSP,
        ID_INS_C_MV,
        ID_INS_C_NOP,
        ID_INS_C_OR,
        ID_INS_C_SD,
        ID_INS_C_SDSP,
        ID_INS_C_SLLI,
        ID_INS_C_SRAI,
        ID_INS_C_SRLI,
        ID_INS_C_SUB,
        ID_INS_C_SUBW,
        ID_INS_C_SW,
        ID_INS_C_SWSP,
        ID_INS_C_UNIMP,
        ID_INS_C_XOR,
        /* End of compressed instructions */
        ID_INS_DIV,
        ID_INS_DIVU,
        ID_INS_DIVUW,
        ID_INS_DIVW,
        ID_INS_EBREAK,
        ID_INS_ECALL,
        ID_INS_FADD_D,
        ID_INS_FADD_S,
        ID_INS_FCLASS_D,
        ID_INS_FCLASS_S,
        ID_INS_FCVT_D_L,
        ID_INS_FCVT_D_LU,
        ID_INS_FCVT_D_S,
        ID_INS_FCVT_D_W,
        ID_INS_FCVT_D_WU,
        ID_INS_FCVT_LU_D,
        ID_INS_FCVT_LU_S,
        ID_INS_FCVT_L_D,
        ID_INS_FCVT_L_S,
        ID_INS_FCVT_S_D,
        ID_INS_FCVT_S_L,
        ID_INS_FCVT_S_LU,
        ID_INS_FCVT_S_W,
        ID_INS_FCVT_S_WU,
        ID_INS_FCVT_WU_D,
        ID_INS_FCVT_WU_S,
        ID_INS_FCVT_W_D,
        ID_INS_FCVT_W_S,
        ID_INS_FDIV_D,
        ID_INS_FDIV_S,
        ID_INS_FENCE,
        ID_INS_FENCE_I,
        ID_INS_FENCE_TSO,
        ID_INS_FEQ_D,
        ID_INS_FEQ_S,
        ID_INS_FLD,
        ID_INS_FLE_D,
        ID_INS_FLE_S,
        ID_INS_FLT_D,
        ID_INS_FLT_S,
        ID_INS_FLW,
        ID_INS_FMADD_D,
        ID_INS_FMADD_S,
        ID_INS_FMAX_D,
        ID_INS_FMAX_S,
        ID_INS_FMIN_D,
        ID_INS_FMIN_S,
        ID_INS_FMSUB_D,
        ID_INS_FMSUB_S,
        ID_INS_FMUL_D,
        ID_INS_FMUL_S,
        ID_INS_FMV_D_X,
        ID_INS_FMV_W_X,
        ID_INS_FMV_X_D,
        ID_INS_FMV_X_W,
        ID_INS_FNMADD_D,
        ID_INS_FNMADD_S,
        ID_INS_FNMSUB_D,
        ID_INS_FNMSUB_S,
        ID_INS_FSD,
        ID_INS_FSGNJN_D,
        ID_INS_FSGNJN_S,
        ID_INS_FSGNJX_D,
        ID_INS_FSGNJX_S,
        ID_INS_FSGNJ_D,
        ID_INS_FSGNJ_S,
        ID_INS_FSQRT_D,
        ID_INS_FSQRT_S,
        ID_INS_FSUB_D,
        ID_INS_FSUB_S,
        ID_INS_FSW,
        ID_INS_JAL,
        ID_INS_JALR,
        ID_INS_LB,
        ID_INS_LBU,
        ID_INS_LD,
        ID_INS_LH,
        ID_INS_LHU,
        ID_INS_LR_D,
        ID_INS_LR_D_AQ,
        ID_INS_LR_D_AQ_RL,
        ID_INS_LR_D_RL,
        ID_INS_LR_W,
        ID_INS_LR_W_AQ,
        ID_INS_LR_W_AQ_RL,
        ID_INS_LR_W_RL,
        ID_INS_LUI,
        ID_INS_LW,
        ID_INS_LWU,
        ID_INS_MRET,
        ID_INS_MUL,
        ID_INS_MULH,
        ID_INS_MULHSU,
        ID_INS_MULHU,
        ID_INS_MULW,
        ID_INS_OR,
        ID_INS_ORI,
        ID_INS_REM,
        ID_INS_REMU,
        ID_INS_REMUW,
        ID_INS_REMW,
        ID_INS_SB,
        ID_INS_SC_D,
        ID_INS_SC_D_AQ,
        ID_INS_SC_D_AQ_RL,
        ID_INS_SC_D_RL,
        ID_INS_SC_W,
        ID_INS_SC_W_AQ,
        ID_INS_SC_W_AQ_RL,
        ID_INS_SC_W_RL,
        ID_INS_SD,
        ID_INS_SFENCE_VMA,
        ID_INS_SH,
        ID_INS_SLL,
        ID_INS_SLLI,
        ID_INS_SLLIW,
        ID_INS_SLLW,
        ID_INS_SLT,
        ID_INS_SLTI,
        ID_INS_SLTIU,
        ID_INS_SLTU,
        ID_INS_SRA,
        ID_INS_SRAI,
        ID_INS_SRAIW,
        ID_INS_SRAW,
        ID_INS_SRET,
        ID_INS_SRL,
        ID_INS_SRLI,
        ID_INS_SRLIW,
        ID_INS_SRLW,
        ID_INS_SUB,
        ID_INS_SUBW,
        ID_INS_SW,
        ID_INS_UNIMP,
        ID_INS_URET,
        ID_INS_WFI,
        ID_INS_XOR,
        ID_INS_XORI,

        ID_INS_ENDING, //!
      };

    /*! @} End of RISCV namespace */
    };
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_RISCVSPECIFICATIONS_H */
