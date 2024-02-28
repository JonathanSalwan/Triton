//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_RISCVSEMANTICS_H
#define TRITON_RISCVSEMANTICS_H

#include <triton/archEnums.hpp>
#include <triton/architecture.hpp>
#include <triton/dllexport.hpp>
#include <triton/instruction.hpp>
#include <triton/modes.hpp>
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
    namespace riscv {
    /*!
     *  \ingroup arch
     *  \addtogroup riscv
     *  @{
     */

      /*! \class riscvSemantics
          \brief The RISCV ISA semantics. */
      class riscvSemantics : public SemanticsInterface {
        private:
          //! Architecture API
          triton::arch::Architecture* architecture;

          //! Symbolic Engine API
          triton::engines::symbolic::SymbolicEngine* symbolicEngine;

          //! Taint Engine API
          triton::engines::taint::TaintEngine* taintEngine;

          //! The Modes API
          triton::modes::SharedModes modes;

          //! The AST Context API
          triton::ast::SharedAstContext astCtxt;

          //! Exception status
          triton::arch::exception_e exception;

        public:
          //! Constructor.
          TRITON_EXPORT riscvSemantics(triton::arch::Architecture* architecture,
                                     triton::engines::symbolic::SymbolicEngine* symbolicEngine,
                                     triton::engines::taint::TaintEngine* taintEngine,
                                     const triton::modes::SharedModes& modes,
                                     const triton::ast::SharedAstContext& astCtxt);

          //! Builds the semantics of the instruction. Returns `triton::arch::NO_FAULT` if succeed.
          TRITON_EXPORT triton::arch::exception_e buildSemantics(triton::arch::Instruction& inst);

        private:
          //! Control flow semantics. Used to represent PC.
          void controlFlow_s(triton::arch::Instruction& inst);

           //! The ADD semantics.
          void add_s(triton::arch::Instruction& inst);

          //! The ADDI semantics.
          void addi_s(triton::arch::Instruction& inst);

          //! The MV (ADDI pseudo instruction) semantics.
          void addi_mv_s(triton::arch::Instruction& inst);

          //! The ADDIW semantics.
          void addiw_s(triton::arch::Instruction& inst);

          //! The ADDW semantics.
          void addw_s(triton::arch::Instruction& inst);

          //! The AND semantics.
          void and_s(triton::arch::Instruction& inst);

          //! The ANDI semantics.
          void andi_s(triton::arch::Instruction& inst);

          //! The AUIPC semantics.
          void auipc_s(triton::arch::Instruction& inst);

          //! The BEQ semantics.
          void beq_s(triton::arch::Instruction& inst);

          //! The BGE semantics.
          void bge_s(triton::arch::Instruction& inst);

          //! The BGEU semantics.
          void bgeu_s(triton::arch::Instruction& inst);

          //! The BLT semantics.
          void blt_s(triton::arch::Instruction& inst);

          //! The BLTU semantics.
          void bltu_s(triton::arch::Instruction& inst);

          //! The BNE semantics.
          void bne_s(triton::arch::Instruction& inst);

           //! The compressed ADD semantics.
          void c_add_s(triton::arch::Instruction& inst);

           //! The compressed ADDI semantics.
          void c_addi_s(triton::arch::Instruction& inst);

           //! The compressed ADDI16SP semantics.
          void c_addi16sp_s(triton::arch::Instruction& inst);

           //! The compressed ADDI4SPN semantics.
          void c_addi4spn_s(triton::arch::Instruction& inst);

           //! The compressed ADDIW semantics.
          void c_addiw_s(triton::arch::Instruction& inst);

           //! The compressed ADDW semantics.
          void c_addw_s(triton::arch::Instruction& inst);

           //! The compressed AND semantics.
          void c_and_s(triton::arch::Instruction& inst);

           //! The compressed ANDI semantics.
          void c_andi_s(triton::arch::Instruction& inst);

           //! The compressed BEQZ semantics.
          void c_beqz_s(triton::arch::Instruction& inst);

           //! The compressed BNEZ semantics.
          void c_bnez_s(triton::arch::Instruction& inst);

           //! The compressed JAL semantics.
          void c_jal_s(triton::arch::Instruction& inst);

           //! The compressed JALR semantics.
          void c_jalr_s(triton::arch::Instruction& inst);

           //! The compressed LD semantics.
          void c_ld_s(triton::arch::Instruction& inst);

           //! The compressed LDSP semantics.
          void c_ldsp_s(triton::arch::Instruction& inst);

           //! The compressed LI semantics.
          void c_li_s(triton::arch::Instruction& inst);

           //! The compressed LW semantics.
          void c_lw_s(triton::arch::Instruction& inst);

           //! The compressed LWSP semantics.
          void c_lwsp_s(triton::arch::Instruction& inst);

           //! The compressed MV semantics.
          void c_mv_s(triton::arch::Instruction& inst);

           //! The compressed NOP semantics.
          void c_nop_s(triton::arch::Instruction& inst);

           //! The compressed OR semantics.
          void c_or_s(triton::arch::Instruction& inst);

           //! The compressed SD semantics.
          void c_sd_s(triton::arch::Instruction& inst);

           //! The compressed SDSP semantics.
          void c_sdsp_s(triton::arch::Instruction& inst);

           //! The compressed SLLI semantics.
          void c_slli_s(triton::arch::Instruction& inst);

           //! The compressed SRAI semantics.
          void c_srai_s(triton::arch::Instruction& inst);

           //! The compressed SRLI semantics.
          void c_srli_s(triton::arch::Instruction& inst);

           //! The compressed SUB semantics.
          void c_sub_s(triton::arch::Instruction& inst);

           //! The compressed SUBW semantics.
          void c_subw_s(triton::arch::Instruction& inst);

           //! The compressed SW semantics.
          void c_sw_s(triton::arch::Instruction& inst);

           //! The compressed SWSP semantics.
          void c_swsp_s(triton::arch::Instruction& inst);

           //! The compressed XOR semantics.
          void c_xor_s(triton::arch::Instruction& inst);

          //! The DIV semantics.
          void div_s(triton::arch::Instruction& inst);

          //! The DIVU semantics.
          void divu_s(triton::arch::Instruction& inst);

          //! The DIVUW semantics.
          void divuw_s(triton::arch::Instruction& inst);

          //! The DIVW semantics.
          void divw_s(triton::arch::Instruction& inst);

          //! The JAL semantics.
          void jal_s(triton::arch::Instruction& inst);

          //! The J (JAL pseudo instruction) semantics.
          void jal_j_s(triton::arch::Instruction& inst);

          //! The JALR semantics.
          void jalr_s(triton::arch::Instruction& inst);

          //! The RET/JR (JALR pseudo instruction) semantics.
          void jalr_no_link_s(triton::arch::Instruction& inst);

          //! The LB semantics.
          void lb_s(triton::arch::Instruction& inst);

          //! The LBU semantics.
          void lbu_s(triton::arch::Instruction& inst);

          //! The LD semantics.
          void ld_s(triton::arch::Instruction& inst);

          //! The LH semantics.
          void lh_s(triton::arch::Instruction& inst);

          //! The LHU semantics.
          void lhu_s(triton::arch::Instruction& inst);

          //! The LUI semantics.
          void lui_s(triton::arch::Instruction& inst);

          //! The LW semantics.
          void lw_s(triton::arch::Instruction& inst);

          //! The LWU semantics.
          void lwu_s(triton::arch::Instruction& inst);

          //! The MUL semantics.
          void mul_s(triton::arch::Instruction& inst);

          //! The MULH semantics.
          void mulh_s(triton::arch::Instruction& inst);

          //! The MULHSU semantics.
          void mulhsu_s(triton::arch::Instruction& inst);

          //! The MULHU semantics.
          void mulhu_s(triton::arch::Instruction& inst);

          //! The MULW semantics.
          void mulw_s(triton::arch::Instruction& inst);

          //! The OR semantics.
          void or_s(triton::arch::Instruction& inst);

          //! The ORI semantics.
          void ori_s(triton::arch::Instruction& inst);

          //! The REM semantics.
          void rem_s(triton::arch::Instruction& inst);

          //! The REMU semantics.
          void remu_s(triton::arch::Instruction& inst);

          //! The REMUW semantics.
          void remuw_s(triton::arch::Instruction& inst);

          //! The REMW semantics.
          void remw_s(triton::arch::Instruction& inst);

          //! The SB semantics.
          void sb_s(triton::arch::Instruction& inst);

          //! The SD semantics.
          void sd_s(triton::arch::Instruction& inst);

          //! The SH semantics.
          void sh_s(triton::arch::Instruction& inst);

          //! The SLL semantics.
          void sll_s(triton::arch::Instruction& inst);

          //! The SLLI semantics.
          void slli_s(triton::arch::Instruction& inst);

          //! The SLLIW semantics.
          void slliw_s(triton::arch::Instruction& inst);

          //! The SLLW semantics.
          void sllw_s(triton::arch::Instruction& inst);

          //! The SLT semantics.
          void slt_s(triton::arch::Instruction& inst);

          //! The SGTZ (SLT pseudo instruction) semantics.
          void slt_sgtz_s(triton::arch::Instruction& inst);

          //! The SLTZ (SLT pseudo instruction) semantics.
          void slt_sltz_s(triton::arch::Instruction& inst);

          //! The SLTI semantics.
          void slti_s(triton::arch::Instruction& inst);

          //! The SLTIU semantics.
          void sltiu_s(triton::arch::Instruction& inst);

          //! The The SEQZ (SLTIU pseudo instruction) semantics.
          void sltiu_seqz_s(triton::arch::Instruction& inst);

          //! The SLTU semantics.
          void sltu_s(triton::arch::Instruction& inst);

          //! The The SNEZ (SLTU pseudo instruction) semantics.
          void sltu_snez_s(triton::arch::Instruction& inst);

          //! The SRA semantics.
          void sra_s(triton::arch::Instruction& inst);

          //! The SRAI semantics.
          void srai_s(triton::arch::Instruction& inst);

          //! The SRAIW semantics.
          void sraiw_s(triton::arch::Instruction& inst);

          //! The SRAW semantics.
          void sraw_s(triton::arch::Instruction& inst);

          //! The SRL semantics.
          void srl_s(triton::arch::Instruction& inst);

          //! The SRLI semantics.
          void srli_s(triton::arch::Instruction& inst);

          //! The SRLIW semantics.
          void srliw_s(triton::arch::Instruction& inst);

          //! The SRLW semantics.
          void srlw_s(triton::arch::Instruction& inst);

          //! The SUB semantics.
          void sub_s(triton::arch::Instruction& inst);

          //! The SUBW semantics.
          void subw_s(triton::arch::Instruction& inst);

          //! The SW semantics.
          void sw_s(triton::arch::Instruction& inst);

          //! The XOR semantics.
          void xor_s(triton::arch::Instruction& inst);

          //! The XORI semantics.
          void xori_s(triton::arch::Instruction& inst);
      };

    /*! @} End of riscv namespace */
    };
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_RISCVSEMANTICS_H */

