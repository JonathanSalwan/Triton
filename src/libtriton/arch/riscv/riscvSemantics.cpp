//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <triton/cpuSize.hpp>
#include <triton/exceptions.hpp>
#include <triton/riscvSemantics.hpp>
#include <triton/riscvSpecifications.hpp>
#include <triton/astContext.hpp>



/*! \page SMT_Semantics_Supported_page SMT Semantics Supported
    \brief [**internal**] All information about the supported semantics.

- \ref SMT_aarch64_Semantics_Supported_page
- \ref SMT_arm32_Semantics_Supported_page
- \ref SMT_riscv_Semantics_Supported_page
- \ref SMT_x86_Semantics_Supported_page

*/


/*! \page SMT_riscv_Semantics_Supported_page RV32 and RV64 SMT semantics supported
    \brief [**internal**] List of the supported semantics for the RV32 and RV64 architectures.


Mnemonic                      | Description
------------------------------|------------
ADD                           | Add (register)
ADDI  (pseudo: MV, NOP)       | Add (immediate)
ADDIW (pseudo: SEXT.W)        | Add word (immediate) / 64-bit only /
ADDW                          | Add word (register) / 64-bit only /
AND                           | And (register)
ANDI                          | And (immediate)
AUIPC                         | Add upper intermediate to pc
BEQ   (pseudo: BEQZ)          | Branch if equal
BGE   (pseudo: BLEZ, BGEZ)    | Branch if greater or equal
BGEU                          | Branch if greater or equal (unsigned)
BLT   (pseudo: BLTZ, BGTZ)    | Branch if less
BLTU                          | Branch if less (unsigned)
BNE   (pseudo: BNEZ)          | Branch if not equal
DIV                           | Signed integer division
DIVU                          | Unsigned integer division
DIVUW                         | Word unsigned integer division / 64-bit only /
DIVW                          | Word signed integer division / 64-bit only /
JAL   (pseudo: J)             | Jump and link
JALR  (pseudo: JR, RET)       | Jump and link register
LB                            | Load register signed byte
LBU                           | Load register unsigned byte
LD                            | Load register double word / 64-bit only /
LH                            | Load register signed halfword
LHU                           | Load register unsigned halfword
LUI                           | Load upper intermediate
LW                            | Load register signed word
LWU                           | Load register unsigned word / 64-bit only /
MUL                           | Signed multiply
MULH                          | Signed multiply high
MULHSU                        | Signed-unsigned multiply high
MULHU                         | Unsigned multiply high
MULW                          | Word multiply / 64-bit only /
OR                            | Or (register)
ORI                           | Or (immediate)
REM                           | Signed integer reminder
REMU                          | Unsigned integer reminder
REMUW                         | Word unsigned integer reminder / 64-bit only /
REMW                          | Word signed integer reminder / 64-bit only /
SB                            | Store register byte
SD                            | Store register double word  / 64-bit only /
SH                            | Store register halfword
SLL                           | Logical left shift (register)
SLLI                          | Logical left shift (immediate)
SLLIW                         | Word logical left shift (immediate) / 64-bit only /
SLLW                          | Word logical left shift (register)
SLT   (pseudo: SLTZ, SGTZ)    | Set if less than register
SLTI                          | Set if less than immediate
SLTIU (pseudo: SEQZ)          | Set if less than immediate (unsigned)
SLTU  (pseudo: SNEZ)          | Set if less than register (unsigned)
SRA                           | Arithmetic right shift (register)
SRAI                          | Arithmetic right shift (immediate)
SRAIW                         | Word arithmetic right shift (register) / 64-bit only /
SRAW                          | Word arithmetic right shift (immediate) / 64-bit only /
SRL                           | Logical right shift (register)
SRLI                          | Logical right shift (immediate)
SRLIW                         | Word logical right shift (register) / 64-bit only /
SRLW                          | Word logical right shift (immediate) / 64-bit only /
SUB   (pseudo: NEG)           | Subtract
SUBW  (pseudo: NEGW)          | Subtract word / 64-bit only /
SW                            | Store register word
XOR                           | Exclusive or (register)
XORI (pseudo: NOT)            | Exclusive or (immediate)
------------------------------|------------
                    Compressed instructions
------------------------------|------------
C.ADD                         | Add (register)
C.ADDI                        | Add (immediate)
C.ADDI16SP                    | Add to SP (immediate, multiplied by 16)
C.ADDI4SPN                    | Add to SP (immediate, multiplied by 4)
C.ADDIW                       | Add word (immediate) / 64-bit only /
C.ADDW                        | Add word (register) / 64-bit only /
C.AND                         | And (register)
C.ANDI                        | And (immediate)
C.BEQZ                        | Branch if equal to zero
C.BNEZ                        | Branch if not equal to zero
C.J                           | Jump
C.JAL                         | Jump and link / 32-bit only /
C.JALR                        | Jump and link register
C.JR                          | Jump register
C.LD                          | Load register double word / 64-bit only /
C.LDSP                        | Load register double word from SP / 64-bit only /
C.LI                          | Load immediate
C.LUI                         | Load upper intermediate
C.LW                          | Load register signed word
C.LWSP                        | Load register word from SP / 64-bit only /
C.MV                          | Move register
C.NOP                         | No operation
C.OR                          | Or (register)
C.SD                          | Store register double word  / 64-bit only /
C.SDSP                        | Store register double word to SP / 64-bit only /
C.SLLI                        | Logical left shift (immediate)
C.SRAI                        | Arithmetic right shift (immediate)
C.SRLI                        | Logical right shift (immediate)
C.SUB                         | Subtract
C.SUBW                        | Subtract word / 64-bit only /
C.SW                          | Store register word
C.SWSP                        | Store register word to SP
C.XOR                         | Exclusive or (register)

*/


namespace triton {
  namespace arch {
    namespace riscv {

      riscvSemantics::riscvSemantics(triton::arch::Architecture* architecture,
                                 triton::engines::symbolic::SymbolicEngine* symbolicEngine,
                                 triton::engines::taint::TaintEngine* taintEngine,
                                 const triton::modes::SharedModes& modes,
                                 const triton::ast::SharedAstContext& astCtxt) : modes(modes), astCtxt(astCtxt) {

        this->architecture    = architecture;
        this->exception       = triton::arch::NO_FAULT;
        this->symbolicEngine  = symbolicEngine;
        this->taintEngine     = taintEngine;

        if (architecture == nullptr)
          throw triton::exceptions::Semantics("riscvSemantics::riscvSemantics(): The architecture API must be defined.");

        if (this->symbolicEngine == nullptr)
          throw triton::exceptions::Semantics("riscvSemantics::riscvSemantics(): The symbolic engine API must be defined.");

        if (this->taintEngine == nullptr)
          throw triton::exceptions::Semantics("riscvSemantics::riscvSemantics(): The taint engines API must be defined.");
      }


      triton::arch::exception_e riscvSemantics::buildSemantics(triton::arch::Instruction& inst) {
        this->exception = triton::arch::NO_FAULT;
        switch (inst.getType()) {
          case ID_INS_ADD:            this->add_s(inst);          break;
          case ID_INS_ADDI:           this->addi_s(inst);         break;
          case ID_INS_ADDIW:          this->addiw_s(inst);        break;
          case ID_INS_ADDW:           this->addw_s(inst);         break;
          case ID_INS_AND:            this->and_s(inst);          break;
          case ID_INS_ANDI:           this->and_s(inst);          break;
          case ID_INS_AUIPC:          this->auipc_s(inst);        break;
          case ID_INS_BEQ:            this->beq_s(inst);          break;
          case ID_INS_BGE:            this->bge_s(inst);          break;
          case ID_INS_BGEU:           this->bgeu_s(inst);         break;
          case ID_INS_BLT:            this->blt_s(inst);          break;
          case ID_INS_BLTU:           this->bltu_s(inst);         break;
          case ID_INS_BNE:            this->bne_s(inst);          break;
          /* Compressed instructions */
          case ID_INS_C_ADD:          this->c_add_s(inst);        break;
          case ID_INS_C_ADDI:         this->c_add_s(inst);        break;
          case ID_INS_C_ADDI16SP:     this->c_addi16sp_s(inst);   break;
          case ID_INS_C_ADDI4SPN:     this->c_addi4spn_s(inst);   break;
          case ID_INS_C_ADDIW:        this->c_addw_s(inst);       break;
          case ID_INS_C_ADDW:         this->c_addw_s(inst);       break;
          case ID_INS_C_AND:          this->c_and_s(inst);        break;
          case ID_INS_C_ANDI:         this->c_and_s(inst);        break;
          case ID_INS_C_BEQZ:         this->c_beqz_s(inst);       break;
          case ID_INS_C_BNEZ:         this->c_bnez_s(inst);       break;
          case ID_INS_C_J:            this->jal_j_s(inst);        break;
          case ID_INS_C_JAL:          this->c_jal_s(inst);        break;
          case ID_INS_C_JALR:         this->c_jalr_s(inst);       break;
          case ID_INS_C_JR:           this->jalr_no_link_s(inst); break;
          case ID_INS_C_LD:           this->c_ld_s(inst);         break;
          case ID_INS_C_LDSP:         this->c_ldsp_s(inst);       break;
          case ID_INS_C_LI:           this->c_li_s(inst);         break;
          case ID_INS_C_LW:           this->c_lw_s(inst);         break;
          case ID_INS_C_LWSP:         this->c_lwsp_s(inst);       break;
          case ID_INS_C_LUI:          this->lui_s(inst);          break;
          case ID_INS_C_MV:           this->c_mv_s(inst);         break;
          case ID_INS_C_NOP:          this->c_nop_s(inst);        break;
          case ID_INS_C_OR:           this->c_or_s(inst);         break;
          case ID_INS_C_SD:           this->c_sd_s(inst);         break;
          case ID_INS_C_SDSP:         this->c_sdsp_s(inst);       break;
          case ID_INS_C_SLLI:         this->c_slli_s(inst);       break;
          case ID_INS_C_SRAI:         this->c_srai_s(inst);       break;
          case ID_INS_C_SRLI:         this->c_srli_s(inst);       break;
          case ID_INS_C_SUB:          this->c_sub_s(inst);        break;
          case ID_INS_C_SUBW:         this->c_subw_s(inst);       break;
          case ID_INS_C_SW:           this->c_sw_s(inst);         break;
          case ID_INS_C_SWSP:         this->c_swsp_s(inst);       break;
          case ID_INS_C_XOR:          this->c_xor_s(inst);        break;
          /* End of compressed instructions */
          case ID_INS_DIV:            this->div_s(inst);          break;
          case ID_INS_DIVU:           this->divu_s(inst);         break;
          case ID_INS_DIVUW:          this->divuw_s(inst);        break;
          case ID_INS_DIVW:           this->divw_s(inst);         break;
          case ID_INS_JAL:            this->jal_s(inst);          break;
          case ID_INS_JALR:           this->jalr_s(inst);         break;
          case ID_INS_LB:             this->lb_s(inst);           break;
          case ID_INS_LBU:            this->lbu_s(inst);          break;
          case ID_INS_LD:             this->ld_s(inst);           break;
          case ID_INS_LH:             this->lh_s(inst);           break;
          case ID_INS_LHU:            this->lhu_s(inst);          break;
          case ID_INS_LUI:            this->lui_s(inst);          break;
          case ID_INS_LW:             this->lw_s(inst);           break;
          case ID_INS_LWU:            this->lwu_s(inst);          break;
          case ID_INS_MUL:            this->mul_s(inst);          break;
          case ID_INS_MULH:           this->mulh_s(inst);         break;
          case ID_INS_MULHSU:         this->mulhsu_s(inst);       break;
          case ID_INS_MULHU:          this->mulhu_s(inst);        break;
          case ID_INS_MULW:           this->mulw_s(inst);         break;
          case ID_INS_OR:             this->or_s(inst);           break;
          case ID_INS_ORI:            this->or_s(inst);           break;
          case ID_INS_REM:            this->rem_s(inst);          break;
          case ID_INS_REMU:           this->remu_s(inst);         break;
          case ID_INS_REMUW:          this->remuw_s(inst);        break;
          case ID_INS_REMW:           this->remw_s(inst);         break;
          case ID_INS_SB:             this->sb_s(inst);           break;
          case ID_INS_SD:             this->sd_s(inst);           break;
          case ID_INS_SH:             this->sh_s(inst);           break;
          case ID_INS_SLL:            this->sll_s(inst);          break;
          case ID_INS_SLLI:           this->sll_s(inst);          break;
          case ID_INS_SLLIW:          this->sllw_s(inst);         break;
          case ID_INS_SLLW:           this->sllw_s(inst);         break;
          case ID_INS_SLT:            this->slt_s(inst);          break;
          case ID_INS_SLTI:           this->slt_s(inst);          break;
          case ID_INS_SLTIU:          this->sltu_s(inst);         break;
          case ID_INS_SLTU:           this->sltu_s(inst);         break;
          case ID_INS_SRA:            this->sra_s(inst);          break;
          case ID_INS_SRAI:           this->sra_s(inst);          break;
          case ID_INS_SRAIW:          this->sraw_s(inst);         break;
          case ID_INS_SRAW:           this->sraw_s(inst);         break;
          case ID_INS_SRL:            this->srl_s(inst);          break;
          case ID_INS_SRLI:           this->srl_s(inst);          break;
          case ID_INS_SRLIW:          this->srlw_s(inst);         break;
          case ID_INS_SRLW:           this->srlw_s(inst);         break;
          case ID_INS_SUB:            this->sub_s(inst);          break;
          case ID_INS_SUBW:           this->subw_s(inst);         break;
          case ID_INS_SW:             this->sw_s(inst);           break;
          case ID_INS_XOR:            this->xor_s(inst);          break;
          case ID_INS_XORI:           this->xori_s(inst);         break;

          default:
            this->exception = triton::arch::FAULT_UD;
            break;
        }
        return this->exception;
      }


      void riscvSemantics::controlFlow_s(triton::arch::Instruction& inst) {
        auto pc = this->architecture->getProgramCounter();
        auto pc_op = triton::arch::OperandWrapper(pc);

        /* Create the semantics */
        auto node = this->astCtxt->bv(inst.getNextAddress(), pc_op.getBitSize());

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicRegisterExpression(inst, node, pc, "Program Counter");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaintRegister(pc, triton::engines::taint::UNTAINTED);
      }


      void riscvSemantics::add_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt->bvadd(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ADD(I) operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(src1, src2);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::addi_s(triton::arch::Instruction& inst) {
        /* Check for possible pseudo instructions
           mv rd, rs -- [addi rd, rs, 0] -- Copy register
           nop       -- [addi x0, x0, 0] -- No operation
         */
        switch (inst.operands.size()) {
          case 0: this->controlFlow_s(inst); return;  // nop
          case 2: addi_mv_s(inst);  return;           // mv
          default:  add_s(inst);  return;             // addi
        }
      }


      void riscvSemantics::addi_mv_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create the semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MV operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::addiw_s(triton::arch::Instruction& inst) { /* 64-bit only */
        auto& dst = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto  size = dst.getBitSize();

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto node = this->astCtxt->sx(32, this->astCtxt->extract(31, 0, op1));  // sext.w pseudo instruction semantics
        if (inst.operands.size() > 2) {
          auto& src2 = inst.operands[2];
          auto op2 = this->symbolicEngine->getOperandAst(inst, src2);
          node = this->astCtxt->sx(32, this->astCtxt->extract(31, 0, this->astCtxt->bvadd(op1, op2)));
        }

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ADDIW operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::addw_s(triton::arch::Instruction& inst) { /* 64-bit only */
        auto& dst = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt->sx(32, this->astCtxt->bvadd(
                      this->astCtxt->extract(31, 0, op1),
                      this->astCtxt->extract(31, 0, op2)
                    ));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ADDW operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(src1, src2);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::and_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt->bvand(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "AND(I) operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::auipc_s(triton::arch::Instruction& inst) {
        // dst := pc + sx_64(src_imm(_20) << 12)
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  pc = triton::arch::OperandWrapper(this->architecture->getProgramCounter());

        /* Create symbolic operands */
        auto imm = this->symbolicEngine->getOperandAst(inst, src);
        auto pc_ast = this->symbolicEngine->getOperandAst(pc);

        /* Create the semantics */
        auto node = this->astCtxt->concat(this->astCtxt->extract(19, 0, imm), this->astCtxt->bv(0, 12));
        if (dst.getBitSize() == 64) {
          node = this->astCtxt->sx(32, node);
        }
        node = this->astCtxt->bvadd(node, pc_ast);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "AUIPC operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->isTainted(pc);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::beq_s(triton::arch::Instruction& inst) {
        /* Check for possible pseudo instructions
           beqz rs, offset -- [beq rs, x0, offset] -- Branch if == zero
         */
        auto  pc = triton::arch::OperandWrapper(this->architecture->getProgramCounter());
        auto& src1 = inst.operands[0];
        auto& src2 = inst.operands[1];
        auto size = src1.getBitSize();

        /* Create symbolic operands */
        auto pc_ast = this->symbolicEngine->getOperandAst(pc);
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->astCtxt->bv(0, size);
        auto op3 = this->symbolicEngine->getOperandAst(inst, src2);

        if (inst.operands.size() == 3) {
          auto& imm  = inst.operands[2];
          op2 = op3;
          op3 = this->symbolicEngine->getOperandAst(inst, imm);
        }

        /* Create the semantics */
        auto node = this->astCtxt->ite(this->astCtxt->equal(op1, op2),
                      this->astCtxt->bvadd(pc_ast, op3),
                      this->astCtxt->bv(inst.getNextAddress(), pc.getBitSize())
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Set condition flag */
        if (op1->evaluate() == op2->evaluate())
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(pc, src1);
        expr->isTainted = this->taintEngine->taintUnion(pc, src2);

        /* Create the path constraint */
        this->symbolicEngine->pushPathConstraint(inst, expr);
      }


      void riscvSemantics::bge_s(triton::arch::Instruction& inst) {
        /* Check for possible pseudo instructions (no ble in capstone)
           blez rs, offset -- [bge x0, rs, offset] -- Branch if <= zero
           bgez rs, offset -- [bge rs, x0, offset] -- Branch if >= zero
         */
        auto  pc = triton::arch::OperandWrapper(this->architecture->getProgramCounter());
        auto& src1 = inst.operands[0];
        auto& src2 = inst.operands[1];
        auto size = src1.getBitSize();

        /* Create symbolic operands */
        auto pc_ast = this->symbolicEngine->getOperandAst(pc);
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->astCtxt->bv(0, size);
        auto op3 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create branch condition AST */
        bool taken = false;
        auto node = this->astCtxt->bvsge(op1, op2);  // bgez
        if (inst.operands.size() < 3) {
          auto mnem = inst.getDisassembly();
          if (mnem[1] == 'l') {                      // blez
            node = this->astCtxt->bvsle(op1, op2);
            taken = (long long)(op1->evaluate()) <= 0;
          }
          else {
            taken = (long long)(op1->evaluate()) >= 0;
          }
        }
        else {                                       // bge
          auto& imm  = inst.operands[2];
          op2 = op3;
          op3 = this->symbolicEngine->getOperandAst(inst, imm);
          node = this->astCtxt->bvsge(op1, op2);
          taken = (long long)(op1->evaluate() - op2->evaluate()) >= 0;
        }

        /* Create the semantics */
        node = this->astCtxt->ite(node,
                 this->astCtxt->bvadd(pc_ast, op3),
                 this->astCtxt->bv(inst.getNextAddress(), pc.getBitSize())
               );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Set condition flag */
        inst.setConditionTaken(taken);

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(pc, src1);
        expr->isTainted = this->taintEngine->taintUnion(pc, src2);

        /* Create the path constraint */
        this->symbolicEngine->pushPathConstraint(inst, expr);
      }


      void riscvSemantics::bgeu_s(triton::arch::Instruction& inst) {
        auto  pc = triton::arch::OperandWrapper(this->architecture->getProgramCounter());
        auto& src1 = inst.operands[0];
        auto& src2 = inst.operands[1];
        auto& imm  = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);
        auto op3 = this->symbolicEngine->getOperandAst(inst, imm);
        auto pc_ast = this->symbolicEngine->getOperandAst(pc);

        /* Create the semantics */
        auto node = this->astCtxt->ite(this->astCtxt->bvuge(op1, op2),
                      this->astCtxt->bvadd(pc_ast, op3),
                      this->astCtxt->bv(inst.getNextAddress(), pc.getBitSize())
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Set condition flag */
        if (op1->evaluate() >= op2->evaluate())
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(pc, src1);
        expr->isTainted = this->taintEngine->taintUnion(pc, src2);

        /* Create the path constraint */
        this->symbolicEngine->pushPathConstraint(inst, expr);
      }


      void riscvSemantics::blt_s(triton::arch::Instruction& inst) {
        /* Check for possible pseudo instructions (no bgt in capstone)
           bltz rs, offset -- [blt rs, x0, offset] -- Branch if < zero
           bgtz rs, offset -- [blt x0, rs, offset] -- Branch if > zero
         */
        auto  pc = triton::arch::OperandWrapper(this->architecture->getProgramCounter());
        auto& src1 = inst.operands[0];
        auto& src2 = inst.operands[1];
        auto size = src1.getBitSize();

        /* Create symbolic operands */
        auto pc_ast = this->symbolicEngine->getOperandAst(pc);
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->astCtxt->bv(0, size);
        auto op3 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create branch condition AST */
        bool taken = false;
        auto node = this->astCtxt->bvslt(op1, op2);  // bltz
        if (inst.operands.size() < 3) {
          auto mnem = inst.getDisassembly();
          if (mnem[1] == 'g') {                      // bgtz
            node = this->astCtxt->bvsgt(op1, op2);
            taken = (long long)(op1->evaluate()) > 0;
          }
          else {
            taken = (long long)(op1->evaluate()) < 0;
          }
        }
        else {                                       // blt
          auto& imm  = inst.operands[2];
          op2 = op3;
          op3 = this->symbolicEngine->getOperandAst(inst, imm);
          node = this->astCtxt->bvslt(op1, op2);
          taken = (long long)(op1->evaluate() - op2->evaluate()) < 0;
        }

        /* Create the semantics */
        node = this->astCtxt->ite(node,
                 this->astCtxt->bvadd(pc_ast, op3),
                 this->astCtxt->bv(inst.getNextAddress(), pc.getBitSize())
               );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Set condition flag */
        inst.setConditionTaken(taken);

        /* Spread taint */

        expr->isTainted = this->taintEngine->taintUnion(pc, src1);
        expr->isTainted = this->taintEngine->taintUnion(pc, src2);

        /* Create the path constraint */
        this->symbolicEngine->pushPathConstraint(inst, expr);
      }


      void riscvSemantics::bltu_s(triton::arch::Instruction& inst) {
        auto  pc = triton::arch::OperandWrapper(this->architecture->getProgramCounter());
        auto& src1 = inst.operands[0];
        auto& src2 = inst.operands[1];
        auto& imm  = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);
        auto op3 = this->symbolicEngine->getOperandAst(inst, imm);
        auto pc_ast = this->symbolicEngine->getOperandAst(pc);

        /* Create the semantics */
        auto node = this->astCtxt->ite(this->astCtxt->bvult(op1, op2),
                      this->astCtxt->bvadd(pc_ast, op3),
                      this->astCtxt->bv(inst.getNextAddress(), pc.getBitSize())
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Set condition flag */
        if (op2->evaluate() > op1->evaluate())
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(pc, src1);
        expr->isTainted = this->taintEngine->taintUnion(pc, src2);

        /* Create the path constraint */
        this->symbolicEngine->pushPathConstraint(inst, expr);
      }


      void riscvSemantics::bne_s(triton::arch::Instruction& inst) {
        /* Check for possible pseudo instructions
           bnez rs, offset -- [blt rs, x0, offset] -- Branch if != zero
         */
        auto  pc = triton::arch::OperandWrapper(this->architecture->getProgramCounter());
        auto& src1 = inst.operands[0];
        auto& src2 = inst.operands[1];
        auto size = src1.getBitSize();

        /* Create symbolic operands */
        auto pc_ast = this->symbolicEngine->getOperandAst(pc);
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->astCtxt->bv(0, size);
        auto op3 = this->symbolicEngine->getOperandAst(inst, src2);

        if (inst.operands.size() == 3) {
          auto& imm  = inst.operands[2];
          op2 = op3;
          op3 = this->symbolicEngine->getOperandAst(inst, imm);
        }

        /* Create the semantics */
        auto node = this->astCtxt->ite(this->astCtxt->equal(op1, op2),
                      this->astCtxt->bv(inst.getNextAddress(), pc.getBitSize()),
                      this->astCtxt->bvadd(pc_ast, op3)
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Set condition flag */
        if (op1->evaluate() - op2->evaluate())
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(pc, src1);
        expr->isTainted = this->taintEngine->taintUnion(pc, src2);

        /* Create the path constraint */
        this->symbolicEngine->pushPathConstraint(inst, expr);
      }


      // Compressed instructions:
      void riscvSemantics::c_add_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, dst);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node = this->astCtxt->bvadd(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "C.ADD(I) operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::c_addi16sp_s(triton::arch::Instruction& inst) {
        auto& sp  = inst.operands[0];
        auto& imm = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, sp);
        auto op2 = this->symbolicEngine->getOperandAst(inst, imm);

        /* Create the semantics */
        auto node = this->astCtxt->bvadd(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, sp, "C.ADDI16SP operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->isTainted(sp);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::c_addi4spn_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto& imm = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src);
        auto op2 = this->symbolicEngine->getOperandAst(inst, imm);

        /* Create the semantics */
        auto node = this->astCtxt->bvadd(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "C.ADDI4SPN operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::c_addw_s(triton::arch::Instruction& inst) { /* 64-bit only */
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, dst);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node = this->astCtxt->sx(32, this->astCtxt->bvadd(
                      this->astCtxt->extract(31, 0, op1),
                      this->astCtxt->extract(31, 0, op2)
                    ));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "C.ADD(I)W operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::c_and_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, dst);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node = this->astCtxt->bvand(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "C.AND(I) operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::c_beqz_s(triton::arch::Instruction& inst) {
        auto  pc = triton::arch::OperandWrapper(this->architecture->getProgramCounter());
        auto& src1 = inst.operands[0];
        auto& src2 = inst.operands[1];
        auto size = src1.getBitSize();

        /* Create symbolic operands */
        auto pc_ast = this->symbolicEngine->getOperandAst(pc);
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->astCtxt->bv(0, size);
        auto op3 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt->ite(this->astCtxt->equal(op1, op2),
                      this->astCtxt->bvadd(pc_ast, op3),
                      this->astCtxt->bv(inst.getNextAddress(), pc.getBitSize())
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Set condition flag */
        if (op1->evaluate() == 0)
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(pc, src1);

        /* Create the path constraint */
        this->symbolicEngine->pushPathConstraint(inst, expr);
      }


      void riscvSemantics::c_bnez_s(triton::arch::Instruction& inst) {
        auto  pc = triton::arch::OperandWrapper(this->architecture->getProgramCounter());
        auto& src1 = inst.operands[0];
        auto& src2 = inst.operands[1];
        auto size = src1.getBitSize();

        /* Create symbolic operands */
        auto pc_ast = this->symbolicEngine->getOperandAst(pc);
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->astCtxt->bv(0, size);
        auto op3 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt->ite(this->astCtxt->equal(op1, op2),
                      this->astCtxt->bv(inst.getNextAddress(), pc.getBitSize()),
                      this->astCtxt->bvadd(pc_ast, op3)
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Set condition flag */
        if (op1->evaluate() != 0)
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(pc, src1);

        /* Create the path constraint */
        this->symbolicEngine->pushPathConstraint(inst, expr);
      }


      void riscvSemantics::c_jal_s(triton::arch::Instruction& inst) { /* 32-bit only */
        /* x1 := pc + 2; pc := pc + offset
           Compressed instruction expands to:
           jal offset -- [jal x1, offset] -- Jump and link
         */
        auto pc = triton::arch::OperandWrapper(this->architecture->getProgramCounter());
        auto size = pc.getBitSize();
        auto& src = inst.operands[0];
        auto ra = this->architecture->getRegister(triton::arch::ID_REG_RV32_X1);
        auto reg = triton::arch::OperandWrapper(ra);

        /* Create symbolic operands */
        auto pc_ast = this->symbolicEngine->getOperandAst(pc);
        auto imm = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node = this->astCtxt->bv(inst.getNextAddress(), pc.getBitSize());
        auto node_pc = this->astCtxt->bvadd(pc_ast, imm);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, reg, "C.JAL operation ra (x1)");
        auto expr_pc = this->symbolicEngine->createSymbolicExpression(inst, node_pc, pc, "Program Counter");

        /* Spread taint */
        expr->isTainted = this->taintEngine->isTainted(pc);
        expr_pc->isTainted = this->taintEngine->isTainted(pc);

        /* Create the path constraint */
        this->symbolicEngine->pushPathConstraint(inst, expr_pc);
      }


      void riscvSemantics::c_jalr_s(triton::arch::Instruction& inst) {
        /* x1 := pc + 2; pc := (x[rs] + imm) & ~1
           Compressed instruction expands to:
           jalr rs -- [jalr x1, rs, 0] -- Jump and link register
         */
        auto pc = triton::arch::OperandWrapper(this->architecture->getProgramCounter());
        auto size = pc.getBitSize();
        auto& src = inst.operands[0];
        auto ra = this->architecture->getRegister(
                    size == 64 ?
                    triton::arch::ID_REG_RV64_X1 :
                    triton::arch::ID_REG_RV32_X1
                  );
        auto dst = triton::arch::OperandWrapper(ra);

        /* Create symbolic operands */
        auto pc_ast = this->symbolicEngine->getOperandAst(pc);
        auto op_src = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node_dst = this->astCtxt->bv(inst.getNextAddress(), pc.getBitSize());
        auto node_pc = this->astCtxt->bvand( /* ignore last bit */
                    op_src,
                    this->astCtxt->bvshl(this->astCtxt->bv(-1, size), this->astCtxt->bv(1, size))
                  );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node_dst, dst, "C.JALR operation ra (x1)");
        auto expr_pc = this->symbolicEngine->createSymbolicExpression(inst, node_pc, pc, "Program Counter");

        /* Spread taint */
        expr->isTainted = this->taintEngine->isTainted(pc);
        expr_pc->isTainted = this->taintEngine->setTaint(pc, this->taintEngine->isTainted(src));

        /* Create the path constraint */
        this->symbolicEngine->pushPathConstraint(inst, expr_pc);
      }


      void riscvSemantics::c_ld_s(triton::arch::Instruction& inst) { /* 64-bit only */
        // x[rd] := M[sp + offset][63:0]
        auto& dst  = inst.operands[0]; // rd
        auto& src1 = inst.operands[1]; // offset - disp
        auto& src2 = inst.operands[2]; // rs1 - base

        // FIXME when fixed https://github.com/capstone-engine/capstone/issues/2351
        /* Construct double word memory access manually with base and displacement */
        triton::arch::MemoryAccess mem;
        mem.setBits(triton::bitsize::qword - 1, 0);
        triton::arch::Immediate& disp = src1.getImmediate();
        triton::arch::Register& base = src2.getRegister();
        mem.setBaseRegister(base);
        mem.setDisplacement(disp);
        auto mem_op = triton::arch::OperandWrapper(mem);
        this->symbolicEngine->initLeaAst(mem_op.getMemory());

        /* Create the semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, mem_op);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "C.LD operation - LOAD access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, mem_op);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::c_ldsp_s(triton::arch::Instruction& inst) { /* 64-bit only */
        // x[rd] := M[sp + offset][63:0]
        auto& dst  = inst.operands[0]; // rd
        auto& src1 = inst.operands[1]; // offset - disp; (sp - base)

        // FIXME when fixed https://github.com/capstone-engine/capstone/issues/2351
        /* Construct double word memory access manually with base and displacement */
        triton::arch::MemoryAccess mem;
        mem.setBits(triton::bitsize::qword - 1, 0);
        triton::arch::Immediate& disp = src1.getImmediate();
        auto sp = this->architecture->getStackPointer();
        mem.setBaseRegister(sp);
        mem.setDisplacement(disp);
        auto mem_op = triton::arch::OperandWrapper(mem);
        this->symbolicEngine->initLeaAst(mem_op.getMemory());

        /* Create the semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, mem_op);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "C.LDSP operation - LOAD access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, mem_op);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::c_li_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create the semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "C.LI operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, false);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::c_lw_s(triton::arch::Instruction& inst) {
        // x[rd] := M[x[rs] + offset][31:0]
        auto& dst  = inst.operands[0]; // rd
        auto& src1 = inst.operands[1]; // offset - disp
        auto& src2 = inst.operands[2]; // rs1 - base

        // FIXME when fixed https://github.com/capstone-engine/capstone/issues/2351
        /* Construct word memory access manually with base and displacement */
        triton::arch::MemoryAccess mem;
        mem.setBits(triton::bitsize::dword - 1, 0);
        triton::arch::Immediate& disp = src1.getImmediate();
        triton::arch::Register& base = src2.getRegister();
        mem.setBaseRegister(base);
        mem.setDisplacement(disp);
        auto mem_op = triton::arch::OperandWrapper(mem);
        this->symbolicEngine->initLeaAst(mem_op.getMemory());

        /* Create the semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, mem_op);
        if (dst.getBitSize() == 64) { /* extend to register size */
          node = this->astCtxt->sx(32, node);
        }

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "C.LW operation - LOAD access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, mem_op);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::c_lwsp_s(triton::arch::Instruction& inst) {
        // x[rd] := M[sp + offset][31:0]
        auto& dst  = inst.operands[0]; // rd
        auto& src = inst.operands[1];  // offset - disp; (sp - base)

        // FIXME when fixed https://github.com/capstone-engine/capstone/issues/2351
        /* Construct word memory access manually with base and displacement */
        triton::arch::MemoryAccess mem;
        mem.setBits(triton::bitsize::dword - 1, 0);
        triton::arch::Immediate& disp = src.getImmediate();
        auto sp = this->architecture->getStackPointer();
        mem.setBaseRegister(sp);
        mem.setDisplacement(disp);
        auto mem_op = triton::arch::OperandWrapper(mem);
        this->symbolicEngine->initLeaAst(mem_op.getMemory());

        /* Create the semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, mem_op);
        if (dst.getBitSize() == 64) { /* extend to register size */
          node = this->astCtxt->sx(32, node);
        }

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "C.LWSP operation - LOAD access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, mem_op);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::c_mv_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create the semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "C.MV operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::c_nop_s(triton::arch::Instruction& inst) {
        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::c_or_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, dst);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node = this->astCtxt->bvor(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "C.OR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(dst) | this->taintEngine->isTainted(src));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::c_sd_s(triton::arch::Instruction& inst) { /* 64-bit only */
        // M[x[rs1] + offset] := x[rs2]
        auto& src = inst.operands[0];  // rs2
        auto& imm = inst.operands[1];  // offset - disp
        auto& dst = inst.operands[2];  // rs1 - base

        // FIXME when fixed https://github.com/capstone-engine/capstone/issues/2351
        /* Construct double word memory access manually with base and displacement */
        triton::arch::MemoryAccess mem;
        mem.setBits(triton::bitsize::qword - 1, 0);
        triton::arch::Immediate& disp = imm.getImmediate();
        triton::arch::Register& base  = dst.getRegister();
        mem.setBaseRegister(base);
        mem.setDisplacement(disp);
        auto mem_op = triton::arch::OperandWrapper(mem);
        this->symbolicEngine->initLeaAst(mem_op.getMemory());

        /* Create the semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, mem_op, "C.SD operation - STORE access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(mem_op, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::c_sdsp_s(triton::arch::Instruction& inst) { /* 64-bit only */
        // M[sp + offset] := x[rs]
        auto& src = inst.operands[0];  // rs
        auto& imm = inst.operands[1];  // offset - disp; (sp - base)

        // FIXME when fixed https://github.com/capstone-engine/capstone/issues/2351
        /* Construct double word memory access manually with base and displacement */
        triton::arch::MemoryAccess mem;
        mem.setBits(triton::bitsize::qword - 1, 0);
        triton::arch::Immediate& disp = imm.getImmediate();
        auto sp = this->architecture->getStackPointer();
        mem.setBaseRegister(sp);
        mem.setDisplacement(disp);
        auto mem_op = triton::arch::OperandWrapper(mem);
        this->symbolicEngine->initLeaAst(mem_op.getMemory());

        /* Create the semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, mem_op, "C.SDSP operation - STORE access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(mem_op, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::c_slli_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  size = src.getBitSize();

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, dst);
        auto op2 = this->astCtxt->bvand(
                     this->symbolicEngine->getOperandAst(inst, src),
                     dst.getBitSize() == 64 ? this->astCtxt->bv(0x1f, size) : this->astCtxt->bv(0x0f, size)
                   );

        /* Create the semantics */
        auto node = this->astCtxt->bvshl(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "C.SLLI operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::c_srai_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  size = src.getBitSize();

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, dst);
        auto op2 = this->astCtxt->bvand(
                     this->symbolicEngine->getOperandAst(inst, src),
                     dst.getBitSize() == 64 ? this->astCtxt->bv(0x1f, size) : this->astCtxt->bv(0x0f, size)
                   );

        /* Create the semantics */
        auto node = this->astCtxt->bvashr(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "C.SRAI operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::c_srli_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  size = src.getBitSize();

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, dst);
        auto op2 = this->astCtxt->bvand(
                     this->symbolicEngine->getOperandAst(inst, src),
                     dst.getBitSize() == 64 ? this->astCtxt->bv(0x1f, size) : this->astCtxt->bv(0x0f, size)
                   );

        /* Create the semantics */
        auto node = this->astCtxt->bvlshr(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "C.SRLI operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::c_sub_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, dst);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node = this->astCtxt->bvsub(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "C.SUB operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::c_subw_s(triton::arch::Instruction& inst) { /* 64-bit only */
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->astCtxt->extract(31, 0, this->symbolicEngine->getOperandAst(inst, dst));
        auto op2 = this->astCtxt->extract(31, 0, this->symbolicEngine->getOperandAst(inst, src));

        /* Create the semantics */
        auto node = this->astCtxt->sx(32, this->astCtxt->bvsub(op1, op2));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "C.SUBW operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::c_sw_s(triton::arch::Instruction& inst) {
        // M[x[rs1] + offset] := (x[rs2] & 0xffffffff)
        auto& src = inst.operands[0];  // rs2
        auto& imm = inst.operands[1];  // offset - disp
        auto& dst = inst.operands[2];  // rs1 - base

        // FIXME when fixed https://github.com/capstone-engine/capstone/issues/2351
        /* Construct double word memory access manually with base and displacement */
        triton::arch::MemoryAccess mem;
        mem.setBits(triton::bitsize::dword - 1, 0);
        triton::arch::Immediate& disp = imm.getImmediate();
        triton::arch::Register& base  = dst.getRegister();
        mem.setBaseRegister(base);
        mem.setDisplacement(disp);
        auto mem_op = triton::arch::OperandWrapper(mem);
        this->symbolicEngine->initLeaAst(mem_op.getMemory());

        /* Create the semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, src);
        if (src.getBitSize() == 64) {
          node = this->astCtxt->extract(31, 0, node);
        }

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, mem_op, "C.SW operation - STORE access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(mem_op, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::c_swsp_s(triton::arch::Instruction& inst) {
        // M[sp + offset] := (x[rs] & 0xffffffff)
        auto& src = inst.operands[0];  // rs
        auto& imm = inst.operands[1];  // offset - disp; (sp - base)

        // FIXME when fixed https://github.com/capstone-engine/capstone/issues/2351
        /* Construct double word memory access manually with base and displacement */
        triton::arch::MemoryAccess mem;
        mem.setBits(triton::bitsize::dword - 1, 0);
        triton::arch::Immediate& disp = imm.getImmediate();
        auto sp = this->architecture->getStackPointer();
        mem.setBaseRegister(sp);
        mem.setDisplacement(disp);
        auto mem_op = triton::arch::OperandWrapper(mem);
        this->symbolicEngine->initLeaAst(mem_op.getMemory());

        /* Create the semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, src);
        if (src.getBitSize() == 64) {
          node = this->astCtxt->extract(31, 0, node);
        }

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, mem_op, "C.SWSP operation - STORE access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(mem_op, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::c_xor_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, dst);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node = this->astCtxt->bvxor(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "C.XOR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(dst) | this->taintEngine->isTainted(src));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::div_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt->ite(
                      this->astCtxt->equal(op2, this->astCtxt->bv(0, op2->getBitvectorSize())),
                      this->astCtxt->bv(0, dst.getBitSize()),
                      this->astCtxt->bvsdiv(op1, op2)
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "DIV operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::divu_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt->ite(
                      this->astCtxt->equal(op2, this->astCtxt->bv(0, op2->getBitvectorSize())),
                      this->astCtxt->bv(0, dst.getBitSize()),
                      this->astCtxt->bvudiv(op1, op2)
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "DIVU operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::divuw_s(triton::arch::Instruction& inst) { /* 64-bit only */
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->astCtxt->extract(31, 0, this->symbolicEngine->getOperandAst(inst, src1));
        auto op2 = this->astCtxt->extract(31, 0, this->symbolicEngine->getOperandAst(inst, src2));

        /* Create the semantics */
        auto node = this->astCtxt->ite(
                      this->astCtxt->equal(op2, this->astCtxt->bv(0, op2->getBitvectorSize())),
                      this->astCtxt->bv(0, dst.getBitSize()),
                      this->astCtxt->sx(32, this->astCtxt->bvudiv(op1, op2))
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "DIVUW operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::divw_s(triton::arch::Instruction& inst) { /* 64-bit only */
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->astCtxt->extract(31, 0, this->symbolicEngine->getOperandAst(inst, src1));
        auto op2 = this->astCtxt->extract(31, 0, this->symbolicEngine->getOperandAst(inst, src2));

        /* Create the semantics */
        auto node = this->astCtxt->ite(
                      this->astCtxt->equal(op2, this->astCtxt->bv(0, op2->getBitvectorSize())),
                      this->astCtxt->bv(0, dst.getBitSize()),
                      this->astCtxt->sx(32, this->astCtxt->bvsdiv(op1, op2))
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "DIVW operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }

      void riscvSemantics::jal_s(triton::arch::Instruction& inst) {
        /* Check for possible pseudo instructions
           j offset   -- [jal x0, offset] -- Jump
           jal offset -- [jal x1, offset] -- Jump and link
         */
        auto mnem = inst.getDisassembly();
        if (mnem[1] == ' ') {
          jal_j_s(inst);
          return;
        }

        auto pc = triton::arch::OperandWrapper(this->architecture->getProgramCounter());
        auto size = pc.getBitSize();

        auto ra = this->architecture->getRegister(
                    size == 64 ?
                    triton::arch::ID_REG_RV64_X1 :
                    triton::arch::ID_REG_RV32_X1
                  );
        auto reg = triton::arch::OperandWrapper(ra);
        auto& src1 = inst.operands[0];

        /* Create symbolic operands */
        auto pc_ast = this->symbolicEngine->getOperandAst(pc);
        auto imm = this->symbolicEngine->getOperandAst(inst, src1);
        if (src1.getType() == triton::arch::OP_REG) {
          auto& src2 = inst.operands[1];
          reg = src1;
          imm = this->symbolicEngine->getOperandAst(inst, src2);
        }

        /* Create the semantics */
        auto node = this->astCtxt->bv(inst.getNextAddress(), size);
        auto node_pc = this->astCtxt->bvadd(pc_ast, imm);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, reg, "JAL operation ret addr");
        auto expr_pc = this->symbolicEngine->createSymbolicExpression(inst, node_pc, pc, "Program Counter");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(reg, this->taintEngine->isTainted(pc));
        expr_pc->isTainted = this->taintEngine->setTaint(pc, this->taintEngine->isTainted(pc));

        /* Create the path constraint */
        this->symbolicEngine->pushPathConstraint(inst, expr_pc);
      }


      void riscvSemantics::jal_j_s(triton::arch::Instruction& inst) {
        auto pc = triton::arch::OperandWrapper(this->architecture->getProgramCounter());
        auto& src1 = inst.operands[0];
        auto size = pc.getBitSize();

        /* Create symbolic operands */
        auto pc_ast = this->symbolicEngine->getOperandAst(pc);
        auto imm = this->symbolicEngine->getOperandAst(inst, src1);

        /* Create the semantics */
        auto node_pc = this->astCtxt->bvadd(pc_ast, imm);

        /* Create symbolic expression */
        auto expr_pc = this->symbolicEngine->createSymbolicExpression(inst, node_pc, pc, "Program Counter");

        /* Spread taint */
        expr_pc->isTainted = this->taintEngine->isTainted(pc);

        /* Create the path constraint */
        this->symbolicEngine->pushPathConstraint(inst, expr_pc);
      }


      void riscvSemantics::jalr_s(triton::arch::Instruction& inst) {
        /* x[rd] := pc + 4; pc := (x[rs] + imm) & ~1
        /* Check for possible pseudo instructions
           ret     -- [jalr x0, x1, 0] -- Return from subroutine
           jr rs   -- [jalr x0, rs, 0] -- Jump register
           jalr rs -- [jalr x1, rs, 0] -- Jump and link register
         */
        auto mnem = inst.getDisassembly();
        if (mnem[2] != 'l') { jalr_no_link_s(inst); return; } // ret & jr semantics

        auto pc = triton::arch::OperandWrapper(this->architecture->getProgramCounter());
        auto size = pc.getBitSize();
        auto ra = this->architecture->getRegister(
                    size == 64 ?
                    triton::arch::ID_REG_RV64_X1 :
                    triton::arch::ID_REG_RV32_X1
                  );
        auto dst = triton::arch::OperandWrapper(ra);
        auto& src = inst.operands[0];

        /* Create semantics (jalr with 1 operand) */
        auto pc_ast = this->symbolicEngine->getOperandAst(pc);
        auto node_dst = this->astCtxt->bv(inst.getNextAddress(), size);
        auto node_pc  = this->symbolicEngine->getOperandAst(inst, src);
        if (inst.operands.size() == 3) { // jalr with 3 operands semantics
          dst = src;
          src = inst.operands[1];
          auto& imm = inst.operands[2];

          /* Create symbolic operands */
          auto op1 = this->symbolicEngine->getOperandAst(inst, src);
          auto op2 = this->symbolicEngine->getOperandAst(inst, imm);

          node_pc = this->astCtxt->bvadd(op1, op2);
        }
        node_pc = this->astCtxt->bvand( /* ignore last bit */
                    node_pc,
                    this->astCtxt->bvshl(this->astCtxt->bv(-1, size), this->astCtxt->bv(1, size))
                  );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node_dst, dst, "JALR operation ret addr");
        auto expr_pc = this->symbolicEngine->createSymbolicExpression(inst, node_pc, pc, "Program Counter");

        /* Spread taint */
        expr->isTainted = this->taintEngine->isTainted(pc);
        expr_pc->isTainted = this->taintEngine->setTaint(pc, this->taintEngine->isTainted(src));

        /* Create the path constraint */
        this->symbolicEngine->pushPathConstraint(inst, expr_pc);
      }


      void riscvSemantics::jalr_no_link_s(triton::arch::Instruction& inst) {  // rd == x0
        auto pc = triton::arch::OperandWrapper(this->architecture->getProgramCounter());
        auto size = pc.getBitSize();
        auto ra = this->architecture->getRegister(
                    size == 64 ?
                    triton::arch::ID_REG_RV64_X1 :
                    triton::arch::ID_REG_RV32_X1
                  );
        auto src = triton::arch::OperandWrapper(ra);
        if (inst.operands.size()) {
          src = inst.operands[0];
        }

        /* Create the semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, src);
        node = this->astCtxt->bvand( /* ignore last bit */
                 node,
                 this->astCtxt->bvshl(this->astCtxt->bv(-1, size), this->astCtxt->bv(1, size))
               );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(pc, this->taintEngine->isTainted(src));

        /* Create the path constraint */
        this->symbolicEngine->pushPathConstraint(inst, expr);
      }


      void riscvSemantics::lb_s(triton::arch::Instruction& inst) {
        //  x[rd] := M[x[rs] + offset][7:0]
        auto& dst = inst.operands[0];  // rd
        auto& src = inst.operands[1];  // rs - base, offset - disp
        auto size = dst.getBitSize();

        /* Create the semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, src);
        node = this->astCtxt->sx(size - 8, node);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LB operation - LOAD access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::lbu_s(triton::arch::Instruction& inst) {
        //  x[rd] := M[x[rs] + offset][7:0]
        auto& dst = inst.operands[0];  // rd
        auto& src = inst.operands[1];  // rs - base, offset - disp
        auto size = dst.getBitSize();

        /* Create the semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, src);
        node = this->astCtxt->zx(size - 8, node);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LBU operation - LOAD access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::ld_s(triton::arch::Instruction& inst) { /* 64-bit only */
        //  x[rd] := M[x[rs] + offset][63:0]
        auto& dst = inst.operands[0];  // rd
        auto& src = inst.operands[1];  // rs - base, offset - disp

        /* Create the semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LD operation - LOAD access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::lh_s(triton::arch::Instruction& inst) {
        //  x[rd] := M[x[rs] + offset][15:0]
        auto& dst = inst.operands[0];  // rd
        auto& src = inst.operands[1];  // rs - base, offset - disp
        auto size = dst.getBitSize();

        /* Create the semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, src);
        node = this->astCtxt->sx(size - 16, node);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LH operation - LOAD access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::lhu_s(triton::arch::Instruction& inst) {
        // x[rd] := M[x[rs] + offset][15:0]
        auto& dst = inst.operands[0];  // rd
        auto& src = inst.operands[1];  // rs - base, offset - disp
        auto size = dst.getBitSize();

        /* Create the semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, src);
        node = this->astCtxt->zx(size - 16, node);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LHU operation - LOAD access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::lui_s(triton::arch::Instruction& inst) {
        // dst := (src_imm(_20) << 12)
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto size = dst.getBitSize();

        /* Create symbolic operands */
        auto imm = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node = this->astCtxt->bvshl(
                      this->astCtxt->sx(size - 20, this->astCtxt->extract(19, 0, imm)),
                      this->astCtxt->bv(12, size)
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LUI operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, false);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::lw_s(triton::arch::Instruction& inst) {
        // x[rd] := M[x[rs] + offset][31:0]
        auto& dst = inst.operands[0];  // rd
        auto& src = inst.operands[1];  // rs1 - base, offset - disp

        /* Create the semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, src);
        if (dst.getBitSize() == 64) { /* extend to register size */
          node = this->astCtxt->sx(32, node);
        }

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LW operation - LOAD access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::lwu_s(triton::arch::Instruction& inst) { /* 64-bit only */
        // x[rd] := M[x[rs] + offset][31:0]
        auto& dst = inst.operands[0];  // rd
        auto& src = inst.operands[1];  // rs1 - base, offset - disp
        auto size = dst.getBitSize();

        /* Create the semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, src);
        node = this->astCtxt->zx(32, node);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LWU operation - LOAD access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::mul_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt->bvmul(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MUL operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::mulh_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];
        auto  size = src2.getBitSize();

        /* Create symbolic operands */
        auto op1 = this->astCtxt->sx(size, this->symbolicEngine->getOperandAst(inst, src1));
        auto op2 = this->astCtxt->sx(size, this->symbolicEngine->getOperandAst(inst, src2));

        /* Create the semantics */
        auto node = this->astCtxt->extract(size * 2 - 1, size, this->astCtxt->bvmul(op1, op2));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MULH operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::mulhsu_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];
        auto  size = src2.getBitSize();

        /* Create symbolic operands */
        auto op1 = this->astCtxt->sx(size, this->symbolicEngine->getOperandAst(inst, src1));
        auto op2 = this->astCtxt->zx(size, this->symbolicEngine->getOperandAst(inst, src2));

        /* Create the semantics */
        auto node = this->astCtxt->extract(size * 2 - 1, size, this->astCtxt->bvmul(op1, op2));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MULHSU operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::mulhu_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];
        auto  size = src2.getBitSize();

        /* Create symbolic operands */
        auto op1 = this->astCtxt->zx(size,  this->symbolicEngine->getOperandAst(inst, src1));
        auto op2 = this->astCtxt->zx(size,  this->symbolicEngine->getOperandAst(inst, src2));

        /* Create the semantics */
        auto node = this->astCtxt->extract(size * 2 - 1, size, this->astCtxt->bvmul(op1, op2));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MULHU operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::mulw_s(triton::arch::Instruction& inst) { /* 64-bit only */
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->astCtxt->extract(31, 0, this->symbolicEngine->getOperandAst(inst, src1));
        auto op2 = this->astCtxt->extract(31, 0, this->symbolicEngine->getOperandAst(inst, src2));

        /* Create the semantics */
        auto node = this->astCtxt->sx(32, this->astCtxt->bvmul(op1, op2));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MULW operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::or_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt->bvor(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "OR(I) operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::rem_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt->ite(
                      this->astCtxt->equal(op2, this->astCtxt->bv(0, op2->getBitvectorSize())),
                      this->astCtxt->bv(0, dst.getBitSize()),
                      this->astCtxt->bvsrem(op1, op2)
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "REM operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::remu_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt->ite(
                      this->astCtxt->equal(op2, this->astCtxt->bv(0, op2->getBitvectorSize())),
                      this->astCtxt->bv(0, dst.getBitSize()),
                      this->astCtxt->bvurem(op1, op2)
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "REMU operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::remuw_s(triton::arch::Instruction& inst) { /* 64-bit only */
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->astCtxt->extract(31, 0, this->symbolicEngine->getOperandAst(inst, src1));
        auto op2 = this->astCtxt->extract(31, 0, this->symbolicEngine->getOperandAst(inst, src2));

        /* Create the semantics */
        auto node = this->astCtxt->ite(
                      this->astCtxt->equal(op2, this->astCtxt->bv(0, op2->getBitvectorSize())),
                      this->astCtxt->bv(0, dst.getBitSize()),
                      this->astCtxt->sx(32, this->astCtxt->bvurem(op1, op2))
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "REMUW operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::remw_s(triton::arch::Instruction& inst) { /* 64-bit only */
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->astCtxt->extract(31, 0, this->symbolicEngine->getOperandAst(inst, src1));
        auto op2 = this->astCtxt->extract(31, 0, this->symbolicEngine->getOperandAst(inst, src2));

        /* Create the semantics */
        auto node = this->astCtxt->ite(
                      this->astCtxt->equal(op2, this->astCtxt->bv(0, op2->getBitvectorSize())),
                      this->astCtxt->bv(0, dst.getBitSize()),
                      this->astCtxt->sx(32, this->astCtxt->bvsrem(op1, op2))
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "REMW operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::sb_s(triton::arch::Instruction& inst) {
        // M[x[rs1] + offset] := (x[rs2] & 0xff)
        auto& src = inst.operands[0];  // rs2
        auto& dst = inst.operands[1];  // rs1 - base, offset - disp

        /* Create symbolic operands */
        auto node = this->symbolicEngine->getOperandAst(inst, src);
        node = this->astCtxt->extract(7, 0, node);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SB operation - STORE access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::sd_s(triton::arch::Instruction& inst) { /* 64-bit only */
        // M[x[rs1] + offset] := x[rs2]
        auto& src = inst.operands[0];  // rs2
        auto& dst = inst.operands[1];  // rs1 - base, offset - disp

        /* Create symbolic operands */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SD operation - STORE access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::sh_s(triton::arch::Instruction& inst) {
        // M[x[rs1] + offset] := (x[rs2] & 0xffff)
        auto& src = inst.operands[0];  // rs2
        auto& dst = inst.operands[1];  // rs1 - base, offset - disp

        /* Create symbolic operands */
        auto node = this->symbolicEngine->getOperandAst(inst, src);
        node = this->astCtxt->extract(15, 0, node);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SH operation - STORE access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::sll_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];
        auto  size = src2.getBitSize();

        /* Create symbolic operands */
        auto bits = size == 64 ? 0x3f : 0x1f;
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->astCtxt->bvand(
                     this->symbolicEngine->getOperandAst(inst, src2),
                     this->astCtxt->bv(bits, size)
                   );

        /* Create the semantics */
        auto node = this->astCtxt->bvshl(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SLL(I) operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(src1, src2);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::sllw_s(triton::arch::Instruction& inst) { /* 64-bit only */
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];
        auto  size = src2.getBitSize();

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->astCtxt->bvand(
                     this->symbolicEngine->getOperandAst(inst, src2),
                     this->astCtxt->bv(0x1f, size)
                   );

        /* Create the semantics */
        auto node = this->astCtxt->bvshl(
                      this->astCtxt->sx(32, this->astCtxt->extract(31, 0, op1)),
                      op2
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SLL(I)W operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(src1, src2);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::slt_s(triton::arch::Instruction& inst) {
        /* Check for possible pseudo instructions
           sltz rd, rs -- [slt rd, rs, x0] -- Set if < zero
           sgtz rd, rs -- [slt rd, x0, rs] -- Set if > zero
         */
        auto mnem = inst.getDisassembly();
        if (mnem[3] == 'z') {
          if (mnem[1] == 'l') { slt_sltz_s(inst); } else { slt_sgtz_s(inst); }
        } else {
          slti_s(inst);
        }
      }


      void riscvSemantics::slt_sgtz_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src = inst.operands[1];
        auto  size = dst.getBitSize();

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src);
        auto zero = this->astCtxt->bv(0, size);

        /* Create the semantics */
        auto node = this->astCtxt->ite(this->astCtxt->bvsgt(op1, zero),
                      this->astCtxt->bv(1, size),
                      zero
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SGTZ operation");

        /* Set condition flag */
        if ((long long)op1->evaluate() > 0)
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::slt_sltz_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src = inst.operands[1];
        auto  size = dst.getBitSize();

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src);
        auto zero = this->astCtxt->bv(0, size);

        /* Create the semantics */
        auto node = this->astCtxt->ite(this->astCtxt->bvslt(op1, zero),
                      this->astCtxt->bv(1, size),
                      zero
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SLTZ operation");

        /* Set condition flag */
        if ((long long)op1->evaluate() < 0)
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::slti_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];
        auto  size = dst.getBitSize();

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt->ite(this->astCtxt->bvslt(op1, op2),
                      this->astCtxt->bv(1, size),
                      this->astCtxt->bv(0, size)
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SLT(I) operation");

        /* Set condition flag */
        if ((long long)(op2->evaluate() - op1->evaluate()) > 0)
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::sltiu_seqz_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src = inst.operands[1];
        auto  size = dst.getBitSize();

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src);
        auto zero = this->astCtxt->bv(0, size);

        /* Create the semantics */
        auto node = this->astCtxt->ite(this->astCtxt->equal(op1, zero),
                      this->astCtxt->bv(1, size),
                      zero
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SEQZ operation");

        /* Set condition flag */
        if (op1->evaluate() == 0)
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::sltu_s(triton::arch::Instruction& inst) {
        /* Check for possible pseudo instructions
           seqz rd, rs -- [sltiu rd, rs, 1] -- Set if == zero
           snez rd, rs -- [sltu rd, x0, rs] -- Set if != zero
         */
        auto mnem = inst.getDisassembly();
        if (mnem[1] == 'e') {
          sltiu_seqz_s(inst);
          return;
        }
        if (mnem[1] == 'n') {
          sltu_snez_s(inst);
          return;
        }

        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];
        auto  size = dst.getBitSize();

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt->ite(this->astCtxt->bvult(op1, op2),
                      this->astCtxt->bv(1, size),
                      this->astCtxt->bv(0, size)
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SLT(I)U operation");

        /* Set condition flag */
        if (op2->evaluate() > op1->evaluate())
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::sltu_snez_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src = inst.operands[1];
        auto  size = dst.getBitSize();

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src);
        auto zero = this->astCtxt->bv(0, size);

        /* Create the semantics */
        auto node = this->astCtxt->ite(this->astCtxt->equal(op1, zero),
                      zero,
                      this->astCtxt->bv(1, size)
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SNEZ operation");

        /* Set condition flag */
        if (op1->evaluate() != 0)
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::sra_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];
        auto  size = src2.getBitSize();

        /* Create symbolic operands */
        auto bits = size == 64 ? 0x3f : 0x1f;
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->astCtxt->bvand(
                     this->symbolicEngine->getOperandAst(inst, src2),
                     this->astCtxt->bv(bits, size)
                   );

        /* Create the semantics */
        auto node = this->astCtxt->bvashr(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SRA operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(src1, src2);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::sraw_s(triton::arch::Instruction& inst) { /* 64-bit only */
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];
        auto  size = src2.getBitSize();

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->astCtxt->bvand(
                     this->symbolicEngine->getOperandAst(inst, src2),
                     this->astCtxt->bv(0x1f, size)
                   );

        /* Create the semantics */
        auto node = this->astCtxt->bvashr(
                      this->astCtxt->sx(32, this->astCtxt->extract(31, 0, op1)),
                      op2
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SRA(I)W operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(src1, src2);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::srl_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];
        auto  size = src2.getBitSize();

        /* Create symbolic operands */
        auto bits = size == 64 ? 0x3f : 0x1f;
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->astCtxt->bvand(
                     this->symbolicEngine->getOperandAst(inst, src2),
                     this->astCtxt->bv(bits, size)
                   );

        /* Create the semantics */
        auto node = this->astCtxt->bvlshr(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SRL(I) operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(src1, src2);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::srlw_s(triton::arch::Instruction& inst) { /* 64-bit only */
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];
        auto  size = src2.getBitSize();

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->astCtxt->bvand(
                     this->symbolicEngine->getOperandAst(inst, src2),
                     this->astCtxt->bv(0x1f, size)
                   );

        /* Create the semantics */
        auto node = this->astCtxt->bvlshr(
                      this->astCtxt->sx(32, this->astCtxt->extract(31, 0, op1)),
                      op2
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SRL(I)W operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(src1, src2);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::sub_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto  size = dst.getBitSize();
        bool fix_taint = false;

        /* Create symbolic operands and semantics  */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto node = this->astCtxt->bvneg(op1); // neg pseudo instruction semantics
        if (inst.operands.size() > 2) {
          auto& src2 = inst.operands[2];
          auto op2 = this->symbolicEngine->getOperandAst(inst, src2);
          node = this->astCtxt->bvsub(op1, op2); // sub semantics
          fix_taint = this->taintEngine->isTainted(src2);
        }

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SUB operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->isTainted(src1) || fix_taint;

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::subw_s(triton::arch::Instruction& inst) { /* 64-bit only */
        auto& dst = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto  size = dst.getBitSize();
        bool fix_taint = false;

        /* Create symbolic operands and semantics  */
        auto op1 = this->astCtxt->extract(31, 0, this->symbolicEngine->getOperandAst(inst, src1));
        auto node = this->astCtxt->sx(32, this->astCtxt->bvneg(op1)); // negw pseudo instruction semantics
        if (inst.operands.size() > 2) {
          auto& src2 = inst.operands[2];
          auto op2 = this->astCtxt->extract(31, 0, this->symbolicEngine->getOperandAst(inst, src2));
          node = this->astCtxt->sx(32, this->astCtxt->bvsub(op1, op2)); // subw semantics
          fix_taint = this->taintEngine->isTainted(src2);
        }

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SUBW operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->isTainted(src1) || fix_taint;

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::sw_s(triton::arch::Instruction& inst) {
        // M[x[rs1] + offset] := (x[rs2] & 0xffffffff)
        auto& src = inst.operands[0];  // rs2
        auto& dst = inst.operands[1];  // rs1 - base, offset - disp

        /* Create symbolic operands and semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, src);
        if (src.getBitSize() == 64) {
          node = this->astCtxt->extract(31, 0, node);
        }

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SW operation - STORE access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::xor_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt->bvxor(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "XOR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void riscvSemantics::xori_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto node = this->astCtxt->bvnot(op1); // not pseudo instruction semantics

        if (inst.operands.size() > 2) {
          auto& src2 = inst.operands[2];
          auto op2 = this->symbolicEngine->getOperandAst(inst, src2);
          node = this->astCtxt->bvxor(op1, op2); // xori semantics
        }

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "XORI operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }

    }; /* riscv namespace */
  }; /* arch namespace */
}; /* triton namespace */
