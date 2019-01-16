//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <utility>
#include <triton/aarch64Semantics.hpp>
#include <triton/aarch64Specifications.hpp>
#include <triton/astContext.hpp>
#include <triton/cpuSize.hpp>
#include <triton/exceptions.hpp>



/*! \page SMT_aarch64_Semantics_Supported_page AArch64 SMT semantics supported
    \brief [**internal**] List of the supported semantics for the AArch64 architecture.


Mnemonic                      | Description
------------------------------|------------
ADC                           | Add with Carry
ADD (extended register)       | Add (extended register)
ADD (immediate)               | Add (immediate)
ADD (shifted register)        | Add (shifted register)
ADDS (extended register)      | Add (extended register), setting flags
ADDS (immediate)              | Add (immediate), setting flags
ADDS (shifted register)       | Add (shifted register), setting flags
ADR                           | Form PC-relative address
ADRP                          | Form PC-relative address to 4KB page
AND (immediate)               | Bitwise AND (immediate)
AND (shifted register)        | Bitwise AND (shifted register)
ANDS (immediate)              | Bitwise AND (immediate), setting flags
ANDS (shifted register)       | Bitwise AND (shifted register), setting flags
ASR (immediate)               | Arithmetic Shift Right (immediate): an alias of SBFM
ASR (register)                | Arithmetic Shift Right (register): an alias of ASRV
B                             | Branch
BL                            | Branch with Link
BLR                           | Branch with Link to Register
BR                            | Branch to Register
CBNZ                          | Compare and Branch on Nonzero
CBZ                           | Compare and Branch on Zero
CCMP (immediate)              | Conditional Compare (immediate)
CCMP (register)               | Conditional Compare (register)
CINC                          | Conditional Increment: an alias of CSINC
CLZ                           | Count Leading Zeros
CMN (extended register)       | Compare Negative (extended register): an alias of ADDS (extended register)
CMN (immediate)               | Compare Negative (immediate): an alias of ADDS (immediate)
CMN (shifted register)        | Compare Negative (shifted register): an alias of ADDS (shifted register)
CMP (extended register)       | Compare (extended register): an alias of SUBS (extended register)
CMP (immediate)               | Compare (immediate): an alias of SUBS (immediate)
CMP (shifted register)        | Compare (shifted register): an alias of SUBS (shifted register)
CSEL                          | Conditional Select
CSET                          | Conditional Set: an alias of CSINC
CSINC                         | Conditional Select Increment
CSNEG                         | Conditional Select Negation
EON (shifted register)        | Bitwise Exclusive OR NOT (shifted register)
EOR (immediate)               | Bitwise Exclusive OR (immediate)
EOR (shifted register)        | Bitwise Exclusive OR (shifted register)
EXTR                          | EXTR: Extract register
LDAR                          | Load-Acquire Register
LDARB                         | Load-Acquire Register Byte
LDARH                         | Load-Acquire Register Halfword
LDAXR                         | Load-Acquire Exclusive Register
LDAXRB                        | Load-Acquire Exclusive Register Byte
LDAXRH                        | Load-Acquire Exclusive Register Halfword
LDP                           | Load Pair of Registers
LDR (immediate)               | Load Register (immediate)
LDR (literal)                 | Load Register (literal)
LDR (register)                | Load Register (register)
LDRB (immediate)              | Load Register Byte (immediate)
LDRB (register)               | Load Register Byte (register)
LDRH (immediate)              | Load Register Halfword (immediate)
LDRH (register)               | Load Register Halfword (register)
LDRSB (immediate)             | Load Register Signed Byte (immediate)
LDRSB (register)              | Load Register Signed Byte (register)
LDRSH (immediate)             | Load Register Signed Halfword (immediate)
LDRSH (register)              | Load Register Signed Halfword (register)
LDRSW (immediate)             | Load Register Signed Word (immediate)
LDRSW (literal)               | Load Register Signed Word (literal)
LDRSW (register)              | Load Register Signed Word (register)
LDUR                          | Load Register (unscaled)
LDURB                         | Load Register Byte (unscaled)
LDURH                         | Load Register Halfword (unscaled)
LDURSB                        | Load Register Signed Byte (unscaled)
LDURSH                        | Load Register Signed Halfword (unscaled)
LDURSW                        | Load Register Signed Word (unscaled)
LDXR                          | Load Exclusive Register
LDXRB                         | Load Exclusive Register Byte
LDXRH                         | Load Exclusive Register Halfword
LSL (immediate)               | Logical Shift Left (immediate): an alias of UBFM
LSL (register)                | Logical Shift Left (register): an alias of LSLV
LSR (immediate)               | Logical Shift Right (immediate): an alias of UBFM
LSR (register)                | Logical Shift Right (register): an alias of LSRV
MADD                          | Multiply-Add
MNEG                          | Multiply-Negate: an alias of MSUB
MOV (bitmask immediate)       | Move (bitmask immediate): an alias of ORR (immediate)
MOV (register)                | Move (register): an alias of ORR (shifted register)
MOV (to/from SP)              | Move between register and stack pointer: an alias of ADD (immediate)
MOVK                          | Move wide with keep
MOVN                          | Move wide with NOT
MOVZ                          | Move shifted 16-bit immediate to register
MSUB                          | Multiply-Subtract
MUL                           | Multiply: an alias of MADD
MVN                           | Bitwise NOT: an alias of ORN (shifted register)
NEG (shifted register)        | Negate (shifted register): an alias of SUB (shifted register)
NOP                           | No Operation
ORN                           | Bitwise OR NOT (shifted register)
ORR (immediate)               | Bitwise OR (immediate)
ORR (shifted register)        | Bitwise OR (shifted register)
RBIT                          | Reverse Bits
RET                           | Return from subroutine
REV                           | Reverse Bytes
REV16                         | Reverse bytes in 16-bit halfwords
REV32                         | Reverse bytes in 32-bit words
REV64                         | Reverse Bytes: an alias of REV
ROR (immediate)               | Rotate right (immediate): an alias of EXTR
ROR (register)                | Rotate Right (register): an alias of RORV
RORV                          | Rotate Right Variable
SBFX                          | Signed Bitfield Extract: an alias of SBFM
SDIV                          | Signed Divide
SMADDL                        | Signed Multiply-Add Long
SMSUBL                        | Signed Multiply-Subtract Long
SMULH                         | Signed Multiply High
SMULL                         | Signed Multiply Long: an alias of SMADDL
STLR                          | Store-Release Register
STLRB                         | Store-Release Register Byte
STLRH                         | Store-Release Register Halfword
STP                           | Store Pair of Registers
STR (immediate)               | Store Register (immediate)
STR (register)                | Store Register (register)
STRB (immediate)              | Store Register Byte (immediate)
STRB (register)               | Store Register Byte (register)
STRH (immediate)              | Store Register Halfword (immediate)
STRH (register)               | Store Register Halfword (register)
STUR                          | Store Register (unscaled)
STURB                         | Store Register Byte (unscaled)
STURH                         | Store Register Halfword (unscaled)
SUB (extended register)       | Subtract (extended register)
SUB (immediate)               | Subtract (immediate)
SUB (shifted register)        | Subtract (shifted register)
SUBS (extended register)      | Subtract (extended register), setting flags
SUBS (immediate)              | Subtract (immediate), setting flags
SUBS (shifted register)       | Subtract (shifted register), setting flags
SXTB                          | Signed Extend Byte: an alias of SBFM
SXTH                          | Sign Extend Halfword: an alias of SBFM
SXTW                          | Sign Extend Word: an alias of SBFM
TST (immediate)               | Test bits (immediate): an alias of ANDS (immediate)
TST (shifted register)        | Test (shifted register): an alias of ANDS (shifted register)
UBFIZ                         | Unsigned Bitfield Insert in Zero: an alias of UBFM
UBFX                          | Unsigned Bitfield Extract: an alias of UBFM
UDIV                          | Unsigned Divide
UMADDL                        | Unsigned Multiply-Add Long
UMNEGL                        | Unsigned Multiply-Negate Long: an alias of UMSUBL
UMSUBL                        | Unsigned Multiply-Subtract Long
UMULH                         | Unsigned Multiply High
UMULL                         | Unsigned Multiply Long: an alias of UMADDL
UXTB                          | Unsigned Extend Byte: an alias of UBFM
UXTH                          | Unsigned Extend Halfword: an alias of UBFM

*/


namespace triton {
  namespace arch {
    namespace aarch64 {

      AArch64Semantics::AArch64Semantics(triton::arch::Architecture* architecture,
                                         triton::engines::symbolic::SymbolicEngine* symbolicEngine,
                                         triton::engines::taint::TaintEngine* taintEngine,
                                         triton::ast::AstContext& astCtxt) : astCtxt(astCtxt) {

        this->architecture    = architecture;
        this->symbolicEngine  = symbolicEngine;
        this->taintEngine     = taintEngine;

        if (architecture == nullptr)
          throw triton::exceptions::Semantics("AArch64Semantics::AArch64Semantics(): The architecture API must be defined.");

        if (this->symbolicEngine == nullptr)
          throw triton::exceptions::Semantics("AArch64Semantics::AArch64Semantics(): The symbolic engine API must be defined.");

        if (this->taintEngine == nullptr)
          throw triton::exceptions::Semantics("AArch64Semantics::AArch64Semantics(): The taint engines API must be defined.");
      }


      bool AArch64Semantics::buildSemantics(triton::arch::Instruction& inst) {
        switch (inst.getType()) {
          case ID_INS_ADC:       this->adc_s(inst);           break;
          case ID_INS_ADD:       this->add_s(inst);           break;
          case ID_INS_ADR:       this->adr_s(inst);           break;
          case ID_INS_ADRP:      this->adrp_s(inst);          break;
          case ID_INS_AND:       this->and_s(inst);           break;
          case ID_INS_ASR:       this->asr_s(inst);           break;
          case ID_INS_B:         this->b_s(inst);             break;
          case ID_INS_BL:        this->bl_s(inst);            break;
          case ID_INS_BLR:       this->blr_s(inst);           break;
          case ID_INS_BR:        this->br_s(inst);            break;
          case ID_INS_CBNZ:      this->cbnz_s(inst);          break;
          case ID_INS_CBZ:       this->cbz_s(inst);           break;
          case ID_INS_CCMP:      this->ccmp_s(inst);          break;
          case ID_INS_CINC:      this->cinc_s(inst);          break;
          case ID_INS_CLZ:       this->clz_s(inst);           break;
          case ID_INS_CMN:       this->cmn_s(inst);           break;
          case ID_INS_CMP:       this->cmp_s(inst);           break;
          case ID_INS_CSEL:      this->csel_s(inst);          break;
          case ID_INS_CSET:      this->cset_s(inst);          break;
          case ID_INS_CSINC:     this->csinc_s(inst);         break;
          case ID_INS_CSNEG:     this->csneg_s(inst);         break;
          case ID_INS_EON:       this->eon_s(inst);           break;
          case ID_INS_EOR:       this->eor_s(inst);           break;
          case ID_INS_EXTR:      this->extr_s(inst);          break;
          case ID_INS_LDAR:      this->ldar_s(inst);          break;
          case ID_INS_LDARB:     this->ldarb_s(inst);         break;
          case ID_INS_LDARH:     this->ldarh_s(inst);         break;
          case ID_INS_LDAXR:     this->ldaxr_s(inst);         break;
          case ID_INS_LDAXRB:    this->ldaxrb_s(inst);        break;
          case ID_INS_LDAXRH:    this->ldaxrh_s(inst);        break;
          case ID_INS_LDP:       this->ldp_s(inst);           break;
          case ID_INS_LDR:       this->ldr_s(inst);           break;
          case ID_INS_LDRB:      this->ldrb_s(inst);          break;
          case ID_INS_LDRH:      this->ldrh_s(inst);          break;
          case ID_INS_LDRSB:     this->ldrsb_s(inst);         break;
          case ID_INS_LDRSH:     this->ldrsh_s(inst);         break;
          case ID_INS_LDRSW:     this->ldrsw_s(inst);         break;
          case ID_INS_LDUR:      this->ldur_s(inst);          break;
          case ID_INS_LDURB:     this->ldurb_s(inst);         break;
          case ID_INS_LDURH:     this->ldurh_s(inst);         break;
          case ID_INS_LDURSB:    this->ldursb_s(inst);        break;
          case ID_INS_LDURSH:    this->ldursh_s(inst);        break;
          case ID_INS_LDURSW:    this->ldursw_s(inst);        break;
          case ID_INS_LDXR:      this->ldxr_s(inst);          break;
          case ID_INS_LDXRB:     this->ldxrb_s(inst);         break;
          case ID_INS_LDXRH:     this->ldxrh_s(inst);         break;
          case ID_INS_LSL:       this->lsl_s(inst);           break;
          case ID_INS_LSR:       this->lsr_s(inst);           break;
          case ID_INS_MADD:      this->madd_s(inst);          break;
          case ID_INS_MNEG:      this->mneg_s(inst);          break;
          case ID_INS_MOV:       this->mov_s(inst);           break;
          case ID_INS_MOVK:      this->movk_s(inst);          break;
          case ID_INS_MOVN:      this->movn_s(inst);          break;
          case ID_INS_MOVZ:      this->movz_s(inst);          break;
          case ID_INS_MSUB:      this->msub_s(inst);          break;
          case ID_INS_MUL:       this->mul_s(inst);           break;
          case ID_INS_MVN:       this->mvn_s(inst);           break;
          case ID_INS_NEG:       this->neg_s(inst);           break;
          case ID_INS_NOP:       this->nop_s(inst);           break;
          case ID_INS_ORN:       this->orn_s(inst);           break;
          case ID_INS_ORR:       this->orr_s(inst);           break;
          case ID_INS_RBIT:      this->rbit_s(inst);          break;
          case ID_INS_RET:       this->ret_s(inst);           break;
          case ID_INS_REV16:     this->rev16_s(inst);         break;
          case ID_INS_REV32:     this->rev32_s(inst);         break;
          case ID_INS_REV64:     this->rev_s(inst);           break;
          case ID_INS_REV:       this->rev_s(inst);           break;
          case ID_INS_ROR:       this->ror_s(inst);           break;
          case ID_INS_SBFX:      this->sbfx_s(inst);          break;
          case ID_INS_SDIV:      this->sdiv_s(inst);          break;
          case ID_INS_SMADDL:    this->smaddl_s(inst);        break;
          case ID_INS_SMSUBL:    this->smsubl_s(inst);        break;
          case ID_INS_SMULH:     this->smulh_s(inst);         break;
          case ID_INS_SMULL:     this->smull_s(inst);         break;
          case ID_INS_STLR:      this->stlr_s(inst);          break;
          case ID_INS_STLRB:     this->stlrb_s(inst);         break;
          case ID_INS_STLRH:     this->stlrh_s(inst);         break;
          case ID_INS_STP:       this->stp_s(inst);           break;
          case ID_INS_STR:       this->str_s(inst);           break;
          case ID_INS_STRB:      this->strb_s(inst);          break;
          case ID_INS_STRH:      this->strh_s(inst);          break;
          case ID_INS_STUR:      this->stur_s(inst);          break;
          case ID_INS_STURB:     this->sturb_s(inst);         break;
          case ID_INS_STURH:     this->sturh_s(inst);         break;
          case ID_INS_SUB:       this->sub_s(inst);           break;
          case ID_INS_SXTB:      this->sxtb_s(inst);          break;
          case ID_INS_SXTH:      this->sxth_s(inst);          break;
          case ID_INS_SXTW:      this->sxtw_s(inst);          break;
          case ID_INS_TBNZ:      this->tbnz_s(inst);          break;
          case ID_INS_TBZ:       this->tbz_s(inst);           break;
          case ID_INS_TST:       this->tst_s(inst);           break;
          case ID_INS_UBFIZ:     this->ubfiz_s(inst);         break;
          case ID_INS_UBFX:      this->ubfx_s(inst);          break;
          case ID_INS_UDIV:      this->udiv_s(inst);          break;
          case ID_INS_UMADDL:    this->umaddl_s(inst);        break;
          case ID_INS_UMNEGL:    this->umnegl_s(inst);        break;
          case ID_INS_UMSUBL:    this->umsubl_s(inst);        break;
          case ID_INS_UMULH:     this->umulh_s(inst);         break;
          case ID_INS_UMULL:     this->umull_s(inst);         break;
          case ID_INS_UXTB:      this->uxtb_s(inst);          break;
          case ID_INS_UXTH:      this->uxth_s(inst);          break;
          default:
            return false;
        }
        return true;
      }


      void AArch64Semantics::controlFlow_s(triton::arch::Instruction& inst) {
        auto pc = triton::arch::OperandWrapper(this->architecture->getParentRegister(ID_REG_AARCH64_PC));

        /* Create the semantics */
        auto node = this->astCtxt.bv(inst.getNextAddress(), pc.getBitSize());

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicRegisterExpression(inst, node, this->architecture->getParentRegister(ID_REG_AARCH64_PC), "Program Counter");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaintRegister(this->architecture->getParentRegister(ID_REG_AARCH64_PC), triton::engines::taint::UNTAINTED);
      }


      triton::ast::SharedAbstractNode AArch64Semantics::getCodeConditionAst(triton::arch::Instruction& inst,
                                                                            triton::ast::SharedAbstractNode& thenNode,
                                                                            triton::ast::SharedAbstractNode& elseNode) {

        switch (inst.getCodeCondition()) {
          // Always. Any flags. This suffix is normally omitted.
          case triton::arch::aarch64::ID_CONDITION_AL: {
            return thenNode;
          }

          // Equal. Z set.
          case triton::arch::aarch64::ID_CONDITION_EQ: {
            auto z = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_Z)));
            auto node = this->astCtxt.ite(
                        this->astCtxt.equal(z, this->astCtxt.bvtrue()),
                        thenNode,
                        elseNode);
            return node;
          }

          // Signed >=. N and V the same.
          case triton::arch::aarch64::ID_CONDITION_GE: {
            auto n = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_N)));
            auto v = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_V)));
            auto node = this->astCtxt.ite(
                        this->astCtxt.equal(n, v),
                        thenNode,
                        elseNode);
            return node;
          }

          // Signed >. Z clear, N and V the same.
          case triton::arch::aarch64::ID_CONDITION_GT: {
            auto z = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_Z)));
            auto n = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_N)));
            auto v = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_V)));
            auto node = this->astCtxt.ite(
                        this->astCtxt.land(
                          this->astCtxt.equal(z, this->astCtxt.bvfalse()),
                          this->astCtxt.equal(n, v)
                        ),
                        thenNode,
                        elseNode);
            return node;
          }

          // Higher (unsigned >). C set and Z clear.
          case triton::arch::aarch64::ID_CONDITION_HI: {
            auto c = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_C)));
            auto z = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_Z)));
            auto node = this->astCtxt.ite(
                        this->astCtxt.land(
                          this->astCtxt.equal(c, this->astCtxt.bvtrue()),
                          this->astCtxt.equal(z, this->astCtxt.bvfalse())
                        ),
                        thenNode,
                        elseNode);
            return node;
          }

          // Higher or same (unsigned >=). C set.
          case triton::arch::aarch64::ID_CONDITION_HS: {
            auto c = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_C)));
            auto node = this->astCtxt.ite(
                        this->astCtxt.equal(c, this->astCtxt.bvtrue()),
                        thenNode,
                        elseNode);
            return node;
          }

          // Signed <=. Z set or N and V differ.
          case triton::arch::aarch64::ID_CONDITION_LE: {
            auto z = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_Z)));
            auto n = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_N)));
            auto v = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_V)));
            auto node = this->astCtxt.ite(
                        this->astCtxt.lor(
                          this->astCtxt.equal(z, this->astCtxt.bvtrue()),
                          this->astCtxt.lnot(this->astCtxt.equal(n, v))
                        ),
                        thenNode,
                        elseNode);
            return node;
          }

          // Lower (unsigned <). C clear.
          case triton::arch::aarch64::ID_CONDITION_LO: {
            auto c = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_C)));
            auto node = this->astCtxt.ite(
                        this->astCtxt.equal(c, this->astCtxt.bvfalse()),
                        thenNode,
                        elseNode);
            return node;
          }

          // Lower or same (unsigned <=). C clear or Z set.
          case triton::arch::aarch64::ID_CONDITION_LS: {
            auto c = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_C)));
            auto z = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_Z)));
            auto node = this->astCtxt.ite(
                        this->astCtxt.lor(
                          this->astCtxt.equal(c, this->astCtxt.bvfalse()),
                          this->astCtxt.equal(z, this->astCtxt.bvtrue())
                        ),
                        thenNode,
                        elseNode);
            return node;
          }

          // Signed <. N and V differ.
          case triton::arch::aarch64::ID_CONDITION_LT: {
            auto n = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_N)));
            auto v = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_V)));
            auto node = this->astCtxt.ite(
                        this->astCtxt.lnot(this->astCtxt.equal(n, v)),
                        thenNode,
                        elseNode);
            return node;
          }

          // Negative. N set.
          case triton::arch::aarch64::ID_CONDITION_MI: {
            auto n = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_N)));
            auto node = this->astCtxt.ite(
                        this->astCtxt.equal(n, this->astCtxt.bvtrue()),
                        thenNode,
                        elseNode);
            return node;
          }

          // Not equal. Z clear.
          case triton::arch::aarch64::ID_CONDITION_NE: {
            auto z = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_Z)));
            auto node = this->astCtxt.ite(
                        this->astCtxt.equal(z, this->astCtxt.bvfalse()),
                        thenNode,
                        elseNode);
            return node;
          }

          // Positive or zero. N clear.
          case triton::arch::aarch64::ID_CONDITION_PL: {
            auto n = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_N)));
            auto node = this->astCtxt.ite(
                        this->astCtxt.equal(n, this->astCtxt.bvfalse()),
                        thenNode,
                        elseNode);
            return node;
          }

          // No overflow. V clear.
          case triton::arch::aarch64::ID_CONDITION_VC: {
            auto v = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_V)));
            auto node = this->astCtxt.ite(
                        this->astCtxt.equal(v, this->astCtxt.bvfalse()),
                        thenNode,
                        elseNode);
            return node;
          }

          // Overflow. V set.
          case triton::arch::aarch64::ID_CONDITION_VS: {
            auto v = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_V)));
            auto node = this->astCtxt.ite(
                        this->astCtxt.equal(v, this->astCtxt.bvtrue()),
                        thenNode,
                        elseNode);
            return node;
          }

          default:
            /* The instruction don't use condition, so just return the 'then' node */
            return thenNode;
        }
      }


      bool AArch64Semantics::getCodeConditionTainteSate(const triton::arch::Instruction& inst) {
        switch (inst.getCodeCondition()) {
          // Always. Any flags. This suffix is normally omitted.
          case triton::arch::aarch64::ID_CONDITION_AL: {
            return false;
          }

          // Equal. Z set.
          // Not equal. Z clear.
          case triton::arch::aarch64::ID_CONDITION_EQ:
          case triton::arch::aarch64::ID_CONDITION_NE: {
            auto z = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_Z));
            return this->taintEngine->isTainted(z);
          }

          // Signed >=. N and V the same.
          // Signed <. N and V differ.
          case triton::arch::aarch64::ID_CONDITION_GE:
          case triton::arch::aarch64::ID_CONDITION_LT: {
            auto n = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_N));
            auto v = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_V));
            return this->taintEngine->isTainted(n) | this->taintEngine->isTainted(v);
          }

          // Signed >. Z clear, N and V the same.
          // Signed <=. Z set, N and V differ.
          case triton::arch::aarch64::ID_CONDITION_GT:
          case triton::arch::aarch64::ID_CONDITION_LE: {
            auto z = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_Z));
            auto n = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_N));
            auto v = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_V));
            return this->taintEngine->isTainted(z) | this->taintEngine->isTainted(n) | this->taintEngine->isTainted(v);
          }

          // Higher (unsigned >). C set and Z clear.
          // Lower or same (unsigned <=). C clear or Z set.
          case triton::arch::aarch64::ID_CONDITION_HI:
          case triton::arch::aarch64::ID_CONDITION_LS: {
            auto c = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_C));
            auto z = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_Z));
            return this->taintEngine->isTainted(c) | this->taintEngine->isTainted(z);
          }

          // Higher or same (unsigned >=). C set.
          // Lower (unsigned <). C clear.
          case triton::arch::aarch64::ID_CONDITION_HS:
          case triton::arch::aarch64::ID_CONDITION_LO: {
            auto c = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_C));
            return this->taintEngine->isTainted(c);
          }

          // Negative. N set.
          // Positive or zero. N clear.
          case triton::arch::aarch64::ID_CONDITION_MI:
          case triton::arch::aarch64::ID_CONDITION_PL: {
            auto n = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_N));
            return this->taintEngine->isTainted(n);
          }

          // No overflow. V clear.
          // Overflow. V set.
          case triton::arch::aarch64::ID_CONDITION_VC:
          case triton::arch::aarch64::ID_CONDITION_VS: {
            auto v = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_V));
            return this->taintEngine->isTainted(v);
          }

          default:
            return false;
        }
      }


      void AArch64Semantics::clearFlag_s(triton::arch::Instruction& inst, const triton::arch::Register& flag, std::string comment) {
        /* Create the semantics */
        auto node = this->astCtxt.bv(0, 1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, flag, comment);

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaintRegister(flag, triton::engines::taint::UNTAINTED);
      }


      void AArch64Semantics::setFlag_s(triton::arch::Instruction& inst, const triton::arch::Register& flag, std::string comment) {
        /* Create the semantics */
        auto node = this->astCtxt.bv(1, 1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, flag, comment);

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaintRegister(flag, triton::engines::taint::UNTAINTED);
      }


      void AArch64Semantics::nf_s(triton::arch::Instruction& inst,
                                  const triton::engines::symbolic::SharedSymbolicExpression& parent,
                                  triton::arch::OperandWrapper& dst) {

        auto nf   = this->architecture->getRegister(ID_REG_AARCH64_N);
        auto high = dst.getHigh();

        /*
         * Create the semantic.
         * nf = MSB(result)
         */
        auto node = this->astCtxt.extract(high, high, this->astCtxt.reference(parent));

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, nf, "Negative flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(nf, parent->isTainted);
      }


      void AArch64Semantics::nfCcmp_s(triton::arch::Instruction& inst,
                                      const triton::engines::symbolic::SharedSymbolicExpression& parent,
                                      triton::arch::OperandWrapper& dst,
                                      triton::ast::SharedAbstractNode& nzcv) {

        auto nf   = this->architecture->getRegister(ID_REG_AARCH64_N);
        auto high = dst.getHigh();

        /*
         * Create the semantic.
         * nf = MSB(result) if cond == true else NF(nzcv)
         */
        auto node1 = this->astCtxt.extract(high, high, this->astCtxt.reference(parent));
        auto node2 = this->astCtxt.extract(3, 3, nzcv);
        auto node3 = this->getCodeConditionAst(inst, node1, node2);

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node3, nf, "Negative flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(nf, parent->isTainted);
      }


      void AArch64Semantics::zf_s(triton::arch::Instruction& inst,
                                  const triton::engines::symbolic::SharedSymbolicExpression& parent,
                                  triton::arch::OperandWrapper& dst) {

        auto zf     = this->architecture->getRegister(ID_REG_AARCH64_Z);
        auto bvSize = dst.getBitSize();
        auto low    = dst.getLow();
        auto high   = dst.getHigh();

        /*
         * Create the semantic.
         * zf = 0 == result
         */
        auto node = this->astCtxt.ite(
                      this->astCtxt.equal(
                        this->astCtxt.extract(high, low, this->astCtxt.reference(parent)),
                        this->astCtxt.bv(0, bvSize)
                      ),
                      this->astCtxt.bv(1, 1),
                      this->astCtxt.bv(0, 1)
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, zf, "Zero flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(zf, parent->isTainted);
      }


      void AArch64Semantics::zfCcmp_s(triton::arch::Instruction& inst,
                                      const triton::engines::symbolic::SharedSymbolicExpression& parent,
                                      triton::arch::OperandWrapper& dst,
                                      triton::ast::SharedAbstractNode& nzcv) {

        auto zf     = this->architecture->getRegister(ID_REG_AARCH64_Z);
        auto bvSize = dst.getBitSize();
        auto low    = dst.getLow();
        auto high   = dst.getHigh();

        /*
         * Create the semantic.
         * zf = 0 == result if cond == true else ZF(nzcv)
         */
        auto node1 = this->astCtxt.ite(
                       this->astCtxt.equal(
                         this->astCtxt.extract(high, low, this->astCtxt.reference(parent)),
                         this->astCtxt.bv(0, bvSize)
                       ),
                       this->astCtxt.bv(1, 1),
                       this->astCtxt.bv(0, 1)
                     );
        auto node2 = this->astCtxt.extract(2, 2, nzcv);
        auto node3 = this->getCodeConditionAst(inst, node1, node2);

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node3, zf, "Zero flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(zf, parent->isTainted);
      }


      void AArch64Semantics::cfAdd_s(triton::arch::Instruction& inst,
                                     const triton::engines::symbolic::SharedSymbolicExpression& parent,
                                     triton::arch::OperandWrapper& dst,
                                     triton::ast::SharedAbstractNode& op1,
                                     triton::ast::SharedAbstractNode& op2) {

        auto cf     = this->architecture->getRegister(ID_REG_AARCH64_C);
        auto bvSize = dst.getBitSize();
        auto low    = dst.getLow();
        auto high   = dst.getHigh();

        /*
         * Create the semantic.
         * cf = MSB((op1 & op2) ^ ((op1 ^ op2 ^ result) & (op1 ^ op2)));
         */
        auto node = this->astCtxt.extract(bvSize-1, bvSize-1,
                      this->astCtxt.bvxor(
                        this->astCtxt.bvand(op1, op2),
                        this->astCtxt.bvand(
                          this->astCtxt.bvxor(
                            this->astCtxt.bvxor(op1, op2),
                            this->astCtxt.extract(high, low, this->astCtxt.reference(parent))
                          ),
                        this->astCtxt.bvxor(op1, op2))
                      )
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, cf, "Carry flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(cf, parent->isTainted);
      }


      void AArch64Semantics::cfSub_s(triton::arch::Instruction& inst,
                                     const triton::engines::symbolic::SharedSymbolicExpression& parent,
                                     triton::arch::OperandWrapper& dst,
                                     triton::ast::SharedAbstractNode& op1,
                                     triton::ast::SharedAbstractNode& op2) {

        auto cf     = this->architecture->getRegister(ID_REG_AARCH64_C);
        auto bvSize = dst.getBitSize();
        auto low    = dst.getLow();
        auto high   = dst.getHigh();

        /*
         * Create the semantic.
         * cf = (MSB(((op1 ^ op2 ^ result) ^ ((op1 ^ result) & (op1 ^ op2))))) ^ 1
         */
        auto node = this->astCtxt.bvxor(
                      this->astCtxt.extract(bvSize-1, bvSize-1,
                        this->astCtxt.bvxor(
                          this->astCtxt.bvxor(op1, this->astCtxt.bvxor(op2, this->astCtxt.extract(high, low, this->astCtxt.reference(parent)))),
                          this->astCtxt.bvand(
                            this->astCtxt.bvxor(op1, this->astCtxt.extract(high, low, this->astCtxt.reference(parent))),
                            this->astCtxt.bvxor(op1, op2)
                          )
                        )
                      ),
                      this->astCtxt.bvtrue()
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, cf, "Carry flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(cf, parent->isTainted);
      }


      void AArch64Semantics::cfCcmp_s(triton::arch::Instruction& inst,
                                      const triton::engines::symbolic::SharedSymbolicExpression& parent,
                                      triton::arch::OperandWrapper& dst,
                                      triton::ast::SharedAbstractNode& op1,
                                      triton::ast::SharedAbstractNode& op2,
                                      triton::ast::SharedAbstractNode& nzcv) {

        auto cf     = this->architecture->getRegister(ID_REG_AARCH64_C);
        auto bvSize = dst.getBitSize();
        auto low    = dst.getLow();
        auto high   = dst.getHigh();

        /*
         * Create the semantic.
         * if cond == true:
         *   cf = (MSB(((op1 ^ op2 ^ result) ^ ((op1 ^ result) & (op1 ^ op2))))) ^ 1
         * else
         *   cf = CF(nzcv)
         */
        auto node1 = this->astCtxt.bvxor(
                       this->astCtxt.extract(bvSize-1, bvSize-1,
                         this->astCtxt.bvxor(
                           this->astCtxt.bvxor(op1, this->astCtxt.bvxor(op2, this->astCtxt.extract(high, low, this->astCtxt.reference(parent)))),
                           this->astCtxt.bvand(
                             this->astCtxt.bvxor(op1, this->astCtxt.extract(high, low, this->astCtxt.reference(parent))),
                             this->astCtxt.bvxor(op1, op2)
                           )
                         )
                       ),
                       this->astCtxt.bvtrue()
                     );
        auto node2 = this->astCtxt.extract(1, 1, nzcv);
        auto node3 = this->getCodeConditionAst(inst, node1, node2);

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node3, cf, "Carry flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(cf, parent->isTainted);
      }


      void AArch64Semantics::vfAdd_s(triton::arch::Instruction& inst,
                                     const triton::engines::symbolic::SharedSymbolicExpression& parent,
                                     triton::arch::OperandWrapper& dst,
                                     triton::ast::SharedAbstractNode& op1,
                                     triton::ast::SharedAbstractNode& op2) {

        auto vf     = this->architecture->getRegister(ID_REG_AARCH64_V);
        auto bvSize = dst.getBitSize();
        auto low    = dst.getLow();
        auto high   = dst.getHigh();

        /*
         * Create the semantic.
         * vf = MSB((op1 ^ ~op2) & (op1 ^ result))
         */
        auto node = this->astCtxt.extract(bvSize-1, bvSize-1,
                      this->astCtxt.bvand(
                        this->astCtxt.bvxor(op1, this->astCtxt.bvnot(op2)),
                        this->astCtxt.bvxor(op1, this->astCtxt.extract(high, low, this->astCtxt.reference(parent)))
                      )
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, vf, "Overflow flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(vf, parent->isTainted);
      }


      void AArch64Semantics::vfSub_s(triton::arch::Instruction& inst,
                                     const triton::engines::symbolic::SharedSymbolicExpression& parent,
                                     triton::arch::OperandWrapper& dst,
                                     triton::ast::SharedAbstractNode& op1,
                                     triton::ast::SharedAbstractNode& op2) {

        auto vf     = this->architecture->getRegister(ID_REG_AARCH64_V);
        auto bvSize = dst.getBitSize();
        auto low    = dst.getLow();
        auto high   = dst.getHigh();

        /*
         * Create the semantic.
         * vf = MSB((op1 ^ op2) & (op1 ^ result))
         */
        auto node = this->astCtxt.extract(bvSize-1, bvSize-1,
                      this->astCtxt.bvand(
                        this->astCtxt.bvxor(op1, op2),
                        this->astCtxt.bvxor(op1, this->astCtxt.extract(high, low, this->astCtxt.reference(parent)))
                      )
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, vf, "Overflow flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(vf, parent->isTainted);
      }


      void AArch64Semantics::vfCcmp_s(triton::arch::Instruction& inst,
                                      const triton::engines::symbolic::SharedSymbolicExpression& parent,
                                      triton::arch::OperandWrapper& dst,
                                      triton::ast::SharedAbstractNode& op1,
                                      triton::ast::SharedAbstractNode& op2,
                                      triton::ast::SharedAbstractNode& nzcv) {

        auto vf     = this->architecture->getRegister(ID_REG_AARCH64_V);
        auto bvSize = dst.getBitSize();
        auto low    = dst.getLow();
        auto high   = dst.getHigh();

        /*
         * Create the semantic.
         * if cond == true:
         *   vf = MSB((op1 ^ op2) & (op1 ^ result))
         * else:
         *   vf = VF(nzcv)
         */
        auto node1 = this->astCtxt.extract(bvSize-1, bvSize-1,
                       this->astCtxt.bvand(
                         this->astCtxt.bvxor(op1, op2),
                         this->astCtxt.bvxor(op1, this->astCtxt.extract(high, low, this->astCtxt.reference(parent)))
                       )
                     );
        auto node2 = this->astCtxt.extract(0, 0, nzcv);
        auto node3 = this->getCodeConditionAst(inst, node1, node2);

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node3, vf, "Overflow flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(vf, parent->isTainted);
      }


      void AArch64Semantics::adc_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];
        auto  cf   = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_C));

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);
        auto op3 = this->symbolicEngine->getOperandAst(inst, cf);

        /* Create the semantics */
        auto node = this->astCtxt.bvadd(this->astCtxt.bvadd(op1, op2), this->astCtxt.zx(dst.getBitSize()-1, op3));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ADC operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2) | this->taintEngine->isTainted(cf));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::add_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.bvadd(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ADD(S) operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update symbolic flags */
        if (inst.isUpdateFlag() == true) {
          this->cfAdd_s(inst, expr, dst, op1, op2);
          this->nf_s(inst, expr, dst);
          this->vfAdd_s(inst, expr, dst, op1, op2);
          this->zf_s(inst, expr, dst);
        }

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::adr_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  pc  = triton::arch::OperandWrapper(this->architecture->getParentRegister(ID_REG_AARCH64_PC));

        /*
         * Note: Capstone already encodes the result into the source operand. We don't have
         * to compute the add operation but do we lose the symbolic?
         */
        /* Create symbolic semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ADR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src) | this->taintEngine->isTainted(pc));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::adrp_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  pc  = triton::arch::OperandWrapper(this->architecture->getParentRegister(ID_REG_AARCH64_PC));

        /*
         * Note: Capstone already encodes the result into the source operand. We don't have
         * to compute the add operation but do we lose the symbolic?
         */
        /* Create symbolic semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ADRP operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src) | this->taintEngine->isTainted(pc));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::and_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.bvand(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "AND(S) operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update symbolic flags */
        if (inst.isUpdateFlag() == true) {
          this->clearFlag_s(inst, this->architecture->getRegister(ID_REG_AARCH64_C), "Clears carry flag");
          this->nf_s(inst, expr, dst);
          this->clearFlag_s(inst, this->architecture->getRegister(ID_REG_AARCH64_V), "Clears overflow flag");
          this->zf_s(inst, expr, dst);
        }

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::asr_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.bvashr(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ASR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::b_s(triton::arch::Instruction& inst) {
        auto  dst = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_PC));
        auto& src = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src);
        auto op2 = this->astCtxt.bv(inst.getNextAddress(), dst.getBitSize());

        /* Create the semantics */
        auto node = this->getCodeConditionAst(inst, op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "B operation - Program Counter");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->getCodeConditionTainteSate(inst));
      }


      void AArch64Semantics::bl_s(triton::arch::Instruction& inst) {
        auto  dst1 = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_X30));
        auto  dst2 = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_PC));
        auto& src  = inst.operands[0];

        /* Create the semantics */
        auto node1 = this->astCtxt.bv(inst.getNextAddress(), dst1.getBitSize());
        auto node2 = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst1, "BL operation - Link Register");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, dst2, "BL operation - Program Counter");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst1, src);
        expr2->isTainted = this->taintEngine->taintAssignment(dst2, src);
      }


      void AArch64Semantics::blr_s(triton::arch::Instruction& inst) {
        auto  dst1 = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_X30));
        auto  dst2 = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_PC));
        auto& src  = inst.operands[0];

        /* Create the semantics */
        auto node1 = this->astCtxt.bv(inst.getNextAddress(), dst1.getBitSize());
        auto node2 = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst1, "BLR operation - Link Register");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, dst2, "BLR operation - Program Counter");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst1, src);
        expr2->isTainted = this->taintEngine->taintAssignment(dst2, src);
      }


      void AArch64Semantics::br_s(triton::arch::Instruction& inst) {
        auto  dst = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_PC));
        auto& src = inst.operands[0];

        /* Create the semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "BR operation - Program Counter");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);
      }


      void AArch64Semantics::cbnz_s(triton::arch::Instruction& inst) {
        auto  dst  = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_PC));
        auto& src1 = inst.operands[0];
        auto& src2 = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.ite(
                      this->astCtxt.lnot(this->astCtxt.equal(op1, this->astCtxt.bv(0, src1.getBitSize()))),
                      op2,
                      this->astCtxt.bv(inst.getNextAddress(), dst.getBitSize())
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CBNZ operation - Program Counter");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));
      }


      void AArch64Semantics::cbz_s(triton::arch::Instruction& inst) {
        auto  dst  = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_PC));
        auto& src1 = inst.operands[0];
        auto& src2 = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.ite(
                      this->astCtxt.equal(op1, this->astCtxt.bv(0, src1.getBitSize())),
                      op2,
                      this->astCtxt.bv(inst.getNextAddress(), dst.getBitSize())
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CBZ operation - Program Counter");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));
      }


      void AArch64Semantics::ccmp_s(triton::arch::Instruction& inst) {
        auto& src1  = inst.operands[0];
        auto& src2  = inst.operands[1];
        auto& src3  = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);
        auto op3 = this->symbolicEngine->getOperandAst(inst, src3);

        /* Create the semantics */
        auto node = this->astCtxt.bvsub(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicVolatileExpression(inst, node, "CCMP temporary operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2);

        /* Update symbolic flags */
        this->cfCcmp_s(inst, expr, src1, op1, op2, op3);
        this->nfCcmp_s(inst, expr, src1, op3);
        this->vfCcmp_s(inst, expr, src1, op1, op2, op3);
        this->zfCcmp_s(inst, expr, src1, op3);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::cinc_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src);
        auto op2 = this->astCtxt.bvadd(op1, this->astCtxt.bv(1, src.getBitSize()));

        /* Create the semantics */
        auto node = this->getCodeConditionAst(inst, op2, op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CINC operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->getCodeConditionTainteSate(inst));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::clz_s(triton::arch::Instruction& inst) {
        auto& dst     = inst.operands[0];
        auto& src     = inst.operands[1];
        auto  bvSize  = dst.getBitSize();

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        triton::ast::SharedAbstractNode node = nullptr;
        switch (src.getSize()) {
          case DWORD_SIZE:
            node = this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(31, 31, op), this->astCtxt.bvtrue()), this->astCtxt.bv(0, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(30, 30, op), this->astCtxt.bvtrue()), this->astCtxt.bv(1, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(29, 29, op), this->astCtxt.bvtrue()), this->astCtxt.bv(2, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(28, 28, op), this->astCtxt.bvtrue()), this->astCtxt.bv(3, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(27, 27, op), this->astCtxt.bvtrue()), this->astCtxt.bv(4, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(26, 26, op), this->astCtxt.bvtrue()), this->astCtxt.bv(5, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(25, 25, op), this->astCtxt.bvtrue()), this->astCtxt.bv(6, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(24, 24, op), this->astCtxt.bvtrue()), this->astCtxt.bv(7, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(23, 23, op), this->astCtxt.bvtrue()), this->astCtxt.bv(8, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(22, 22, op), this->astCtxt.bvtrue()), this->astCtxt.bv(9, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(21, 21, op), this->astCtxt.bvtrue()), this->astCtxt.bv(10, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(20, 20, op), this->astCtxt.bvtrue()), this->astCtxt.bv(11, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(19, 19, op), this->astCtxt.bvtrue()), this->astCtxt.bv(12, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(18, 18, op), this->astCtxt.bvtrue()), this->astCtxt.bv(13, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(17, 17, op), this->astCtxt.bvtrue()), this->astCtxt.bv(14, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(16, 16, op), this->astCtxt.bvtrue()), this->astCtxt.bv(15, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(15, 15, op), this->astCtxt.bvtrue()), this->astCtxt.bv(16, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(14, 14, op), this->astCtxt.bvtrue()), this->astCtxt.bv(17, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(13, 13, op), this->astCtxt.bvtrue()), this->astCtxt.bv(18, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(12, 12, op), this->astCtxt.bvtrue()), this->astCtxt.bv(19, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(11, 11, op), this->astCtxt.bvtrue()), this->astCtxt.bv(20, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(10, 10, op), this->astCtxt.bvtrue()), this->astCtxt.bv(21, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(9, 9, op), this->astCtxt.bvtrue()),   this->astCtxt.bv(22, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(8, 8, op), this->astCtxt.bvtrue()),   this->astCtxt.bv(23, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(7, 7, op), this->astCtxt.bvtrue()),   this->astCtxt.bv(24, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(6, 6, op), this->astCtxt.bvtrue()),   this->astCtxt.bv(25, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(5, 5, op), this->astCtxt.bvtrue()),   this->astCtxt.bv(26, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(4, 4, op), this->astCtxt.bvtrue()),   this->astCtxt.bv(27, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(3, 3, op), this->astCtxt.bvtrue()),   this->astCtxt.bv(28, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(2, 2, op), this->astCtxt.bvtrue()),   this->astCtxt.bv(29, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(1, 1, op), this->astCtxt.bvtrue()),   this->astCtxt.bv(30, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(0, 0, op), this->astCtxt.bvtrue()),   this->astCtxt.bv(31, bvSize),
                   this->astCtxt.bv(32, bvSize)
                   ))))))))))))))))))))))))))))))));
            break;

          case QWORD_SIZE:
            node = this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(63, 63, op), this->astCtxt.bvtrue()), this->astCtxt.bv(0, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(62, 62, op), this->astCtxt.bvtrue()), this->astCtxt.bv(1, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(61, 61, op), this->astCtxt.bvtrue()), this->astCtxt.bv(2, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(60, 60, op), this->astCtxt.bvtrue()), this->astCtxt.bv(3, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(59, 59, op), this->astCtxt.bvtrue()), this->astCtxt.bv(4, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(58, 58, op), this->astCtxt.bvtrue()), this->astCtxt.bv(5, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(57, 57, op), this->astCtxt.bvtrue()), this->astCtxt.bv(6, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(56, 56, op), this->astCtxt.bvtrue()), this->astCtxt.bv(7, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(55, 55, op), this->astCtxt.bvtrue()), this->astCtxt.bv(8, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(54, 54, op), this->astCtxt.bvtrue()), this->astCtxt.bv(9, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(53, 53, op), this->astCtxt.bvtrue()), this->astCtxt.bv(10, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(52, 52, op), this->astCtxt.bvtrue()), this->astCtxt.bv(11, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(51, 51, op), this->astCtxt.bvtrue()), this->astCtxt.bv(12, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(50, 50, op), this->astCtxt.bvtrue()), this->astCtxt.bv(13, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(49, 49, op), this->astCtxt.bvtrue()), this->astCtxt.bv(14, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(48, 48, op), this->astCtxt.bvtrue()), this->astCtxt.bv(15, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(47, 47, op), this->astCtxt.bvtrue()), this->astCtxt.bv(16, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(46, 46, op), this->astCtxt.bvtrue()), this->astCtxt.bv(17, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(45, 45, op), this->astCtxt.bvtrue()), this->astCtxt.bv(18, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(44, 44, op), this->astCtxt.bvtrue()), this->astCtxt.bv(19, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(43, 43, op), this->astCtxt.bvtrue()), this->astCtxt.bv(20, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(42, 42, op), this->astCtxt.bvtrue()), this->astCtxt.bv(21, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(41, 41, op), this->astCtxt.bvtrue()), this->astCtxt.bv(22, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(40, 40, op), this->astCtxt.bvtrue()), this->astCtxt.bv(23, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(39, 39, op), this->astCtxt.bvtrue()), this->astCtxt.bv(24, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(38, 38, op), this->astCtxt.bvtrue()), this->astCtxt.bv(25, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(37, 37, op), this->astCtxt.bvtrue()), this->astCtxt.bv(26, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(36, 36, op), this->astCtxt.bvtrue()), this->astCtxt.bv(27, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(35, 35, op), this->astCtxt.bvtrue()), this->astCtxt.bv(28, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(34, 34, op), this->astCtxt.bvtrue()), this->astCtxt.bv(29, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(33, 33, op), this->astCtxt.bvtrue()), this->astCtxt.bv(30, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(32, 32, op), this->astCtxt.bvtrue()), this->astCtxt.bv(31, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(31, 31, op), this->astCtxt.bvtrue()), this->astCtxt.bv(32, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(30, 30, op), this->astCtxt.bvtrue()), this->astCtxt.bv(33, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(29, 29, op), this->astCtxt.bvtrue()), this->astCtxt.bv(34, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(28, 28, op), this->astCtxt.bvtrue()), this->astCtxt.bv(35, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(27, 27, op), this->astCtxt.bvtrue()), this->astCtxt.bv(36, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(26, 26, op), this->astCtxt.bvtrue()), this->astCtxt.bv(37, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(25, 25, op), this->astCtxt.bvtrue()), this->astCtxt.bv(38, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(24, 24, op), this->astCtxt.bvtrue()), this->astCtxt.bv(39, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(23, 23, op), this->astCtxt.bvtrue()), this->astCtxt.bv(40, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(22, 22, op), this->astCtxt.bvtrue()), this->astCtxt.bv(41, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(21, 21, op), this->astCtxt.bvtrue()), this->astCtxt.bv(42, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(20, 20, op), this->astCtxt.bvtrue()), this->astCtxt.bv(43, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(19, 19, op), this->astCtxt.bvtrue()), this->astCtxt.bv(44, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(18, 18, op), this->astCtxt.bvtrue()), this->astCtxt.bv(45, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(17, 17, op), this->astCtxt.bvtrue()), this->astCtxt.bv(46, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(16, 16, op), this->astCtxt.bvtrue()), this->astCtxt.bv(47, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(15, 15, op), this->astCtxt.bvtrue()), this->astCtxt.bv(48, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(14, 14, op), this->astCtxt.bvtrue()), this->astCtxt.bv(49, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(13, 13, op), this->astCtxt.bvtrue()), this->astCtxt.bv(50, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(12, 12, op), this->astCtxt.bvtrue()), this->astCtxt.bv(51, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(11, 11, op), this->astCtxt.bvtrue()), this->astCtxt.bv(52, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(10, 10, op), this->astCtxt.bvtrue()), this->astCtxt.bv(53, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(9, 9, op),   this->astCtxt.bvtrue()), this->astCtxt.bv(54, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(8, 8, op),   this->astCtxt.bvtrue()), this->astCtxt.bv(55, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(7, 7, op),   this->astCtxt.bvtrue()), this->astCtxt.bv(56, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(6, 6, op),   this->astCtxt.bvtrue()), this->astCtxt.bv(57, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(5, 5, op),   this->astCtxt.bvtrue()), this->astCtxt.bv(58, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(4, 4, op),   this->astCtxt.bvtrue()), this->astCtxt.bv(59, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(3, 3, op),   this->astCtxt.bvtrue()), this->astCtxt.bv(60, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(2, 2, op),   this->astCtxt.bvtrue()), this->astCtxt.bv(61, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(1, 1, op),   this->astCtxt.bvtrue()), this->astCtxt.bv(62, bvSize),
                   this->astCtxt.ite(this->astCtxt.equal(this->astCtxt.extract(0, 0, op),   this->astCtxt.bvtrue()), this->astCtxt.bv(63, bvSize),
                   this->astCtxt.bv(64, bvSize)
                   ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
            break;

          default:
            throw triton::exceptions::Semantics("AArch64Semantics::clz_s(): Invalid operand size.");
        }

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CLZ operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::cmn_s(triton::arch::Instruction& inst) {
        auto& src1 = inst.operands[0];
        auto& src2 = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.bvadd(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicVolatileExpression(inst, node, "CMN operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2);

        /* Update symbolic flags */
        this->cfAdd_s(inst, expr, src1, op1, op2);
        this->nf_s(inst, expr, src1);
        this->vfAdd_s(inst, expr, src1, op1, op2);
        this->zf_s(inst, expr, src1);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::cmp_s(triton::arch::Instruction& inst) {
        auto& src1 = inst.operands[0];
        auto& src2 = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.bvsub(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicVolatileExpression(inst, node, "CMP operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2);

        /* Update symbolic flags */
        this->cfSub_s(inst, expr, src1, op1, op2);
        this->nf_s(inst, expr, src1);
        this->vfSub_s(inst, expr, src1, op1, op2);
        this->zf_s(inst, expr, src1);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::csel_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->getCodeConditionAst(inst, op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CSEL operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::cset_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->astCtxt.bv(1, dst.getBitSize());
        auto op2 = this->astCtxt.bv(0, dst.getBitSize());

        /* Create the semantics */
        auto node = this->getCodeConditionAst(inst, op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CSET operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->getCodeConditionTainteSate(inst));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::csinc_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->astCtxt.bvadd(
                     this->symbolicEngine->getOperandAst(inst, src2),
                     this->astCtxt.bv(1, src2.getBitSize())
                   );

        /* Create the semantics */
        auto node = this->getCodeConditionAst(inst, op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CSINC operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::csneg_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->astCtxt.bvneg(this->symbolicEngine->getOperandAst(inst, src2));

        /* Create the semantics */
        auto node = this->getCodeConditionAst(inst, op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CSNEG operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::eon_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.bvxnor(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "EON operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::eor_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.bvxor(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "EOR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::extr_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];
        auto& src3 = inst.operands[3];
        auto  lsb  = src3.getImmediate().getValue();

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.extract(lsb + dst.getBitSize() - 1, lsb, this->astCtxt.concat(op1, op2));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "EXTR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2) | this->taintEngine->isTainted(src3));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ldar_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& dst = inst.operands[0];
        triton::arch::OperandWrapper& src = inst.operands[1];

        /* Create the semantics of the LOAD */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LDAR operation - LOAD access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ldarb_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& dst = inst.operands[0];
        triton::arch::OperandWrapper& src = inst.operands[1];

        /* Special behavior: Define that the size of the memory access is 8 bits */
        src.getMemory().setPair(std::make_pair(7, 0));

        /* Create the semantics of the LOAD */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LDARB operation - LOAD access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ldarh_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& dst = inst.operands[0];
        triton::arch::OperandWrapper& src = inst.operands[1];

        /* Special behavior: Define that the size of the memory access is 16 bits */
        src.getMemory().setPair(std::make_pair(15, 0));

        /* Create the semantics of the LOAD */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LDARH operation - LOAD access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ldaxr_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& dst = inst.operands[0];
        triton::arch::OperandWrapper& src = inst.operands[1];

        /* Create the semantics of the LOAD */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LDAXR operation - LOAD access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ldaxrb_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& dst = inst.operands[0];
        triton::arch::OperandWrapper& src = inst.operands[1];

        /* Special behavior: Define that the size of the memory access is 8 bits */
        src.getMemory().setPair(std::make_pair(7, 0));

        /* Create the semantics of the LOAD */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LDAXRB operation - LOAD access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ldaxrh_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& dst = inst.operands[0];
        triton::arch::OperandWrapper& src = inst.operands[1];

        /* Special behavior: Define that the size of the memory access is 16 bits */
        src.getMemory().setPair(std::make_pair(15, 0));

        /* Create the semantics of the LOAD */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LDAXRH operation - LOAD access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ldp_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& dst1 = inst.operands[0];
        triton::arch::OperandWrapper& dst2 = inst.operands[1];
        triton::arch::OperandWrapper& src  = inst.operands[2];

        /* Special behavior: Define that the size of the memory access is dst1.size + dst2.size */
        src.getMemory().setPair(std::make_pair((dst1.getBitSize() + dst2.getBitSize()) - 1, 0));

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node1 = this->astCtxt.extract((dst1.getBitSize() - 1), 0, op);
        auto node2 = this->astCtxt.extract((dst1.getBitSize() + dst2.getBitSize()) - 1, dst1.getBitSize(), op);

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst1, "LDP operation - LOAD access");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, dst2, "LDP operation - LOAD access");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst1, src);
        expr2->isTainted = this->taintEngine->taintAssignment(dst2, src);

        /* Optional behavior. Post computation of the base register */
        /* LDP <Xt1>, <Xt2>, [<Xn|SP>], #<imm> */
        if (inst.operands.size() == 4) {
          triton::arch::Immediate& imm = inst.operands[3].getImmediate();
          triton::arch::Register& base = src.getMemory().getBaseRegister();

          /* Create symbolic operands of the post computation */
          auto baseNode = this->symbolicEngine->getOperandAst(inst, base);
          auto immNode  = this->symbolicEngine->getOperandAst(inst, imm);

          /* Create the semantics of the base register */
          auto node2 = this->astCtxt.bvadd(baseNode, this->astCtxt.sx(base.getBitSize() - imm.getBitSize(), immNode));

          /* Create symbolic expression */
          auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, base, "LDP operation - Base register computation");

          /* Spread taint */
          expr2->isTainted = this->taintEngine->isTainted(base);
        }

        /* LDP <Xt1>, <Xt2>, [<Xn|SP>, #<imm>]! */
        else if (inst.operands.size() == 3 && inst.isWriteBack() == true) {
          triton::arch::Register& base = src.getMemory().getBaseRegister();

          /* Create the semantics of the base register */
          auto node3 = src.getMemory().getLeaAst();

          /* Create symbolic expression */
          auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, base, "LDP operation - Base register computation");

          /* Spread taint */
          expr3->isTainted = this->taintEngine->isTainted(base);
        }

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ldr_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& dst = inst.operands[0];
        triton::arch::OperandWrapper& src = inst.operands[1];

        /* Create the semantics of the LOAD */
        auto node1 = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "LDR operation - LOAD access");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Optional behavior. Post computation of the base register */
        /* LDR <Xt>, [<Xn|SP>], #<simm> */
        if (inst.operands.size() == 3) {
          triton::arch::Immediate& imm = inst.operands[2].getImmediate();
          triton::arch::Register& base = src.getMemory().getBaseRegister();

          /* Create symbolic operands of the post computation */
          auto baseNode = this->symbolicEngine->getOperandAst(inst, base);
          auto immNode  = this->symbolicEngine->getOperandAst(inst, imm);

          /* Create the semantics of the base register */
          auto node2 = this->astCtxt.bvadd(baseNode, this->astCtxt.sx(base.getBitSize() - imm.getBitSize(), immNode));

          /* Create symbolic expression */
          auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, base, "LDR operation - Base register computation");

          /* Spread taint */
          expr2->isTainted = this->taintEngine->isTainted(base);
        }

        /* LDR <Xt>, [<Xn|SP>, #<simm>]! */
        else if (inst.operands.size() == 2 && inst.isWriteBack() == true) {
          triton::arch::Register& base = src.getMemory().getBaseRegister();

          /* Create the semantics of the base register */
          auto node3 = src.getMemory().getLeaAst();

          /* Create symbolic expression */
          auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, base, "LDR operation - Base register computation");

          /* Spread taint */
          expr3->isTainted = this->taintEngine->isTainted(base);
        }

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ldrb_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& dst = inst.operands[0];
        triton::arch::OperandWrapper& src = inst.operands[1];

        /* Special behavior: Define that the size of the memory access is 8 bits */
        src.getMemory().setPair(std::make_pair(7, 0));

        /* Create the semantics of the LOAD */
        auto node1 = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "LDRB operation - LOAD access");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Optional behavior. Post computation of the base register */
        /* LDRB <Xt>, [<Xn|SP>], #<simm> */
        if (inst.operands.size() == 3) {
          triton::arch::Immediate& imm = inst.operands[2].getImmediate();
          triton::arch::Register& base = src.getMemory().getBaseRegister();

          /* Create symbolic operands of the post computation */
          auto baseNode = this->symbolicEngine->getOperandAst(inst, base);
          auto immNode  = this->symbolicEngine->getOperandAst(inst, imm);

          /* Create the semantics of the base register */
          auto node2 = this->astCtxt.bvadd(baseNode, this->astCtxt.sx(base.getBitSize() - imm.getBitSize(), immNode));

          /* Create symbolic expression */
          auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, base, "LDRB operation - Base register computation");

          /* Spread taint */
          expr2->isTainted = this->taintEngine->isTainted(base);
        }

        /* LDRB <Xt>, [<Xn|SP>, #<simm>]! */
        else if (inst.operands.size() == 2 && inst.isWriteBack() == true) {
          triton::arch::Register& base = src.getMemory().getBaseRegister();

          /* Create the semantics of the base register */
          auto node3 = src.getMemory().getLeaAst();

          /* Create symbolic expression */
          auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, base, "LDRB operation - Base register computation");

          /* Spread taint */
          expr3->isTainted = this->taintEngine->isTainted(base);
        }

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ldrh_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& dst = inst.operands[0];
        triton::arch::OperandWrapper& src = inst.operands[1];

        /* Special behavior: Define that the size of the memory access is 16 bits */
        src.getMemory().setPair(std::make_pair(15, 0));

        /* Create the semantics of the LOAD */
        auto node1 = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "LDRH operation - LOAD access");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Optional behavior. Post computation of the base register */
        /* LDRH <Xt>, [<Xn|SP>], #<simm> */
        if (inst.operands.size() == 3) {
          triton::arch::Immediate& imm = inst.operands[2].getImmediate();
          triton::arch::Register& base = src.getMemory().getBaseRegister();

          /* Create symbolic operands of the post computation */
          auto baseNode = this->symbolicEngine->getOperandAst(inst, base);
          auto immNode  = this->symbolicEngine->getOperandAst(inst, imm);

          /* Create the semantics of the base register */
          auto node2 = this->astCtxt.bvadd(baseNode, this->astCtxt.sx(base.getBitSize() - imm.getBitSize(), immNode));

          /* Create symbolic expression */
          auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, base, "LDRH operation - Base register computation");

          /* Spread taint */
          expr2->isTainted = this->taintEngine->isTainted(base);
        }

        /* LDRH <Xt>, [<Xn|SP>, #<simm>]! */
        else if (inst.operands.size() == 2 && inst.isWriteBack() == true) {
          triton::arch::Register& base = src.getMemory().getBaseRegister();

          /* Create the semantics of the base register */
          auto node3 = src.getMemory().getLeaAst();

          /* Create symbolic expression */
          auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, base, "LDRH operation - Base register computation");

          /* Spread taint */
          expr3->isTainted = this->taintEngine->isTainted(base);
        }

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ldrsb_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& dst = inst.operands[0];
        triton::arch::OperandWrapper& src = inst.operands[1];

        /* Special behavior: Define that the size of the memory access is 8 bits */
        src.getMemory().setPair(std::make_pair(7, 0));

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics of the LOAD */
        auto node1 = this->astCtxt.sx(dst.getBitSize() - 8, op);

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "LDRSB operation - LOAD access");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Optional behavior. Post computation of the base register */
        /* LDRSB <Xt>, [<Xn|SP>], #<simm> */
        if (inst.operands.size() == 3) {
          triton::arch::Immediate& imm = inst.operands[2].getImmediate();
          triton::arch::Register& base = src.getMemory().getBaseRegister();

          /* Create symbolic operands of the post computation */
          auto baseNode = this->symbolicEngine->getOperandAst(inst, base);
          auto immNode  = this->symbolicEngine->getOperandAst(inst, imm);

          /* Create the semantics of the base register */
          auto node2 = this->astCtxt.bvadd(baseNode, this->astCtxt.sx(base.getBitSize() - imm.getBitSize(), immNode));

          /* Create symbolic expression */
          auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, base, "LDRSB operation - Base register computation");

          /* Spread taint */
          expr2->isTainted = this->taintEngine->isTainted(base);
        }

        /* LDRSB <Xt>, [<Xn|SP>, #<simm>]! */
        else if (inst.operands.size() == 2 && inst.isWriteBack() == true) {
          triton::arch::Register& base = src.getMemory().getBaseRegister();

          /* Create the semantics of the base register */
          auto node3 = src.getMemory().getLeaAst();

          /* Create symbolic expression */
          auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, base, "LDRSB operation - Base register computation");

          /* Spread taint */
          expr3->isTainted = this->taintEngine->isTainted(base);
        }

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ldrsh_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& dst = inst.operands[0];
        triton::arch::OperandWrapper& src = inst.operands[1];

        /* Special behavior: Define that the size of the memory access is 16 bits */
        src.getMemory().setPair(std::make_pair(15, 0));

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics of the LOAD */
        auto node1 = this->astCtxt.sx(dst.getBitSize() - 16, op);

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "LDRSH operation - LOAD access");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Optional behavior. Post computation of the base register */
        /* LDRSH <Xt>, [<Xn|SP>], #<simm> */
        if (inst.operands.size() == 3) {
          triton::arch::Immediate& imm = inst.operands[2].getImmediate();
          triton::arch::Register& base = src.getMemory().getBaseRegister();

          /* Create symbolic operands of the post computation */
          auto baseNode = this->symbolicEngine->getOperandAst(inst, base);
          auto immNode  = this->symbolicEngine->getOperandAst(inst, imm);

          /* Create the semantics of the base register */
          auto node2 = this->astCtxt.bvadd(baseNode, this->astCtxt.sx(base.getBitSize() - imm.getBitSize(), immNode));

          /* Create symbolic expression */
          auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, base, "LDRSH operation - Base register computation");

          /* Spread taint */
          expr2->isTainted = this->taintEngine->isTainted(base);
        }

        /* LDRSH <Xt>, [<Xn|SP>, #<simm>]! */
        else if (inst.operands.size() == 2 && inst.isWriteBack() == true) {
          triton::arch::Register& base = src.getMemory().getBaseRegister();

          /* Create the semantics of the base register */
          auto node3 = src.getMemory().getLeaAst();

          /* Create symbolic expression */
          auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, base, "LDRSH operation - Base register computation");

          /* Spread taint */
          expr3->isTainted = this->taintEngine->isTainted(base);
        }

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ldrsw_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& dst = inst.operands[0];
        triton::arch::OperandWrapper& src = inst.operands[1];

        /* Special behavior: Define that the size of the memory access is 32 bits */
        src.getMemory().setPair(std::make_pair(31, 0));

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics of the LOAD */
        auto node1 = this->astCtxt.sx(dst.getBitSize() - 32, op);

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "LDRSW operation - LOAD access");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Optional behavior. Post computation of the base register */
        /* LDRSW <Xt>, [<Xn|SP>], #<simm> */
        if (inst.operands.size() == 3) {
          triton::arch::Immediate& imm = inst.operands[2].getImmediate();
          triton::arch::Register& base = src.getMemory().getBaseRegister();

          /* Create symbolic operands of the post computation */
          auto baseNode = this->symbolicEngine->getOperandAst(inst, base);
          auto immNode  = this->symbolicEngine->getOperandAst(inst, imm);

          /* Create the semantics of the base register */
          auto node2 = this->astCtxt.bvadd(baseNode, this->astCtxt.sx(base.getBitSize() - imm.getBitSize(), immNode));

          /* Create symbolic expression */
          auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, base, "LDRSW operation - Base register computation");

          /* Spread taint */
          expr2->isTainted = this->taintEngine->isTainted(base);
        }

        /* LDRSW <Xt>, [<Xn|SP>, #<simm>]! */
        else if (inst.operands.size() == 2 && inst.isWriteBack() == true) {
          triton::arch::Register& base = src.getMemory().getBaseRegister();

          /* Create the semantics of the base register */
          auto node3 = src.getMemory().getLeaAst();

          /* Create symbolic expression */
          auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, base, "LDRSW operation - Base register computation");

          /* Spread taint */
          expr3->isTainted = this->taintEngine->isTainted(base);
        }

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ldur_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& dst = inst.operands[0];
        triton::arch::OperandWrapper& src = inst.operands[1];

        /* Create the semantics of the LOAD */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LDUR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ldurb_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& dst = inst.operands[0];
        triton::arch::OperandWrapper& src = inst.operands[1];

        /* Special behavior: Define that the size of the memory access is 8 bits */
        src.getMemory().setPair(std::make_pair(7, 0));

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node = this->astCtxt.zx(dst.getBitSize() - 8, op);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LDURB operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ldurh_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& dst = inst.operands[0];
        triton::arch::OperandWrapper& src = inst.operands[1];

        /* Special behavior: Define that the size of the memory access is 16 bits */
        src.getMemory().setPair(std::make_pair(15, 0));

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node = this->astCtxt.zx(dst.getBitSize() - 16, op);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LDURH operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ldursb_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& dst = inst.operands[0];
        triton::arch::OperandWrapper& src = inst.operands[1];

        /* Special behavior: Define that the size of the memory access is 8 bits */
        src.getMemory().setPair(std::make_pair(7, 0));

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node = this->astCtxt.sx(dst.getBitSize() - 8, op);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LDURSB operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ldursh_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& dst = inst.operands[0];
        triton::arch::OperandWrapper& src = inst.operands[1];

        /* Special behavior: Define that the size of the memory access is 16 bits */
        src.getMemory().setPair(std::make_pair(15, 0));

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node = this->astCtxt.sx(dst.getBitSize() - 16, op);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LDURSH operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ldursw_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& dst = inst.operands[0];
        triton::arch::OperandWrapper& src = inst.operands[1];

        /* Special behavior: Define that the size of the memory access is 32 bits */
        src.getMemory().setPair(std::make_pair(31, 0));

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node = this->astCtxt.sx(dst.getBitSize() - 32, op);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LDURSW operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ldxr_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& dst = inst.operands[0];
        triton::arch::OperandWrapper& src = inst.operands[1];

        /* Create the semantics of the LOAD */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LDXR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ldxrb_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& dst = inst.operands[0];
        triton::arch::OperandWrapper& src = inst.operands[1];

        /* Special behavior: Define that the size of the memory access is 8 bits */
        src.getMemory().setPair(std::make_pair(7, 0));

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node = this->astCtxt.zx(dst.getBitSize() - 8, op);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LDXRB operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ldxrh_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& dst = inst.operands[0];
        triton::arch::OperandWrapper& src = inst.operands[1];

        /* Special behavior: Define that the size of the memory access is 16 bits */
        src.getMemory().setPair(std::make_pair(15, 0));

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node = this->astCtxt.zx(dst.getBitSize() - 16, op);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LDXRH operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::lsl_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];
        auto  size = src2.getBitSize();

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->astCtxt.bvand(
                     this->symbolicEngine->getOperandAst(inst, src2),
                     this->astCtxt.bv(size - 1,  size)
                   );

        /* Create the semantics */
        auto node = this->astCtxt.bvshl(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LSL operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::lsr_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];
        auto  size = src2.getBitSize();

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->astCtxt.bvand(
                     this->symbolicEngine->getOperandAst(inst, src2),
                     this->astCtxt.bv(size - 1,  size)
                   );

        /* Create the semantics */
        auto node = this->astCtxt.bvlshr(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LSR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::madd_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];
        auto& src3 = inst.operands[3];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);
        auto op3 = this->symbolicEngine->getOperandAst(inst, src3);

        /* Create the semantics */
        auto node = this->astCtxt.bvadd(op3, this->astCtxt.bvmul(op1, op2));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MADD operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2) | this->taintEngine->isTainted(src3));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::mneg_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.bvneg(this->astCtxt.bvmul(op1, op2));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MNEG operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::mov_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create the semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOV operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::movk_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  pos = src.getImmediate().getShiftValue(); // 0 by default.

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, dst);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        std::list<triton::ast::SharedAbstractNode> bits;

        switch (pos) {
          case 0:
            // [------------------------------------------------xxxxxxxxxxxxxxxx]
            bits.push_back(this->astCtxt.extract(dst.getHigh(), 16, op1));
            bits.push_back(this->astCtxt.extract(15, 0, op2));
            break;

          case 16:
            // [--------------------------------xxxxxxxxxxxxxxxx----------------]
            if (dst.getBitSize() == 64) {
              /*
               * The case where the instruction is: MOVK <Xd>, #<imm>{, LSL #<shift>}.
               * Otherwise if the instruction is: MOVK <Wd>, #<imm>{, LSL #<shift>}, just
               * skip this extract.
               */
              bits.push_back(this->astCtxt.extract(dst.getHigh(), 32, op1));
            }
            bits.push_back(this->astCtxt.extract(31, 16, op2));
            bits.push_back(this->astCtxt.extract(15, 0, op1));
            break;

          case 32:
            // [----------------xxxxxxxxxxxxxxxx--------------------------------]
            bits.push_back(this->astCtxt.extract(dst.getHigh(), 48, op1));
            bits.push_back(this->astCtxt.extract(47, 32, op2));
            bits.push_back(this->astCtxt.extract(31, 0, op1));
            break;

          case 48:
            // [xxxxxxxxxxxxxxxx------------------------------------------------]
            bits.push_back(this->astCtxt.extract(63, 48, op2));
            bits.push_back(this->astCtxt.extract(47, 0, op1));
            break;

          default:
            throw triton::exceptions::Semantics("AArch64Semantics::movk_s(): Invalid pos (hw field) encoding.");
        }

        auto node = this->astCtxt.concat(bits);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVK operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::movn_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node = this->astCtxt.bvnot(op);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVN operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::movz_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create the semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVZ operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::msub_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];
        auto& src3 = inst.operands[3];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);
        auto op3 = this->symbolicEngine->getOperandAst(inst, src3);

        /* Create the semantics */
        auto node = this->astCtxt.bvsub(op3, this->astCtxt.bvmul(op1, op2));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MSUB operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2) | this->taintEngine->isTainted(src3));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::mul_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.bvmul(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MUL operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::mvn_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node = this->astCtxt.bvnot(op);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MVN operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::neg_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node = this->astCtxt.bvneg(op);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MEG operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::nop_s(triton::arch::Instruction& inst) {
        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::orn_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.bvor(op1, this->astCtxt.bvnot(op2));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ORN operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::orr_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.bvor(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ORR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::rbit_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        std::list<triton::ast::SharedAbstractNode> bits;

        for (triton::uint32 index = 0; index < src.getBitSize(); index++) {
          bits.push_back(this->astCtxt.extract(index, index, op));
        }

        auto node = this->astCtxt.concat(bits);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "RBIT operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ret_s(triton::arch::Instruction& inst) {
        auto dst = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_PC));
        auto src = ((inst.operands.size() == 1) ? inst.operands[0] : triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_X30)));

        /* Create the semantics */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "RET operation - Program Counter");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);
      }


      void AArch64Semantics::rev_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        std::list<triton::ast::SharedAbstractNode> bits;

        switch(src.getSize()) {
          case QWORD_SIZE:
              bits.push_front(this->astCtxt.extract(63, 56, op));
              bits.push_front(this->astCtxt.extract(55, 48, op));
              bits.push_front(this->astCtxt.extract(47, 40, op));
              bits.push_front(this->astCtxt.extract(39, 32, op));
          case DWORD_SIZE:
              bits.push_front(this->astCtxt.extract(31, 24, op));
              bits.push_front(this->astCtxt.extract(23, 16, op));
              bits.push_front(this->astCtxt.extract(15, 8,  op));
              bits.push_front(this->astCtxt.extract(7,  0,  op));
            break;

          default:
            throw triton::exceptions::Semantics("AArch64Semantics::rev_s(): Invalid operand size.");
        }

        auto node = this->astCtxt.concat(bits);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "REV operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::rev16_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        std::list<triton::ast::SharedAbstractNode> bits;

        switch(src.getSize()) {
          case QWORD_SIZE:
              bits.push_back(this->astCtxt.extract(55, 48, op));
              bits.push_back(this->astCtxt.extract(63, 56, op));
              bits.push_back(this->astCtxt.extract(39, 32, op));
              bits.push_back(this->astCtxt.extract(47, 40, op));
          case DWORD_SIZE:
              bits.push_back(this->astCtxt.extract(23, 16, op));
              bits.push_back(this->astCtxt.extract(31, 24, op));
              bits.push_back(this->astCtxt.extract(7,  0,  op));
              bits.push_back(this->astCtxt.extract(15, 8,  op));
            break;

          default:
            throw triton::exceptions::Semantics("AArch64Semantics::rev16_s(): Invalid operand size.");
        }

        auto node = this->astCtxt.concat(bits);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "REV16 operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::rev32_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        std::list<triton::ast::SharedAbstractNode> bits;

        bits.push_back(this->astCtxt.extract(39, 32, op));
        bits.push_back(this->astCtxt.extract(47, 40, op));
        bits.push_back(this->astCtxt.extract(55, 48, op));
        bits.push_back(this->astCtxt.extract(63, 56, op));
        bits.push_back(this->astCtxt.extract(7,  0,  op));
        bits.push_back(this->astCtxt.extract(15, 8,  op));
        bits.push_back(this->astCtxt.extract(23, 16, op));
        bits.push_back(this->astCtxt.extract(31, 24, op));

        auto node = this->astCtxt.concat(bits);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "REV32 operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ror_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.bvror(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ROR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::sbfx_s(triton::arch::Instruction& inst) {
        auto& dst   = inst.operands[0];
        auto& src1  = inst.operands[1];
        auto& src2  = inst.operands[2];
        auto& src3  = inst.operands[3];
        auto  lsb   = src2.getImmediate().getValue();
        auto  width = src3.getImmediate().getValue();

        if (lsb + width > dst.getBitSize())
          throw triton::exceptions::Semantics("AArch64Semantics::sbfx_s(): Invalid lsb and width.");

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src1);

        /* Create the semantics */
        auto node = this->astCtxt.sx(dst.getBitSize() - width, this->astCtxt.extract(lsb+width-1, lsb, op));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SBFX operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src1);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::sdiv_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.ite(
                      this->astCtxt.equal(op2, this->astCtxt.bv(0, op2->getBitvectorSize())),
                      this->astCtxt.bv(0, dst.getBitSize()),
                      this->astCtxt.bvsdiv(op1, op2)
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SDIV operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::smaddl_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];
        auto& src3 = inst.operands[3];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);
        auto op3 = this->symbolicEngine->getOperandAst(inst, src3);

        /* Create the semantics */
        auto node = this->astCtxt.bvadd(
                      op3,
                      this->astCtxt.bvmul(
                        this->astCtxt.sx(DWORD_SIZE_BIT, op1),
                        this->astCtxt.sx(DWORD_SIZE_BIT, op2)
                      )
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SMADDL operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2) | this->taintEngine->isTainted(src3));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::smsubl_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];
        auto& src3 = inst.operands[3];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);
        auto op3 = this->symbolicEngine->getOperandAst(inst, src3);

        /* Create the semantics */
        auto node = this->astCtxt.bvsub(
                      op3,
                      this->astCtxt.bvmul(
                        this->astCtxt.sx(DWORD_SIZE_BIT, op1),
                        this->astCtxt.sx(DWORD_SIZE_BIT, op2)
                      )
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SMSUBL operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2) | this->taintEngine->isTainted(src3));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::smulh_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.extract(
                      DQWORD_SIZE_BIT-1,
                      QWORD_SIZE_BIT,
                      this->astCtxt.bvmul(
                        this->astCtxt.sx(QWORD_SIZE_BIT, op1),
                        this->astCtxt.sx(QWORD_SIZE_BIT, op2)
                      )
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SMULH operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::smull_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.bvmul(
                      this->astCtxt.sx(DWORD_SIZE_BIT, op1),
                      this->astCtxt.sx(DWORD_SIZE_BIT, op2)
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SMULL operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::stlr_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& src = inst.operands[0];
        triton::arch::OperandWrapper& dst = inst.operands[1];

        /* Create the semantics of the STORE */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "STLR operation - STORE access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::stlrb_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& src = inst.operands[0];
        triton::arch::OperandWrapper& dst = inst.operands[1];

        /* Create the semantics of the STORE */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Special behavior: Define that the size of the memory access is 8 bits */
        dst.getMemory().setPair(std::make_pair(7, 0));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "STLRB operation - STORE access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::stlrh_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& src = inst.operands[0];
        triton::arch::OperandWrapper& dst = inst.operands[1];

        /* Create the semantics of the STORE */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Special behavior: Define that the size of the memory access is 16 bits */
        dst.getMemory().setPair(std::make_pair(15, 0));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "STLRH operation - STORE access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::stp_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& src1 = inst.operands[0];
        triton::arch::OperandWrapper& src2 = inst.operands[1];
        triton::arch::OperandWrapper& dst  = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.concat(op2, op1);

        /* Special behavior: Define that the size of the memory access is src1.size + src2.size */
        dst.getMemory().setPair(std::make_pair(node->getBitvectorSize()-1, 0));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "STP operation - STORE access");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Optional behavior. Post computation of the base register */
        /* STP <Xt1>, <Xt2>, [<Xn|SP>], #<imm> */
        if (inst.operands.size() == 4) {
          triton::arch::Immediate& imm = inst.operands[3].getImmediate();
          triton::arch::Register& base = dst.getMemory().getBaseRegister();

          /* Create symbolic operands of the post computation */
          auto baseNode = this->symbolicEngine->getOperandAst(inst, base);
          auto immNode  = this->symbolicEngine->getOperandAst(inst, imm);

          /* Create the semantics of the base register */
          auto node2 = this->astCtxt.bvadd(baseNode, this->astCtxt.sx(base.getBitSize() - imm.getBitSize(), immNode));

          /* Create symbolic expression */
          auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, base, "STP operation - Base register computation");

          /* Spread taint */
          expr2->isTainted = this->taintEngine->isTainted(base);
        }

        /* STP <Xt1>, <Xt2>, [<Xn|SP>, #<imm>]! */
        else if (inst.operands.size() == 3 && inst.isWriteBack() == true) {
          triton::arch::Register& base = dst.getMemory().getBaseRegister();

          /* Create the semantics of the base register */
          auto node3 = dst.getMemory().getLeaAst();

          /* Create symbolic expression */
          auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, base, "STP operation - Base register computation");

          /* Spread taint */
          expr3->isTainted = this->taintEngine->isTainted(base);
        }

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::str_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& src = inst.operands[0];
        triton::arch::OperandWrapper& dst = inst.operands[1];

        /* Create the semantics of the STORE */
        auto node1 = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "STR operation - STORE access");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Optional behavior. Post computation of the base register */
        /* STR <Xt>, [<Xn|SP>], #<simm> */
        if (inst.operands.size() == 3) {
          triton::arch::Immediate& imm = inst.operands[2].getImmediate();
          triton::arch::Register& base = dst.getMemory().getBaseRegister();

          /* Create symbolic operands of the post computation */
          auto baseNode = this->symbolicEngine->getOperandAst(inst, base);
          auto immNode  = this->symbolicEngine->getOperandAst(inst, imm);

          /* Create the semantics of the base register */
          auto node2 = this->astCtxt.bvadd(baseNode, this->astCtxt.sx(base.getBitSize() - imm.getBitSize(), immNode));

          /* Create symbolic expression */
          auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, base, "STR operation - Base register computation");

          /* Spread taint */
          expr2->isTainted = this->taintEngine->isTainted(base);
        }

        /* STR <Xt>, [<Xn|SP>, #<simm>]! */
        else if (inst.operands.size() == 2 && inst.isWriteBack() == true) {
          triton::arch::Register& base = dst.getMemory().getBaseRegister();

          /* Create the semantics of the base register */
          auto node3 = dst.getMemory().getLeaAst();

          /* Create symbolic expression */
          auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, base, "STR operation - Base register computation");

          /* Spread taint */
          expr3->isTainted = this->taintEngine->isTainted(base);
        }

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::strb_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& src = inst.operands[0];
        triton::arch::OperandWrapper& dst = inst.operands[1];

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node1 = this->astCtxt.extract(7, 0, op);

        /* Special behavior: Define that the size of the memory access is 8 bits */
        dst.getMemory().setPair(std::make_pair(7, 0));

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "STRB operation - STORE access");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Optional behavior. Post computation of the base register */
        /* STRB <Wt>, [<Xn|SP>], #<simm> */
        if (inst.operands.size() == 3) {
          triton::arch::Immediate& imm = inst.operands[2].getImmediate();
          triton::arch::Register& base = dst.getMemory().getBaseRegister();

          /* Create symbolic operands of the post computation */
          auto baseNode = this->symbolicEngine->getOperandAst(inst, base);
          auto immNode  = this->symbolicEngine->getOperandAst(inst, imm);

          /* Create the semantics of the base register */
          auto node2 = this->astCtxt.bvadd(baseNode, this->astCtxt.sx(base.getBitSize() - imm.getBitSize(), immNode));

          /* Create symbolic expression */
          auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, base, "STRB operation - Base register computation");

          /* Spread taint */
          expr2->isTainted = this->taintEngine->isTainted(base);
        }

        /* STRB <Wt>, [<Xn|SP>, #<simm>]! */
        else if (inst.operands.size() == 2 && inst.isWriteBack() == true) {
          triton::arch::Register& base = dst.getMemory().getBaseRegister();

          /* Create the semantics of the base register */
          auto node3 = dst.getMemory().getLeaAst();

          /* Create symbolic expression */
          auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, base, "STRB operation - Base register computation");

          /* Spread taint */
          expr3->isTainted = this->taintEngine->isTainted(base);
        }

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::strh_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& src = inst.operands[0];
        triton::arch::OperandWrapper& dst = inst.operands[1];

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node1 = this->astCtxt.extract(15, 0, op);

        /* Special behavior: Define that the size of the memory access is 16 bits */
        dst.getMemory().setPair(std::make_pair(15, 0));

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "STRH operation - STORE access");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Optional behavior. Post computation of the base register */
        /* STRH <Wt>, [<Xn|SP>], #<simm> */
        if (inst.operands.size() == 3) {
          triton::arch::Immediate& imm = inst.operands[2].getImmediate();
          triton::arch::Register& base = dst.getMemory().getBaseRegister();

          /* Create symbolic operands of the post computation */
          auto baseNode = this->symbolicEngine->getOperandAst(inst, base);
          auto immNode  = this->symbolicEngine->getOperandAst(inst, imm);

          /* Create the semantics of the base register */
          auto node2 = this->astCtxt.bvadd(baseNode, this->astCtxt.sx(base.getBitSize() - imm.getBitSize(), immNode));

          /* Create symbolic expression */
          auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, base, "STRH operation - Base register computation");

          /* Spread taint */
          expr2->isTainted = this->taintEngine->isTainted(base);
        }

        /* STRH <Wt>, [<Xn|SP>, #<simm>]! */
        else if (inst.operands.size() == 2 && inst.isWriteBack() == true) {
          triton::arch::Register& base = dst.getMemory().getBaseRegister();

          /* Create the semantics of the base register */
          auto node3 = dst.getMemory().getLeaAst();

          /* Create symbolic expression */
          auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, base, "STRH operation - Base register computation");

          /* Spread taint */
          expr3->isTainted = this->taintEngine->isTainted(base);
        }

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::stur_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& src = inst.operands[0];
        triton::arch::OperandWrapper& dst = inst.operands[1];

        /* Create the semantics of the STORE */
        auto node = this->symbolicEngine->getOperandAst(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "STUR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::sturb_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& src = inst.operands[0];
        triton::arch::OperandWrapper& dst = inst.operands[1];

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node = this->astCtxt.extract(7, 0, op);

        /* Special behavior: Define that the size of the memory access is 8 bits */
        dst.getMemory().setPair(std::make_pair(7, 0));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "STURB operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::sturh_s(triton::arch::Instruction& inst) {
        triton::arch::OperandWrapper& src = inst.operands[0];
        triton::arch::OperandWrapper& dst = inst.operands[1];

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node = this->astCtxt.extract(15, 0, op);

        /* Special behavior: Define that the size of the memory access is 16 bits */
        dst.getMemory().setPair(std::make_pair(15, 0));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "STURH operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::sub_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.bvsub(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SUB(S) operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update symbolic flags */
        if (inst.isUpdateFlag() == true) {
          this->cfSub_s(inst, expr, dst, op1, op2);
          this->nf_s(inst, expr, dst);
          this->vfSub_s(inst, expr, dst, op1, op2);
          this->zf_s(inst, expr, dst);
        }

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::sxtb_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node = this->astCtxt.sx(dst.getBitSize() - 8, this->astCtxt.extract(7, 0, op));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SXTB operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::sxth_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node = this->astCtxt.sx(dst.getBitSize() - 16, this->astCtxt.extract(15, 0, op));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SXTH operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::sxtw_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node = this->astCtxt.sx(dst.getBitSize() - 32, this->astCtxt.extract(31, 0, op));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SXTW operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::tbnz_s(triton::arch::Instruction& inst) {
        auto  dst  = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_PC));
        auto& src1 = inst.operands[0];
        auto& src2 = inst.operands[1];
        auto& src3 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);
        auto op3 = this->symbolicEngine->getOperandAst(inst, src3);

        /* Create the semantics */
        auto node = this->astCtxt.ite(
                      this->astCtxt.equal(
                        this->astCtxt.extract(0, 0, this->astCtxt.bvlshr(op1, op2)),
                        this->astCtxt.bvtrue()
                      ),
                      op3,
                      this->astCtxt.bv(inst.getNextAddress(), dst.getBitSize())
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "TBNZ operation - Program Counter");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));
      }


      void AArch64Semantics::tbz_s(triton::arch::Instruction& inst) {
        auto  dst  = triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_PC));
        auto& src1 = inst.operands[0];
        auto& src2 = inst.operands[1];
        auto& src3 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);
        auto op3 = this->symbolicEngine->getOperandAst(inst, src3);

        /* Create the semantics */
        auto node = this->astCtxt.ite(
                      this->astCtxt.equal(
                        this->astCtxt.extract(0, 0, this->astCtxt.bvlshr(op1, op2)),
                        this->astCtxt.bvfalse()
                      ),
                      op3,
                      this->astCtxt.bv(inst.getNextAddress(), dst.getBitSize())
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "TBZ operation - Program Counter");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));
      }


      void AArch64Semantics::tst_s(triton::arch::Instruction& inst) {
        auto& src1 = inst.operands[0];
        auto& src2 = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.bvand(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicVolatileExpression(inst, node, "TST operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2);

        /* Update symbolic flags */
        if (inst.isUpdateFlag() == true) {
          this->clearFlag_s(inst, this->architecture->getRegister(ID_REG_AARCH64_C), "Clears carry flag");
          this->nf_s(inst, expr, src1);
          this->clearFlag_s(inst, this->architecture->getRegister(ID_REG_AARCH64_V), "Clears overflow flag");
          this->zf_s(inst, expr, src1);
        }

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ubfiz_s(triton::arch::Instruction& inst) {
        auto& dst   = inst.operands[0];
        auto& src1  = inst.operands[1];
        auto& src2  = inst.operands[2];
        auto& src3  = inst.operands[3];
        auto  lsb   = src2.getImmediate().getValue();
        auto  width = src3.getImmediate().getValue();

        if (lsb + width > dst.getBitSize())
          throw triton::exceptions::Semantics("AArch64Semantics::ubfiz_s(): Invalid lsb and width.");

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src1);

        /* Create the semantics */
        std::list<triton::ast::SharedAbstractNode> bits;

        if (lsb + width < dst.getBitSize()) {
          bits.push_back(this->astCtxt.bv(0, dst.getBitSize() - (lsb + width)));
        }

        bits.push_back(this->astCtxt.extract(width, 0, op));

        if (lsb) {
          bits.push_back(this->astCtxt.bv(0, lsb));
        }

        auto node = this->astCtxt.concat(bits);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "UBFIZ operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src1);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::ubfx_s(triton::arch::Instruction& inst) {
        auto& dst   = inst.operands[0];
        auto& src1  = inst.operands[1];
        auto& src2  = inst.operands[2];
        auto& src3  = inst.operands[3];
        auto  lsb   = src2.getImmediate().getValue();
        auto  width = src3.getImmediate().getValue();

        if (lsb + width > dst.getBitSize())
          throw triton::exceptions::Semantics("AArch64Semantics::ubfx_s(): Invalid lsb and width.");

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src1);

        /* Create the semantics */
        auto node = this->astCtxt.zx(dst.getBitSize() - width, this->astCtxt.extract(lsb+width-1, lsb, op));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "UBFX operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src1);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::udiv_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.ite(
                      this->astCtxt.equal(op2, this->astCtxt.bv(0, op2->getBitvectorSize())),
                      this->astCtxt.bv(0, dst.getBitSize()),
                      this->astCtxt.bvudiv(op1, op2)
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "UDIV operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::umaddl_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];
        auto& src3 = inst.operands[3];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);
        auto op3 = this->symbolicEngine->getOperandAst(inst, src3);

        /* Create the semantics */
        auto node = this->astCtxt.bvadd(
                      op3,
                      this->astCtxt.bvmul(
                        this->astCtxt.zx(DWORD_SIZE_BIT, op1),
                        this->astCtxt.zx(DWORD_SIZE_BIT, op2)
                      )
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "UMADDL operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2) | this->taintEngine->isTainted(src3));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::umnegl_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.bvneg(
                      this->astCtxt.bvmul(
                        this->astCtxt.zx(DWORD_SIZE_BIT, op1),
                        this->astCtxt.zx(DWORD_SIZE_BIT, op2)
                      )
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "UMNEGL operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::umsubl_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];
        auto& src3 = inst.operands[3];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);
        auto op3 = this->symbolicEngine->getOperandAst(inst, src3);

        /* Create the semantics */
        auto node = this->astCtxt.bvsub(
                      op3,
                      this->astCtxt.bvmul(
                        this->astCtxt.zx(DWORD_SIZE_BIT, op1),
                        this->astCtxt.zx(DWORD_SIZE_BIT, op2)
                      )
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "UMSUBL operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2) | this->taintEngine->isTainted(src3));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::umulh_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.extract(
                      DQWORD_SIZE_BIT-1,
                      QWORD_SIZE_BIT,
                      this->astCtxt.bvmul(
                        this->astCtxt.zx(QWORD_SIZE_BIT, op1),
                        this->astCtxt.zx(QWORD_SIZE_BIT, op2)
                      )
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "UMULH operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::umull_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->getOperandAst(inst, src1);
        auto op2 = this->symbolicEngine->getOperandAst(inst, src2);

        /* Create the semantics */
        auto node = this->astCtxt.bvmul(
                      this->astCtxt.zx(DWORD_SIZE_BIT, op1),
                      this->astCtxt.zx(DWORD_SIZE_BIT, op2)
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "UMULL operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::uxtb_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node = this->astCtxt.zx(dst.getBitSize() - 8, this->astCtxt.extract(7, 0, op));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "UXTB operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::uxth_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op = this->symbolicEngine->getOperandAst(inst, src);

        /* Create the semantics */
        auto node = this->astCtxt.zx(dst.getBitSize() - 16, this->astCtxt.extract(15, 0, op));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "UXTH operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Update the symbolic control flow */
        this->controlFlow_s(inst);
      }

    }; /* aarch64 namespace */
  }; /* arch namespace */
}; /* triton namespace */
