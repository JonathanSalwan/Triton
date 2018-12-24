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
AND (immediate)               | Bitwise AND (immediate).
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
CMN (extended register)       | Compare Negative (extended register): an alias of ADDS (extended register)
CMN (immediate)               | Compare Negative (immediate): an alias of ADDS (immediate)
CMN (shifted register)        | Compare Negative (shifted register): an alias of ADDS (shifted register)
CMP (extended register)       | Compare (extended register): an alias of SUBS (extended register)
CMP (immediate)               | Compare (immediate): an alias of SUBS (immediate)
CMP (shifted register)        | Compare (shifted register): an alias of SUBS (shifted register)
CSEL                          | Conditional Select
CSINC                         | Conditional Select Increment
CSNEG                         | Conditional Select Negation
EON (shifted register)        | Bitwise Exclusive OR NOT (shifted register)
EOR (immediate)               | Bitwise Exclusive OR (immediate)
EOR (shifted register)        | Bitwise Exclusive OR (shifted register)
EXTR                          | EXTR: Extract register
LDR (immediate)               | Load Register (immediate)
LDR (literal)                 | Load Register (literal)
LDR (register)                | Load Register (register)
LDUR                          | Load Register (unscaled)
LDURB                         | Load Register Byte (unscaled)
LDURH                         | Load Register Halfword (unscaled)
LDURSB                        | Load Register Signed Byte (unscaled)
LDURSH                        | Load Register Signed Halfword (unscaled)
LDURSW                        | Load Register Signed Word (unscaled)
LSL (immediate)               | Logical Shift Left (immediate): an alias of UBFM
LSL (register)                | Logical Shift Left (register): an alias of LSLV
LSR (immediate)               | Logical Shift Right (immediate): an alias of UBFM
LSR (register)                | Logical Shift Right (register): an alias of LSRV
MADD                          | Multiply-Add
MOV (bitmask immediate)       | Move (bitmask immediate): an alias of ORR (immediate)
MOV (register)                | Move (register): an alias of ORR (shifted register)
MOV (to/from SP)              | Move between register and stack pointer: an alias of ADD (immediate)
MOVZ                          | Move shifted 16-bit immediate to register
MSUB                          | Multiply-Subtract
MUL                           | Multiply: an alias of MADD
MVN                           | Bitwise NOT: an alias of ORN (shifted register)
NEG (shifted register)        | Negate (shifted register): an alias of SUB (shifted register)
NOP                           | No Operation
ORN                           | Bitwise OR NOT (shifted register)
ORR (immediate)               | Bitwise OR (immediate)
ORR (shifted register)        | Bitwise OR (shifted register)
RET                           | Return from subroutine
STR (immediate)               | Store Register (immediate)
STR (register)                | Store Register (register)
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
          case ID_INS_CMN:       this->cmn_s(inst);           break;
          case ID_INS_CMP:       this->cmp_s(inst);           break;
          case ID_INS_CSEL:      this->csel_s(inst);          break;
          case ID_INS_CSINC:     this->csinc_s(inst);         break;
          case ID_INS_CSNEG:     this->csneg_s(inst);         break;
          case ID_INS_EON:       this->eon_s(inst);           break;
          case ID_INS_EOR:       this->eor_s(inst);           break;
          case ID_INS_EXTR:      this->extr_s(inst);          break;
          case ID_INS_LDR:       this->ldr_s(inst);           break;
          case ID_INS_LDUR:      this->ldur_s(inst);          break;
          case ID_INS_LDURB:     this->ldurb_s(inst);         break;
          case ID_INS_LDURH:     this->ldurh_s(inst);         break;
          case ID_INS_LDURSB:    this->ldursb_s(inst);        break;
          case ID_INS_LDURSH:    this->ldursh_s(inst);        break;
          case ID_INS_LDURSW:    this->ldursw_s(inst);        break;
          case ID_INS_LSL:       this->lsl_s(inst);           break;
          case ID_INS_LSR:       this->lsr_s(inst);           break;
          case ID_INS_MADD:      this->madd_s(inst);          break;
          case ID_INS_MOV:       this->mov_s(inst);           break;
          case ID_INS_MOVZ:      this->movz_s(inst);          break;
          case ID_INS_MSUB:      this->msub_s(inst);          break;
          case ID_INS_MUL:       this->mul_s(inst);           break;
          case ID_INS_MVN:       this->mvn_s(inst);           break;
          case ID_INS_NEG:       this->neg_s(inst);           break;
          case ID_INS_NOP:       this->nop_s(inst);           break;
          case ID_INS_ORN:       this->orn_s(inst);           break;
          case ID_INS_ORR:       this->orr_s(inst);           break;
          case ID_INS_RET:       this->ret_s(inst);           break;
          case ID_INS_STR:       this->str_s(inst);           break;
          case ID_INS_STUR:      this->stur_s(inst);          break;
          case ID_INS_STURB:     this->sturb_s(inst);         break;
          case ID_INS_STURH:     this->sturh_s(inst);         break;
          case ID_INS_SUB:       this->sub_s(inst);           break;
          case ID_INS_SXTB:      this->sxtb_s(inst);          break;
          case ID_INS_SXTH:      this->sxth_s(inst);          break;
          case ID_INS_SXTW:      this->sxtw_s(inst);          break;
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

          // Signed <=. Z set, N and V differ.
          case triton::arch::aarch64::ID_CONDITION_LE: {
            auto z = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_Z)));
            auto n = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_N)));
            auto v = this->symbolicEngine->getOperandAst(inst, triton::arch::OperandWrapper(this->architecture->getRegister(ID_REG_AARCH64_V)));
            auto node = this->astCtxt.ite(
                        this->astCtxt.land(
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
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, flag, comment);

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaintRegister(flag, triton::engines::taint::UNTAINTED);
      }


      void AArch64Semantics::setFlag_s(triton::arch::Instruction& inst, const triton::arch::Register& flag, std::string comment) {
        /* Create the semantics */
        auto node = this->astCtxt.bv(1, 1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, flag, comment);

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
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, nf, "Negative flag");

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
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, zf, "Zero flag");

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
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, cf, "Carry flag");

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
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, cf, "Carry flag");

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
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, vf, "Overflow flag");

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
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, vf, "Overflow flag");

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

        /* Upate the symbolic control flow */
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

        /* Upate symbolic flags */
        if (inst.isUpdateFlag() == true) {
          this->cfAdd_s(inst, expr, dst, op1, op2);
          this->nf_s(inst, expr, dst);
          this->vfAdd_s(inst, expr, dst, op1, op2);
          this->zf_s(inst, expr, dst);
        }

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate symbolic flags */
        if (inst.isUpdateFlag() == true) {
          this->clearFlag_s(inst, this->architecture->getRegister(ID_REG_AARCH64_C), "Clears carry flag");
          this->nf_s(inst, expr, dst);
          this->clearFlag_s(inst, this->architecture->getRegister(ID_REG_AARCH64_V), "Clears overflow flag");
          this->zf_s(inst, expr, dst);
        }

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate symbolic flags */
        this->cfAdd_s(inst, expr, src1, op1, op2);
        this->nf_s(inst, expr, src1);
        this->vfAdd_s(inst, expr, src1, op1, op2);
        this->zf_s(inst, expr, src1);

        /* Upate the symbolic control flow */
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

        /* Upate symbolic flags */
        this->cfSub_s(inst, expr, src1, op1, op2);
        this->nf_s(inst, expr, src1);
        this->vfSub_s(inst, expr, src1, op1, op2);
        this->zf_s(inst, expr, src1);

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void AArch64Semantics::nop_s(triton::arch::Instruction& inst) {
        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate symbolic flags */
        if (inst.isUpdateFlag() == true) {
          this->cfSub_s(inst, expr, dst, op1, op2);
          this->nf_s(inst, expr, dst);
          this->vfSub_s(inst, expr, dst, op1, op2);
          this->zf_s(inst, expr, dst);
        }

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
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

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }

    }; /* aarch64 namespace */
  }; /* arch namespace */
}; /* triton namespace */
