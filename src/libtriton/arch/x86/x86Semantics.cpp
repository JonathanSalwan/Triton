//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <api.hpp>
#include <cpuSize.hpp>
#include <x86Semantics.hpp>
#include <x86Specifications.hpp>



/*! \page SMT_Semantics_Supported_page SMT Semantics Supported
    \brief [**internal**] All information about the supported semantics.

\tableofcontents

\section SMT_Semantics_Supported_description Description
<hr>

Here is the instructions' list of what **Triton** can converts into the \ref py_smt2lib_page representation.
These semantics are based on the [Medusa's semantics](https://github.com/wisk/medusa/blob/dev/arch/x86.yaml).
Please note that our main objective is not to support all semantics right now, we are currently focusing on
the design of **Triton**'s engines. When engines will be reliable, we will write the last semantics :-).
However, feel free to add your own semantics into the [appropriate file](x86Semantics_8cpp_source.html).

\subsection SMT_Semantics_Supported_x86 x86 and x86-64 SMT semantics supported


Mnemonic                     | Description
-----------------------------|----------------------------------------------------
ADD                          | Add
ADC                          | Add with Carry
AND                          | Logical AND
ANDNPD                       | Bitwise Logical AND NOT of Packed Double-Precision Floating-Point Values
ANDNPS                       | Bitwise Logical AND NOT of Packed Single-Precision Floating-Point Values
ANDPD                        | Bitwise Logical AND of Packed Double-Precision Floating-Point Values
ANDPS                        | Bitwise Logical AND of Packed Single-Precision Floating-Point Values
BSWAP                        | Byte Swap
CALL                         | Call Procedure
CBW                          | Convert byte (al) to word (ax).
CDQE                         | Convert dword (eax) to qword (rax).
CLC                          | Clear Carry Flag
CLD                          | Clear Direction Flag
CMC                          | Complement Carry Flag
CMOVA                        | Move if not below
CMOVAE                       | Move if not below or equal
CMOVB                        | Move if below
CMOVBE                       | Move if below or equal
CMOVE                        | Move if zero
CMOVG                        | Move if not less
CMOVGE                       | Move if not less or equal
CMOVL                        | Move if less
CMOVLE                       | Move if less or equal
CMOVNE                       | Move if not zero
CMOVNO                       | Move if not overflow
CMOVNP                       | Move if not parity
CMOVNS                       | Move if not sign
CMOVO                        | Move if overflow
CMOVP                        | Move if parity
CMOVS                        | Move if sign
CMP                          | Compare Two Operands
CMPXCHG                      | Compare and Exchange
CQO                          | convert qword (rax) to oword (rdx:rax)
CWDE                         | Convert word (ax) to dword (eax).
DEC                          | Decrement by 1
DIV                          | Unsigned Divide
IDIV                         | Signed Divide
IMUL                         | Signed Multiply
INC                          | Increment by 1
JA                           | Jump if not below (Jump if above)
JAE                          | Jump if not below or equal (Jump if above or equal)
JB                           | Jump if below
JBE                          | Jump if below or equal
JE                           | Jump if zero (Jump if equal)
JG                           | Jump if not less or equal (Jump if greater)
JGE                          | Jump if not less (Jump if not less)
JL                           | Jump if less
JLE                          | Jump if less or equal
JMP                          | Jump
JNO                          | Jump if not overflow
JNP                          | Jump if not parity
JNS                          | Jump if not sign
JNZ                          | Jump if not zero
JO                           | Jump if overflow
JP                           | Jump if parity
JS                           | Jump if sign
LEA                          | Load Effective Address
LEAVE                        | High Level Procedure Exit
MOV                          | Move
MOVAPD                       | Move Aligned Packed Double-Precision Floating-Point Values
MOVAPS                       | Move Aligned Packed Single-Precision Floating-Point Values
MOVDQA                       | Move Aligned Double Quadword
MOVDQU                       | Move Unaligned Double Quadword
MOVHLPS                      | Move Packed Single-Precision Floating-Point Values High to Low
MOVHPD                       | Move High Packed Double-Precision Floating-Point Values
MOVHPS                       | Move High Packed Single-Precision Floating-Point Values
MOVLHPS                      | Move Packed Single-Precision Floating-Point Values Low to High
MOVLPD                       | Move Low Packed Double-Precision Floating-Point Values
MOVLPS                       | Move Low Packed Single-Precision Floating-Point Values
MOVSX                        | Move with Sign-Extension
MOVZX                        | Move with Zero-Extend
MUL                          | Unsigned Multiply
NEG                          | Two's Complement Negation
NOP                          | No Operation
NOT                          | One's Complement Negation
OR                           | Logical Inclusive OR
ORPD                         | Bitwise Logical OR of Double-Precision Floating-Point Values
ORPS                         | Bitwise Logical OR of Single-Precision Floating-Point Values
PCMPEQB                      | Compare Packed Data for Equal (bytes)
PCMPEQD                      | Compare Packed Data for Equal (dwords)
PCMPEQW                      | Compare Packed Data for Equal (words)
PMOVMSKB                     | Move Byte Mask
POP                          | Pop a Value from the Stack
PUSH                         | Push a Value onto the Stack
PXOR                         | Logical Exclusive OR
RCL                          | Rotate Left with Carry
RCR                          | Rotate Right with Carry
RET                          | Return from Procedure
ROL                          | Rotate Left
ROR                          | Rotate Right
SAL                          | Shift Left
SAR                          | Shift Right Signed
SBB                          | Integer Subtraction with Borrow
SETA                         | Set byte if above
SETAE                        | Set byte if above or equal
SETB                         | Set byte if below
SETBE                        | Set byte if below or equal
SETE                         | Set byte if zero
SETG                         | Set byte if greater
SETGE                        | Set byte if greater or equal
SETL                         | Set byte if less
SETLE                        | Set byte if less or equal
SETNE                        | Set byte if not zero
SETNO                        | Set byte if not overflow
SETNP                        | Set byte if not parity
SETNS                        | Set byte if not sign
SETO                         | Set byte if overflow
SETP                         | Set byte if parity
SETS                         | Set byte if sign
SHL                          | Shift Left
SHR                          | Shift Right Unsigned
STC                          | Set Carry Flag
STD                          | Set Direction Flag
SUB                          | Subtract
TEST                         | Logical Compare
XADD                         | Exchange and Add
XCHG                         | Exchange Register/Memory with Register
XOR                          | Logical Exclusive OR
XORPD                        | Bitwise Logical XOR for Double-Precision Floating-Point Values
XORPS                        | Bitwise Logical XOR for Single-Precision Floating-Point Values

*/



namespace triton {
  namespace arch {
    namespace x86 {
      namespace semantics {


        void build(triton::arch::Instruction& inst) {
          switch (inst.getType()) {
            case ID_INS_ADC:            triton::arch::x86::semantics::adc_s(inst);        break;
            case ID_INS_ADD:            triton::arch::x86::semantics::add_s(inst);        break;
            case ID_INS_AND:            triton::arch::x86::semantics::and_s(inst);        break;
            case ID_INS_ANDNPD:         triton::arch::x86::semantics::andnpd_s(inst);     break;
            case ID_INS_ANDNPS:         triton::arch::x86::semantics::andnps_s(inst);     break;
            case ID_INS_ANDPD:          triton::arch::x86::semantics::andpd_s(inst);      break;
            case ID_INS_ANDPS:          triton::arch::x86::semantics::andps_s(inst);      break;
            case ID_INS_BSWAP:          triton::arch::x86::semantics::bswap_s(inst);      break;
            case ID_INS_CALL:           triton::arch::x86::semantics::call_s(inst);       break;
            case ID_INS_CBW:            triton::arch::x86::semantics::cbw_s(inst);        break;
            case ID_INS_CDQE:           triton::arch::x86::semantics::cdqe_s(inst);       break;
            case ID_INS_CLC:            triton::arch::x86::semantics::clc_s(inst);        break;
            case ID_INS_CLD:            triton::arch::x86::semantics::cld_s(inst);        break;
            case ID_INS_CMC:            triton::arch::x86::semantics::cmc_s(inst);        break;
            case ID_INS_CMOVA:          triton::arch::x86::semantics::cmova_s(inst);      break;
            case ID_INS_CMOVAE:         triton::arch::x86::semantics::cmovae_s(inst);     break;
            case ID_INS_CMOVB:          triton::arch::x86::semantics::cmovb_s(inst);      break;
            case ID_INS_CMOVBE:         triton::arch::x86::semantics::cmovbe_s(inst);     break;
            case ID_INS_CMOVE:          triton::arch::x86::semantics::cmove_s(inst);      break;
            case ID_INS_CMOVG:          triton::arch::x86::semantics::cmovg_s(inst);      break;
            case ID_INS_CMOVGE:         triton::arch::x86::semantics::cmovge_s(inst);     break;
            case ID_INS_CMOVL:          triton::arch::x86::semantics::cmovl_s(inst);      break;
            case ID_INS_CMOVLE:         triton::arch::x86::semantics::cmovle_s(inst);     break;
            case ID_INS_CMOVNE:         triton::arch::x86::semantics::cmovne_s(inst);     break;
            case ID_INS_CMOVNO:         triton::arch::x86::semantics::cmovno_s(inst);     break;
            case ID_INS_CMOVNP:         triton::arch::x86::semantics::cmovnp_s(inst);     break;
            case ID_INS_CMOVNS:         triton::arch::x86::semantics::cmovns_s(inst);     break;
            case ID_INS_CMOVO:          triton::arch::x86::semantics::cmovo_s(inst);      break;
            case ID_INS_CMOVP:          triton::arch::x86::semantics::cmovp_s(inst);      break;
            case ID_INS_CMOVS:          triton::arch::x86::semantics::cmovs_s(inst);      break;
            case ID_INS_CMP:            triton::arch::x86::semantics::cmp_s(inst);        break;
            case ID_INS_CMPXCHG:        triton::arch::x86::semantics::cmpxchg_s(inst);    break;
            case ID_INS_CQO:            triton::arch::x86::semantics::cqo_s(inst);        break;
            case ID_INS_CWDE:           triton::arch::x86::semantics::cwde_s(inst);       break;
            case ID_INS_DEC:            triton::arch::x86::semantics::dec_s(inst);        break;
            case ID_INS_DIV:            triton::arch::x86::semantics::div_s(inst);        break;
            case ID_INS_IDIV:           triton::arch::x86::semantics::idiv_s(inst);       break;
            case ID_INS_IMUL:           triton::arch::x86::semantics::imul_s(inst);       break;
            case ID_INS_INC:            triton::arch::x86::semantics::inc_s(inst);        break;
            case ID_INS_JA:             triton::arch::x86::semantics::ja_s(inst);         break;
            case ID_INS_JAE:            triton::arch::x86::semantics::jae_s(inst);        break;
            case ID_INS_JB:             triton::arch::x86::semantics::jb_s(inst);         break;
            case ID_INS_JBE:            triton::arch::x86::semantics::jbe_s(inst);        break;
            case ID_INS_JE:             triton::arch::x86::semantics::je_s(inst);         break;
            case ID_INS_JG:             triton::arch::x86::semantics::jg_s(inst);         break;
            case ID_INS_JGE:            triton::arch::x86::semantics::jge_s(inst);        break;
            case ID_INS_JL:             triton::arch::x86::semantics::jl_s(inst);         break;
            case ID_INS_JLE:            triton::arch::x86::semantics::jle_s(inst);        break;
            case ID_INS_JMP:            triton::arch::x86::semantics::jmp_s(inst);        break;
            case ID_INS_JNE:            triton::arch::x86::semantics::jne_s(inst);        break;
            case ID_INS_JNO:            triton::arch::x86::semantics::jno_s(inst);        break;
            case ID_INS_JNP:            triton::arch::x86::semantics::jnp_s(inst);        break;
            case ID_INS_JNS:            triton::arch::x86::semantics::jns_s(inst);        break;
            case ID_INS_JO:             triton::arch::x86::semantics::jo_s(inst);         break;
            case ID_INS_JP:             triton::arch::x86::semantics::jp_s(inst);         break;
            case ID_INS_JS:             triton::arch::x86::semantics::js_s(inst);         break;
            case ID_INS_LEA:            triton::arch::x86::semantics::lea_s(inst);        break;
            case ID_INS_LEAVE:          triton::arch::x86::semantics::leave_s(inst);      break;
            case ID_INS_MOV:            triton::arch::x86::semantics::mov_s(inst);        break;
            case ID_INS_MOVABS:         triton::arch::x86::semantics::movabs_s(inst);     break;
            case ID_INS_MOVAPD:         triton::arch::x86::semantics::movapd_s(inst);     break;
            case ID_INS_MOVAPS:         triton::arch::x86::semantics::movaps_s(inst);     break;
            case ID_INS_MOVDQA:         triton::arch::x86::semantics::movdqa_s(inst);     break;
            case ID_INS_MOVDQU:         triton::arch::x86::semantics::movdqu_s(inst);     break;
            case ID_INS_MOVHLPS:        triton::arch::x86::semantics::movhlps_s(inst);    break;
            case ID_INS_MOVHPD:         triton::arch::x86::semantics::movhpd_s(inst);     break;
            case ID_INS_MOVHPS:         triton::arch::x86::semantics::movhps_s(inst);     break;
            case ID_INS_MOVLHPS:        triton::arch::x86::semantics::movlhps_s(inst);    break;
            case ID_INS_MOVLPD:         triton::arch::x86::semantics::movlpd_s(inst);     break;
            case ID_INS_MOVLPS:         triton::arch::x86::semantics::movlps_s(inst);     break;
            case ID_INS_MOVSX:          triton::arch::x86::semantics::movsx_s(inst);      break;
            case ID_INS_MOVSXD:         triton::arch::x86::semantics::movsxd_s(inst);     break;
            case ID_INS_MOVZX:          triton::arch::x86::semantics::movzx_s(inst);      break;
            case ID_INS_MUL:            triton::arch::x86::semantics::mul_s(inst);        break;
            case ID_INS_NEG:            triton::arch::x86::semantics::neg_s(inst);        break;
            case ID_INS_NOP:            triton::arch::x86::semantics::nop_s(inst);        break;
            case ID_INS_NOT:            triton::arch::x86::semantics::not_s(inst);        break;
            case ID_INS_OR:             triton::arch::x86::semantics::or_s(inst);         break;
            case ID_INS_ORPD:           triton::arch::x86::semantics::orpd_s(inst);       break;
            case ID_INS_ORPS:           triton::arch::x86::semantics::orps_s(inst);       break;
            case ID_INS_PCMPEQB:        triton::arch::x86::semantics::pcmpeqb_s(inst);    break;
            case ID_INS_PCMPEQD:        triton::arch::x86::semantics::pcmpeqd_s(inst);    break;
            case ID_INS_PCMPEQW:        triton::arch::x86::semantics::pcmpeqw_s(inst);    break;
            case ID_INS_PMOVMSKB:       triton::arch::x86::semantics::pmovmskb_s(inst);   break;
            case ID_INS_POP:            triton::arch::x86::semantics::pop_s(inst);        break;
            case ID_INS_PUSH:           triton::arch::x86::semantics::push_s(inst);       break;
            case ID_INS_PXOR:           triton::arch::x86::semantics::pxor_s(inst);       break;
            case ID_INS_RCL:            triton::arch::x86::semantics::rcl_s(inst);        break;
            case ID_INS_RCR:            triton::arch::x86::semantics::rcr_s(inst);        break;
            case ID_INS_RET:            triton::arch::x86::semantics::ret_s(inst);        break;
            case ID_INS_ROL:            triton::arch::x86::semantics::rol_s(inst);        break;
            case ID_INS_ROR:            triton::arch::x86::semantics::ror_s(inst);        break;
            case ID_INS_SAL:            triton::arch::x86::semantics::shl_s(inst);        break;
            case ID_INS_SAR:            triton::arch::x86::semantics::sar_s(inst);        break;
            case ID_INS_SBB:            triton::arch::x86::semantics::sbb_s(inst);        break;
            case ID_INS_SETA:           triton::arch::x86::semantics::seta_s(inst);       break;
            case ID_INS_SETAE:          triton::arch::x86::semantics::setae_s(inst);      break;
            case ID_INS_SETB:           triton::arch::x86::semantics::setb_s(inst);       break;
            case ID_INS_SETBE:          triton::arch::x86::semantics::setbe_s(inst);      break;
            case ID_INS_SETE:           triton::arch::x86::semantics::sete_s(inst);       break;
            case ID_INS_SETG:           triton::arch::x86::semantics::setg_s(inst);       break;
            case ID_INS_SETGE:          triton::arch::x86::semantics::setge_s(inst);      break;
            case ID_INS_SETL:           triton::arch::x86::semantics::setl_s(inst);       break;
            case ID_INS_SETLE:          triton::arch::x86::semantics::setle_s(inst);      break;
            case ID_INS_SETNE:          triton::arch::x86::semantics::setne_s(inst);      break;
            case ID_INS_SETNO:          triton::arch::x86::semantics::setno_s(inst);      break;
            case ID_INS_SETNP:          triton::arch::x86::semantics::setnp_s(inst);      break;
            case ID_INS_SETNS:          triton::arch::x86::semantics::setns_s(inst);      break;
            case ID_INS_SETO:           triton::arch::x86::semantics::seto_s(inst);       break;
            case ID_INS_SETP:           triton::arch::x86::semantics::setp_s(inst);       break;
            case ID_INS_SETS:           triton::arch::x86::semantics::sets_s(inst);       break;
            case ID_INS_SHL:            triton::arch::x86::semantics::shl_s(inst);        break;
            case ID_INS_SHR:            triton::arch::x86::semantics::shr_s(inst);        break;
            case ID_INS_STC:            triton::arch::x86::semantics::stc_s(inst);        break;
            case ID_INS_STD:            triton::arch::x86::semantics::std_s(inst);        break;
            case ID_INS_SUB:            triton::arch::x86::semantics::sub_s(inst);        break;
            case ID_INS_TEST:           triton::arch::x86::semantics::test_s(inst);       break;
            case ID_INS_XADD:           triton::arch::x86::semantics::xadd_s(inst);       break;
            case ID_INS_XCHG:           triton::arch::x86::semantics::xchg_s(inst);       break;
            case ID_INS_XOR:            triton::arch::x86::semantics::xor_s(inst);        break;
            case ID_INS_XORPD:          triton::arch::x86::semantics::xorpd_s(inst);      break;
            case ID_INS_XORPS:          triton::arch::x86::semantics::xorps_s(inst);      break;
          }
        }


        void alignAddStack_s(triton::arch::Instruction& inst, triton::uint32 delta) {
          auto dst = triton::arch::OperandWrapper(TRITON_X86_REG_SP.getParent());

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = smt2lib::bv(delta, dst.getBitSize());

          /* Create the SMT semantics */
          auto node = smt2lib::bvadd(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "Stack alignment");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, dst);
        }


        void alignSubStack_s(triton::arch::Instruction& inst, triton::uint32 delta) {
          auto dst = triton::arch::OperandWrapper(TRITON_X86_REG_SP.getParent());

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = smt2lib::bv(delta, dst.getBitSize());

          /* Create the SMT semantics */
          auto node = smt2lib::bvsub(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "Stack alignment");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, dst);
        }


        void clearFlag_s(triton::arch::Instruction& inst, triton::arch::RegisterOperand& flag, std::string comment) {
          /* Create the SMT semantics */
          auto node = smt2lib::bv(0, 1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, flag, comment);

          /* Spread taint */
          expr->isTainted = triton::api.setTaintReg(flag, triton::engines::taint::UNTAINTED);
        }


        void setFlag_s(triton::arch::Instruction& inst, triton::arch::RegisterOperand& flag, std::string comment) {
          /* Create the SMT semantics */
          auto node = smt2lib::bv(1, 1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, flag, comment);

          /* Spread taint */
          expr->isTainted = triton::api.setTaintReg(flag, triton::engines::taint::UNTAINTED);
        }


        void controlFlow_s(triton::arch::Instruction& inst) {
          /* Create the SMT semantics */
          auto node = smt2lib::bv(inst.getAddress() + inst.getOpcodesSize(), triton::api.cpuRegBitSize());

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicRegisterExpression(inst, node, TRITON_X86_REG_PC, "Program Counter");

          /* Spread taint */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_PC, triton::engines::taint::UNTAINTED);
        }


        void af_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, smt2lib::smtAstAbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();

          /*
           * Create the SMT semantic.
           * af = 0x10 == (0x10 & (regDst ^ op1 ^ op2))
           */
          auto node = smt2lib::ite(
                        smt2lib::equal(
                          smt2lib::bv(0x10, bvSize),
                          smt2lib::bvand(
                            smt2lib::bv(0x10, bvSize),
                            smt2lib::bvxor(
                              smt2lib::extract(high, low, smt2lib::reference(parent->getId())),
                              smt2lib::bvxor(op1, op2)
                            )
                          )
                        ),
                        smt2lib::bv(1, 1),
                        smt2lib::bv(0, 1)
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_AF, "Adjust flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_AF, parent->isTainted);
        }


        void afNeg_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();

          /*
           * Create the SMT semantic.
           * af = 0x10 == (0x10 & (op1 ^ regDst))
           */
          auto node = smt2lib::ite(
                        smt2lib::equal(
                          smt2lib::bv(0x10, bvSize),
                          smt2lib::bvand(
                            smt2lib::bv(0x10, bvSize),
                            smt2lib::bvxor(
                              op1,
                              smt2lib::extract(high, low, smt2lib::reference(parent->getId()))
                            )
                          )
                        ),
                        smt2lib::bv(1, 1),
                        smt2lib::bv(0, 1)
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_AF, "Adjust flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_AF, parent->isTainted);
        }


        void cfAdd_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, smt2lib::smtAstAbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();

          /*
           * Create the SMT semantic.
           * cf = extract(bvSize, bvSize, ((op0 & op1) ^ ((op0 ^ op1 ^ parent) & (op0 ^ op1))));
           */
          auto node = smt2lib::extract(high, high,
                        smt2lib::bvxor(
                          smt2lib::bvand(op1, op2),
                          smt2lib::bvand(
                            smt2lib::bvxor(
                              smt2lib::bvxor(op1, op2),
                              smt2lib::extract(high, low, smt2lib::reference(parent->getId()))
                            ),
                          smt2lib::bvxor(op1, op2))
                        )
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_CF, parent->isTainted);
        }


        void cfImul_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, smt2lib::smtAstAbstractNode* res, bool vol) {
          /*
           * Create the SMT semantic.
           * cf = 0 if sx(dst) == node else 1
           */
          auto node = smt2lib::ite(
                        smt2lib::equal(
                          smt2lib::sx(dst.getBitSize(), op1),
                          res
                        ),
                        smt2lib::bv(0, 1),
                        smt2lib::bv(1, 1)
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_CF, parent->isTainted);
        }


        void cfMul_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, bool vol) {
          auto bvSize = dst.getBitSize();

          /*
           * Create the SMT semantic.
           * cf = 0 if op1 == 0 else 1
           */
          auto node = smt2lib::ite(
                        smt2lib::equal(
                          op1,
                          smt2lib::bv(0, bvSize)
                        ),
                        smt2lib::bv(0, 1),
                        smt2lib::bv(1, 1)
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_CF, parent->isTainted);
        }


        void cfNeg_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, bool vol) {
          auto bvSize = dst.getBitSize();

          /*
           * Create the SMT semantic.
           * cf = 0 if op1 == 0 else 1
           */
          auto node = smt2lib::ite(
                        smt2lib::equal(
                          op1,
                          smt2lib::bv(0, bvSize)
                        ),
                        smt2lib::bv(0, 1),
                        smt2lib::bv(1, 1)
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_CF, parent->isTainted);
        }


        void cfRcl_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();
          auto cf     = triton::arch::OperandWrapper(RegisterOperand(TRITON_X86_REG_CF));

          /*
           * Create the SMT semantic.
           * cf = high(res & 1) if op2 != 0 else undefined
           * As the second operand can't be symbolized, there is
           * no symbolic expression available. So, we must use the
           * op2's concretization.
           */
          smt2lib::smtAstAbstractNode* node;
          if (op2->getKind() != smt2lib::DECIMAL_NODE)
            throw std::runtime_error("triton::arch::x86::semantics::cfRcl_s() - op2 must be a smtAstDecimalNode node");

          if (reinterpret_cast<smt2lib::smtAstDecimalNode*>(op2)->getValue() != 0)
            node = smt2lib::extract(high, high, smt2lib::reference(parent->getId()));
          else
            node = triton::api.buildSymbolicOperand(cf);

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_CF, parent->isTainted);
        }


        void cfRol_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op2, bool vol) {
          auto low = vol ? 0 : dst.getAbstractLow();
          auto cf  = triton::arch::OperandWrapper(RegisterOperand(TRITON_X86_REG_CF));

          /*
           * Create the SMT semantic.
           * cf = (res & 1) if op2 != 0 else undefined
           * As the second operand can't be symbolized, there is
           * no symbolic expression available. So, we must use the
           * op2's concretization.
           */
          smt2lib::smtAstAbstractNode* node;
          if (op2->getKind() != smt2lib::DECIMAL_NODE)
            throw std::runtime_error("triton::arch::x86::semantics::cfRol_s() - op2 must be a smtAstDecimalNode node");

          if (reinterpret_cast<smt2lib::smtAstDecimalNode*>(op2)->getValue() != 0)
            node = smt2lib::extract(low, low, smt2lib::reference(parent->getId()));
          else
            node = triton::api.buildSymbolicOperand(cf);

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_CF, parent->isTainted);
        }


        void cfRor_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();
          auto cf     = triton::arch::OperandWrapper(RegisterOperand(TRITON_X86_REG_CF));

          /*
           * Create the SMT semantic.
           * cf = (res >> bvSize - 1) & 1 if op2 != 0 else undefined
           * As the second operand can't be symbolized, there is
           * no symbolic expression available. So, we must use the
           * op2's concretization.
           */
          if (op2->getKind() != smt2lib::DECIMAL_NODE)
            throw std::runtime_error("triton::arch::x86::semantics::cfRor_s() - op2 must be a smtAstDecimalNode node");

          smt2lib::smtAstAbstractNode* node;
          if (reinterpret_cast<smt2lib::smtAstDecimalNode*>(op2)->getValue() != 0) {
            node = smt2lib::extract(0, 0,
              smt2lib::bvlshr(
                smt2lib::extract(high, low, smt2lib::reference(parent->getId())),
                smt2lib::bvsub(
                  smt2lib::bv(bvSize, bvSize),
                  smt2lib::bv(1, bvSize)
                )
              )
            );
          }
          else {
            node = triton::api.buildSymbolicOperand(cf);
          }

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_CF, parent->isTainted);
        }


        void cfSar_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, smt2lib::smtAstAbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto cf     = triton::arch::OperandWrapper(RegisterOperand(TRITON_X86_REG_CF));

          /*
           * Create the SMT semantic.
           * if op2 != 0:
           *   if op2 > bvSize:
           *     cf.id = ((op1 >> (bvSize - 1)) & 1)
           *   else:
           *     cf.id = ((op1 >> (op2 - 1)) & 1)
           */
          auto node = smt2lib::ite(
                        smt2lib::equal(op2, smt2lib::bv(0, bvSize)),
                        triton::api.buildSymbolicOperand(cf),
                        smt2lib::ite(
                          smt2lib::bvugt(op2, smt2lib::bv(bvSize, bvSize)),
                          smt2lib::extract(0, 0, smt2lib::bvlshr(op1, smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), smt2lib::bv(1, bvSize)))),
                          smt2lib::extract(0, 0, smt2lib::bvlshr(op1, smt2lib::bvsub(op2, smt2lib::bv(1, bvSize))))
                        )
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_CF, parent->isTainted);
        }


        void cfShl_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, smt2lib::smtAstAbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto cf     = triton::arch::OperandWrapper(RegisterOperand(TRITON_X86_REG_CF));

          /*
           * Create the SMT semantic.
           * cf = (op1 >> (bvSize - op2) & 1) if op2 != 0
           */
          auto node = smt2lib::ite(
                        smt2lib::equal(op2, smt2lib::bv(0, bvSize)),
                        triton::api.buildSymbolicOperand(cf),
                        smt2lib::extract(0, 0, smt2lib::bvlshr(op1, smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), op2)))
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_CF, parent->isTainted);
        }


        void cfShr_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, smt2lib::smtAstAbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto cf     = triton::arch::OperandWrapper(RegisterOperand(TRITON_X86_REG_CF));

          /*
           * Create the SMT semantic.
           * cf = ((op1 >> (bvSize - 1)) & 1) if op2 != 0
           */
          auto node = smt2lib::ite(
                        smt2lib::equal(op2, smt2lib::bv(0, bvSize)),
                        triton::api.buildSymbolicOperand(cf),
                        smt2lib::extract(0, 0, smt2lib::bvlshr(op1, smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), smt2lib::bv(1, bvSize))))
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_CF, parent->isTainted);
        }


        void cfSub_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, smt2lib::smtAstAbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();

          /*
           * Create the SMT semantic.
           * cf = extract(bvSize, bvSize (((op1 ^ op2 ^ res) ^ ((op1 ^ res) & (op1 ^ op2)))))
           */
          auto node = smt2lib::extract(high, high,
                        smt2lib::bvxor(
                          smt2lib::bvxor(op1, smt2lib::bvxor(op2, smt2lib::extract(high, low, smt2lib::reference(parent->getId())))),
                          smt2lib::bvand(
                            smt2lib::bvxor(op1, smt2lib::extract(high, low, smt2lib::reference(parent->getId()))),
                            smt2lib::bvxor(op1, op2)
                          )
                        )
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_CF, parent->isTainted);
        }


        void ofAdd_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, smt2lib::smtAstAbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();

          /*
           * Create the SMT semantic.
           * of = high:bool((op1 ^ ~op2) & (op1 ^ regDst))
           */
          auto node = smt2lib::extract(high, high,
                        smt2lib::bvand(
                          smt2lib::bvxor(op1, smt2lib::bvnot(op2)),
                          smt2lib::bvxor(op1, smt2lib::extract(high, low, smt2lib::reference(parent->getId())))
                        )
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_OF, parent->isTainted);
        }


        void ofImul_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, smt2lib::smtAstAbstractNode* res, bool vol) {
          /*
           * Create the SMT semantic.
           * of = 0 if sx(dst) == node else 1
           */
          auto node = smt2lib::ite(
                        smt2lib::equal(
                          smt2lib::sx(dst.getBitSize(), op1),
                          res
                        ),
                        smt2lib::bv(0, 1),
                        smt2lib::bv(1, 1)
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_OF, parent->isTainted);
        }


        void ofMul_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, bool vol) {
          auto bvSize = dst.getBitSize();

          /*
           * Create the SMT semantic.
           * of = 0 if up == 0 else 1
           */
          auto node = smt2lib::ite(
                        smt2lib::equal(
                          op1,
                          smt2lib::bv(0, bvSize)
                        ),
                        smt2lib::bv(0, 1),
                        smt2lib::bv(1, 1)
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_OF, parent->isTainted);
        }


        void ofNeg_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();

          /*
           * Create the SMT semantic.
           * of = (res & op1) >> (bvSize - 1) & 1
           */
          auto node = smt2lib::extract(0, 0,
                        smt2lib::bvshl(
                          smt2lib::bvand(smt2lib::extract(high, low, smt2lib::reference(parent->getId())), op1),
                          smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), smt2lib::bv(1, bvSize))
                        )
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_OF, parent->isTainted);
        }


        void ofRol_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();
          auto cf     = triton::arch::OperandWrapper(RegisterOperand(TRITON_X86_REG_CF));
          auto of     = triton::arch::OperandWrapper(RegisterOperand(TRITON_X86_REG_OF));

          /*
           * Create the SMT semantic.
           * of = ((cf ^ (res >> (bvsize - 1))) & 1) if op2 == 1 else undefined
           * As the second operand can't be symbolized, there is
           * no symbolic expression available. So, we must use the
           * op2's concretization.
           */
          if (op2->getKind() != smt2lib::DECIMAL_NODE)
            throw std::runtime_error("triton::arch::x86::semantics::ofRol_s() - op2 must be a smtAstDecimalNode node");

          smt2lib::smtAstAbstractNode* node;
          if (reinterpret_cast<smt2lib::smtAstDecimalNode*>(op2)->getValue() == 1) {
            node = smt2lib::extract(0, 0,
                      smt2lib::bvxor(
                        smt2lib::zx(bvSize-1, triton::api.buildSymbolicOperand(cf)),
                        smt2lib::bvshl(
                          smt2lib::extract(high, low, smt2lib::reference(parent->getId())),
                          smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), smt2lib::bv(1, bvSize))
                        )
                      )
                    );
          }
          else {
            node = triton::api.buildSymbolicOperand(of);
          }

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_OF, parent->isTainted);
        }


        void ofRor_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();
          auto of     = triton::arch::OperandWrapper(RegisterOperand(TRITON_X86_REG_OF));

          /*
           * Create the SMT semantic.
           * of = (((res >> (bvSize - 1)) ^ (res >> (bvSize - 2))) & 1) if op2 == 1 else undefined
           * As the second operand can't be symbolized, there is
           * no symbolic expression available. So, we must use the
           * op2's concretization.
           */
          if (op2->getKind() != smt2lib::DECIMAL_NODE)
            throw std::runtime_error("triton::arch::x86::semantics::ofRor_s() - op2 must be a smtAstDecimalNode node");

          smt2lib::smtAstAbstractNode* node;
          if (reinterpret_cast<smt2lib::smtAstDecimalNode *>(op2)->getValue() == 1) {
            node = smt2lib::extract(0, 0,
                     smt2lib::bvxor(
                       smt2lib::bvshl(
                         smt2lib::extract(high, low, smt2lib::reference(parent->getId())),
                         smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), smt2lib::bv(1, bvSize))
                       ),
                       smt2lib::bvshl(
                         smt2lib::extract(high, low, smt2lib::reference(parent->getId())),
                         smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), smt2lib::bv(2, bvSize))
                       )
                     )
                   );
          }
          else {
            node = triton::api.buildSymbolicOperand(of);
          }

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_OF, parent->isTainted);
        }


        void ofSar_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto of     = triton::arch::OperandWrapper(RegisterOperand(TRITON_X86_REG_OF));

          /*
           * Create the SMT semantic.
           * of = 0 if op2 == 1
           */
          auto node = smt2lib::ite(
                        smt2lib::equal(op2, smt2lib::bv(1, bvSize)),
                        smt2lib::bv(0, 1),
                        triton::api.buildSymbolicOperand(of)
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_OF, parent->isTainted);
        }


        void ofShl_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, smt2lib::smtAstAbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto of     = triton::arch::OperandWrapper(RegisterOperand(TRITON_X86_REG_OF));

          /*
           * Create the SMT semantic.
           * of = bit_cast((op1 >> (bvSize - 1)) ^ (op1 >> (bvSize - 2)), int1(1)); if op2 == 1
           */
          auto node = smt2lib::ite(
                        smt2lib::equal(op2, smt2lib::bv(1, bvSize)),
                        smt2lib::extract(0, 0,
                          smt2lib::bvxor(
                            smt2lib::bvlshr(op1, smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), smt2lib::bv(1, bvSize))),
                            smt2lib::bvlshr(op1, smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), smt2lib::bv(2, bvSize)))
                          )
                        ),
                        triton::api.buildSymbolicOperand(of)
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_OF, parent->isTainted);
        }


        void ofShr_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, smt2lib::smtAstAbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();
          auto of     = triton::arch::OperandWrapper(RegisterOperand(TRITON_X86_REG_OF));

          /*
           * Create the SMT semantic.
           * of = (op1 >> (bvSize - 1) & 1) if op2 == 1
           */
          auto node = smt2lib::ite(
                        smt2lib::equal(op2, smt2lib::bv(1, bvSize)),
                        smt2lib::extract(high, high, op1),
                        triton::api.buildSymbolicOperand(of)
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_OF, parent->isTainted);
        }


        void ofSub_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op1, smt2lib::smtAstAbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();

          /*
           * Create the SMT semantic.
           * of = high:bool((op1 ^ op2) & (op1 ^ regDst))
           */
          auto node = smt2lib::extract(high, high,
                        smt2lib::bvand(
                          smt2lib::bvxor(op1, op2),
                          smt2lib::bvxor(op1, smt2lib::extract(high, low, smt2lib::reference(parent->getId())))
                        )
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_OF, parent->isTainted);
        }


        void pf_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, bool vol) {
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? BYTE_SIZE_BIT-1 : !low ? BYTE_SIZE_BIT-1 : WORD_SIZE_BIT-1;

          /*
           * Create the SMT semantics.
           *
           * pf is set to one if there is an even number of bit set to 1 in the least
           * significant byte of the result.
           */
          auto node = smt2lib::bv(1, 1);
          for (triton::uint32 counter = 0; counter <= BYTE_SIZE_BIT-1; counter++) {
            node = smt2lib::bvxor(
                     node,
                     smt2lib::extract(0, 0,
                       smt2lib::bvlshr(
                         smt2lib::extract(high, low, smt2lib::reference(parent->getId())),
                         smt2lib::bv(counter, BYTE_SIZE_BIT)
                       )
                    )
                  );
          }

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_PF, "Parity flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_PF, parent->isTainted);
        }


        void pfShl_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? BYTE_SIZE_BIT-1 : !low ? BYTE_SIZE_BIT-1 : WORD_SIZE_BIT-1;
          auto pf     = triton::arch::OperandWrapper(RegisterOperand(TRITON_X86_REG_PF));

          /*
           * Create the SMT semantics.
           * pf if op2 != 0
           */
          auto node1 = smt2lib::bv(1, 1);
          for (triton::uint32 counter = 0; counter <= BYTE_SIZE_BIT-1; counter++) {
            node1 = smt2lib::bvxor(
                     node1,
                     smt2lib::extract(0, 0,
                       smt2lib::bvlshr(
                         smt2lib::extract(high, low, smt2lib::reference(parent->getId())),
                         smt2lib::bv(counter, BYTE_SIZE_BIT)
                       )
                    )
                  );
          }

          auto node2 = smt2lib::ite(
                         smt2lib::equal(op2, smt2lib::bv(0, bvSize)),
                         triton::api.buildSymbolicOperand(pf),
                         node1
                       );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node2, TRITON_X86_REG_PF, "Parity flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_PF, parent->isTainted);
        }


        void sf_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, bool vol) {
          auto bvSize = dst.getBitSize();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();

          /*
           * Create the SMT semantic.
           * sf = high:bool(regDst)
           */
          auto node = smt2lib::extract(high, high, smt2lib::reference(parent->getId()));

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_SF, "Sign flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_SF, parent->isTainted);
        }


        void sfShl_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();
          auto sf     = triton::arch::OperandWrapper(RegisterOperand(TRITON_X86_REG_SF));

          /*
           * Create the SMT semantic.
           * sf if op2 != 0
           */
          auto node = smt2lib::ite(
                        smt2lib::equal(op2, smt2lib::bv(0, bvSize)),
                        triton::api.buildSymbolicOperand(sf),
                        smt2lib::extract(high, high, smt2lib::reference(parent->getId()))
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_SF, "Sign flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_SF, parent->isTainted);
        }


        void zf_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();

          /*
           * Create the SMT semantic.
           * zf = 0 == regDst
           */
          auto node = smt2lib::ite(
                        smt2lib::equal(
                          smt2lib::extract(high, low, smt2lib::reference(parent->getId())),
                          smt2lib::bv(0, bvSize)
                        ),
                        smt2lib::bv(1, 1),
                        smt2lib::bv(0, 1)
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_ZF, "Zero flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_ZF, parent->isTainted);
        }


        void zfShl_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, smt2lib::smtAstAbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();
          auto zf     = triton::arch::OperandWrapper(RegisterOperand(TRITON_X86_REG_ZF));

          /*
           * Create the SMT semantic.
           * zf if op2 != 0
           */
          auto node = smt2lib::ite(
                        smt2lib::equal(op2, smt2lib::bv(0, bvSize)),
                        triton::api.buildSymbolicOperand(zf),
                        smt2lib::ite(
                          smt2lib::equal(
                            smt2lib::extract(high, low, smt2lib::reference(parent->getId())),
                            smt2lib::bv(0, bvSize)
                          ),
                          smt2lib::bv(1, 1),
                          smt2lib::bv(0, 1)
                        )
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_ZF, "Zero flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintReg(TRITON_X86_REG_ZF, parent->isTainted);
        }


        void adc_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];
          auto cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);
          auto op3 = triton::api.buildSymbolicOperand(cf);

          /* Create the SMT semantics */
          auto node = smt2lib::bvadd(smt2lib::bvadd(op1, op2), smt2lib::zx(dst.getBitSize()-1, op3));

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "ADC operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);
          expr->isTainted = triton::api.taintUnion(dst, cf);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::af_s(inst, expr, dst, op1, op2);
          triton::arch::x86::semantics::cfAdd_s(inst, expr, dst, op1, op2);
          triton::arch::x86::semantics::ofAdd_s(inst, expr, dst, op1, op2);
          triton::arch::x86::semantics::pf_s(inst, expr, dst);
          triton::arch::x86::semantics::sf_s(inst, expr, dst);
          triton::arch::x86::semantics::zf_s(inst, expr, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void add_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = smt2lib::bvadd(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "ADD operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::af_s(inst, expr, dst, op1, op2);
          triton::arch::x86::semantics::cfAdd_s(inst, expr, dst, op1, op2);
          triton::arch::x86::semantics::ofAdd_s(inst, expr, dst, op1, op2);
          triton::arch::x86::semantics::pf_s(inst, expr, dst);
          triton::arch::x86::semantics::sf_s(inst, expr, dst);
          triton::arch::x86::semantics::zf_s(inst, expr, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void and_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = smt2lib::bvand(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "AND operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::clearFlag_s(inst, TRITON_X86_REG_CF, "Clears carry flag");
          triton::arch::x86::semantics::clearFlag_s(inst, TRITON_X86_REG_OF, "Clears overflow flag");
          triton::arch::x86::semantics::pf_s(inst, expr, dst);
          triton::arch::x86::semantics::sf_s(inst, expr, dst);
          triton::arch::x86::semantics::zf_s(inst, expr, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void andnpd_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = smt2lib::bvand(smt2lib::bvnot(op1), op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "ANDNPD operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void andnps_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = smt2lib::bvand(smt2lib::bvnot(op1), op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "ANDNPS operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void andpd_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = smt2lib::bvand(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "ANDPD operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void andps_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = smt2lib::bvand(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "ANDPS operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void bswap_s(triton::arch::Instruction& inst) {
          auto src = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          std::list<smt2lib::smtAstAbstractNode *> bytes;
          switch (src.getSize()) {
            case QWORD_SIZE:
              bytes.push_front(smt2lib::extract(63, 56, op1));
              bytes.push_front(smt2lib::extract(55, 48, op1));
              bytes.push_front(smt2lib::extract(47, 40, op1));
              bytes.push_front(smt2lib::extract(39, 32, op1));
            case DWORD_SIZE:
              bytes.push_front(smt2lib::extract(31, 24, op1));
              bytes.push_front(smt2lib::extract(23, 16, op1));
            case WORD_SIZE:
              bytes.push_front(smt2lib::extract(15, 8, op1));
              bytes.push_front(smt2lib::extract(7,  0, op1));
              break;
            default:
              throw std::runtime_error("Error: triton::arch::x86::semantics::bswap_s() - Invalid operand size");
          }

          auto node = smt2lib::concat(bytes);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, src, "BSWAP operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(src, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void call_s(triton::arch::Instruction& inst) {
          auto stack      = TRITON_X86_REG_SP.getParent();
          auto stackValue = triton::api.getRegisterValue(stack).convert_to<triton::__uint>();
          auto pc         = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto sp         = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue, stack.getSize()));
          auto src        = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics - side effect */
          alignSubStack_s(inst, sp.getSize());

          /* Create the SMT semantics - side effect */
          auto node1 = smt2lib::bv(inst.getNextAddress(), pc.getBitSize());

          /* Create the SMT semantics */
          auto node2 = op1;

          /* Create the symbolic expression */
          auto expr1 = triton::api.createSymbolicExpression(inst, node1, sp, "Saved Program Counter");

          /* Create symbolic expression */
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, pc, "Program Counter");

          /* Spread taint */
          expr1->isTainted = triton::api.taintAssignmentMemImm(sp.getMem());
          expr2->isTainted = triton::api.taintAssignment(pc, src);
        }


        void cbw_s(triton::arch::Instruction& inst) {
          auto dst = triton::arch::OperandWrapper(TRITON_X86_REG_AX);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);

          /* Create the SMT semantics */
          auto node = smt2lib::sx(BYTE_SIZE_BIT, smt2lib::extract(BYTE_SIZE_BIT-1, 0, op1));

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "CBW operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cdqe_s(triton::arch::Instruction& inst) {
          auto dst = triton::arch::OperandWrapper(TRITON_X86_REG_RAX);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);

          /* Create the SMT semantics */
          auto node = smt2lib::sx(DWORD_SIZE_BIT, smt2lib::extract(DWORD_SIZE_BIT-1, 0, op1));

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "CDQE operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void clc_s(triton::arch::Instruction& inst) {
          triton::arch::x86::semantics::clearFlag_s(inst, TRITON_X86_REG_CF, "Clears carry flag");
          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cld_s(triton::arch::Instruction& inst) {
          triton::arch::x86::semantics::clearFlag_s(inst, TRITON_X86_REG_DF, "Clears direction flag");
          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cmc_s(triton::arch::Instruction& inst) {
          auto dst = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);

          /* Create the SMT semantics */
          auto node = smt2lib::bvnot(op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, dst.getReg(), "CMC operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cmova_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];
          auto cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
          auto zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);
          auto op3 = triton::api.buildSymbolicOperand(cf);
          auto op4 = triton::api.buildSymbolicOperand(zf);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(smt2lib::bvand(smt2lib::bvnot(op3), smt2lib::bvnot(op4)), smt2lib::bvtrue()), op2, op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "CMOVA operation");

          /* Spread taint and condition flag */
          if ((!triton::api.getRegisterValue(TRITON_X86_REG_CF) & !triton::api.getRegisterValue(TRITON_X86_REG_ZF)) == true) {
            expr->isTainted = triton::api.taintAssignment(dst, src);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cmovae_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];
          auto cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);
          auto op3 = triton::api.buildSymbolicOperand(cf);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(op3, smt2lib::bvfalse()), op2, op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "CMOVAE operation");

          /* Spread taint and condition flag */
          if (!triton::api.getRegisterValue(TRITON_X86_REG_CF)) {
            expr->isTainted = triton::api.taintAssignment(dst, src);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cmovb_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];
          auto cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);
          auto op3 = triton::api.buildSymbolicOperand(cf);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(op3, smt2lib::bvtrue()), op2, op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "CMOVB operation");

          /* Spread taint and condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_CF)) {
            expr->isTainted = triton::api.taintAssignment(dst, src);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cmovbe_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];
          auto cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
          auto zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);
          auto op3 = triton::api.buildSymbolicOperand(cf);
          auto op4 = triton::api.buildSymbolicOperand(zf);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(smt2lib::bvor(op3, op4), smt2lib::bvtrue()), op2, op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "CMOVBE operation");

          /* Spread taint and condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_CF) | triton::api.getRegisterValue(TRITON_X86_REG_ZF)) {
            expr->isTainted = triton::api.taintAssignment(dst, src);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cmove_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];
          auto zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);
          auto op3 = triton::api.buildSymbolicOperand(zf);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(op3, smt2lib::bvtrue()), op2, op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "CMOVE operation");

          /* Spread taint and condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_ZF)) {
            expr->isTainted = triton::api.taintAssignment(dst, src);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cmovg_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];
          auto sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
          auto zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);
          auto op3 = triton::api.buildSymbolicOperand(sf);
          auto op4 = triton::api.buildSymbolicOperand(of);
          auto op5 = triton::api.buildSymbolicOperand(zf);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(smt2lib::bvor(smt2lib::bvxor(op3, op4), op5), smt2lib::bvfalse()), op2, op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "CMOVG operation");

          /* Spread taint and condition flag */
          if (((triton::api.getRegisterValue(TRITON_X86_REG_SF) ^ triton::api.getRegisterValue(TRITON_X86_REG_OF)) | triton::api.getRegisterValue(TRITON_X86_REG_ZF)) == false) {
            expr->isTainted = triton::api.taintAssignment(dst, src);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cmovge_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];
          auto sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);
          auto op3 = triton::api.buildSymbolicOperand(sf);
          auto op4 = triton::api.buildSymbolicOperand(of);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(op3, op4), op2, op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "CMOVGE operation");

          /* Spread taint and condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_SF) == triton::api.getRegisterValue(TRITON_X86_REG_OF)) {
            expr->isTainted = triton::api.taintAssignment(dst, src);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cmovl_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];
          auto sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);
          auto op3 = triton::api.buildSymbolicOperand(sf);
          auto op4 = triton::api.buildSymbolicOperand(of);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(smt2lib::bvxor(op3, op4), smt2lib::bvtrue()), op2, op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "CMOVL operation");

          /* Spread taint and condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_SF) ^ triton::api.getRegisterValue(TRITON_X86_REG_OF)) {
            expr->isTainted = triton::api.taintAssignment(dst, src);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cmovle_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];
          auto sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
          auto zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);
          auto op3 = triton::api.buildSymbolicOperand(sf);
          auto op4 = triton::api.buildSymbolicOperand(of);
          auto op5 = triton::api.buildSymbolicOperand(zf);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(smt2lib::bvor(smt2lib::bvxor(op3, op4), op5), smt2lib::bvtrue()), op2, op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "CMOVBE operation");

          /* Spread taint and condition flag */
          if (((triton::api.getRegisterValue(TRITON_X86_REG_SF) ^ triton::api.getRegisterValue(TRITON_X86_REG_OF)) | triton::api.getRegisterValue(TRITON_X86_REG_ZF)) == true) {
            expr->isTainted = triton::api.taintAssignment(dst, src);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cmovne_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];
          auto zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);
          auto op3 = triton::api.buildSymbolicOperand(zf);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(op3, smt2lib::bvfalse()), op2, op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "CMOVNE operation");

          /* Spread taint and condition flag */
          if (!triton::api.getRegisterValue(TRITON_X86_REG_ZF)) {
            expr->isTainted = triton::api.taintAssignment(dst, src);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cmovno_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];
          auto of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);
          auto op3 = triton::api.buildSymbolicOperand(of);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(op3, smt2lib::bvfalse()), op2, op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "CMOVNO operation");

          /* Spread taint and condition flag */
          if (!triton::api.getRegisterValue(TRITON_X86_REG_OF)) {
            expr->isTainted = triton::api.taintAssignment(dst, src);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cmovnp_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];
          auto pf  = triton::arch::OperandWrapper(TRITON_X86_REG_PF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);
          auto op3 = triton::api.buildSymbolicOperand(pf);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(op3, smt2lib::bvfalse()), op2, op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "CMOVNP operation");

          /* Spread taint and condition flag */
          if (!triton::api.getRegisterValue(TRITON_X86_REG_PF)) {
            expr->isTainted = triton::api.taintAssignment(dst, src);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cmovns_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];
          auto sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);
          auto op3 = triton::api.buildSymbolicOperand(sf);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(op3, smt2lib::bvfalse()), op2, op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "CMOVNS operation");

          /* Spread taint and condition flag */
          if (!triton::api.getRegisterValue(TRITON_X86_REG_SF)) {
            expr->isTainted = triton::api.taintAssignment(dst, src);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cmovo_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];
          auto of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);
          auto op3 = triton::api.buildSymbolicOperand(of);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(op3, smt2lib::bvtrue()), op2, op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "CMOVO operation");

          /* Spread taint and condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_OF)) {
            expr->isTainted = triton::api.taintAssignment(dst, src);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cmovp_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];
          auto pf  = triton::arch::OperandWrapper(TRITON_X86_REG_PF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);
          auto op3 = triton::api.buildSymbolicOperand(pf);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(op3, smt2lib::bvtrue()), op2, op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "CMOVP operation");

          /* Spread taint and condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_PF)) {
            expr->isTainted = triton::api.taintAssignment(dst, src);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cmovs_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];
          auto sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);
          auto op3 = triton::api.buildSymbolicOperand(sf);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(op3, smt2lib::bvtrue()), op2, op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "CMOVS operation");

          /* Spread taint and condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_SF)) {
            expr->isTainted = triton::api.taintAssignment(dst, src);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cmp_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = smt2lib::sx(dst.getBitSize() - src.getBitSize(), triton::api.buildSymbolicOperand(src));

          /* Create the SMT semantics */
          auto node = smt2lib::bvsub(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicVolatileExpression(inst, node, "CMP operation");

          /* Spread taint */
          expr->isTainted = triton::api.isTainted(dst) | triton::api.isTainted(src);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::af_s(inst, expr, dst, op1, op2, true);
          triton::arch::x86::semantics::cfSub_s(inst, expr, dst, op1, op2, true);
          triton::arch::x86::semantics::ofSub_s(inst, expr, dst, op1, op2, true);
          triton::arch::x86::semantics::pf_s(inst, expr, dst, true);
          triton::arch::x86::semantics::sf_s(inst, expr, dst, true);
          triton::arch::x86::semantics::zf_s(inst, expr, dst, true);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cmpxchg_s(triton::arch::Instruction& inst) {
          auto src1 = inst.operands[0];
          auto src2 = inst.operands[1];

          triton::arch::OperandWrapper accumulator(TRITON_X86_REG_AL);
          switch (src1.getSize()) {
            case WORD_SIZE:
              accumulator.setReg(TRITON_X86_REG_AX);
              break;
            case DWORD_SIZE:
              accumulator.setReg(TRITON_X86_REG_EAX);
              break;
            case QWORD_SIZE:
              accumulator.setReg(TRITON_X86_REG_RAX);
              break;
          }

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(accumulator);
          auto op2 = triton::api.buildSymbolicOperand(src1);
          auto op3 = triton::api.buildSymbolicOperand(src2);

          /* Create the SMT semantics */
          auto node1 = smt2lib::bvsub(op1, op2);
          auto node2 = smt2lib::ite(smt2lib::equal(op1, op2), op3, op2);
          auto node3 = smt2lib::ite(smt2lib::equal(op1, op2), op1, op2);

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicVolatileExpression(inst, node1, "CMP operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, src1, "XCHG operation");
          auto expr3 = triton::api.createSymbolicExpression(inst, node3, accumulator, "XCHG operation");

          /* Spread taint */
          expr1->isTainted = triton::api.isTainted(accumulator) | triton::api.isTainted(src1);
          expr2->isTainted = triton::api.taintAssignment(src1, src2);
          expr3->isTainted = triton::api.taintAssignment(accumulator, src1);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::af_s(inst, expr1, accumulator, op1, op2, true);
          triton::arch::x86::semantics::cfSub_s(inst, expr1, accumulator, op1, op2, true);
          triton::arch::x86::semantics::ofSub_s(inst, expr1, accumulator, op1, op2, true);
          triton::arch::x86::semantics::pf_s(inst, expr1, accumulator, true);
          triton::arch::x86::semantics::sf_s(inst, expr1, accumulator, true);
          triton::arch::x86::semantics::zf_s(inst, expr1, accumulator, true);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cqo_s(triton::arch::Instruction& inst) {
          auto dst = triton::arch::OperandWrapper(TRITON_X86_REG_RDX);
          auto src = triton::arch::OperandWrapper(TRITON_X86_REG_RAX);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics - TMP = 128 bitvec (RDX:RAX) */
          auto node1 = smt2lib::sx(QWORD_SIZE_BIT, op1);

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicVolatileExpression(inst, node1, "Temporary variable");

          /* Spread taint */
          expr1->isTainted = triton::api.isRegTainted(TRITON_X86_REG_RDX) | triton::api.isRegTainted(TRITON_X86_REG_RAX);

          /* Create the SMT semantics - RAX = TMP[63...0] */
          auto node2 = smt2lib::extract(QWORD_SIZE_BIT-1, 0, smt2lib::reference(expr1->getId()));

          /* Create symbolic expression */
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, src, "CQO operation - RAX");

          /* Spread taint */
          expr2->isTainted = triton::api.setTaintReg(TRITON_X86_REG_RAX, expr1->isTainted);

          /* Create the SMT semantics - RDX = TMP[127...64] */
          auto node3 = smt2lib::extract(DQWORD_SIZE_BIT-1, QWORD_SIZE_BIT, smt2lib::reference(expr1->getId()));

          /* Create symbolic expression */
          auto expr3 = triton::api.createSymbolicExpression(inst, node3, dst, "CQO operation - RDX");

          /* Spread taint */
          expr3->isTainted = triton::api.setTaintReg(TRITON_X86_REG_RDX, expr1->isTainted);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cwde_s(triton::arch::Instruction& inst) {
          auto dst = triton::arch::OperandWrapper(TRITON_X86_REG_EAX);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);

          /* Create the SMT semantics */
          auto node = smt2lib::sx(WORD_SIZE_BIT, smt2lib::extract(WORD_SIZE_BIT-1, 0, op1));

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "CWDE operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void dec_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = smt2lib::bv(1, dst.getBitSize());

          /* Create the SMT semantics */
          auto node = smt2lib::bvsub(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "DEC operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::af_s(inst, expr, dst, op1, op2);
          triton::arch::x86::semantics::ofSub_s(inst, expr, dst, op1, op2);
          triton::arch::x86::semantics::pf_s(inst, expr, dst);
          triton::arch::x86::semantics::sf_s(inst, expr, dst);
          triton::arch::x86::semantics::zf_s(inst, expr, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void div_s(triton::arch::Instruction& inst) {
          auto src = inst.operands[0];

          /* Create symbolic operands */
          auto divisor = triton::api.buildSymbolicOperand(src);

          /* Create symbolic expression */
          switch (src.getSize()) {

            case BYTE_SIZE: {
              /* AX */
              auto ax = triton::arch::OperandWrapper(TRITON_X86_REG_AX);
              auto dividend = triton::api.buildSymbolicOperand(ax);
              /* res = AX / Source */
              auto result = smt2lib::bvudiv(dividend, smt2lib::zx(BYTE_SIZE_BIT, divisor));
              /* mod = AX % Source */
              auto mod = smt2lib::bvurem(dividend, smt2lib::zx(BYTE_SIZE_BIT, divisor));
              /* AH = mod */
              /* AL = res */
              auto node = smt2lib::concat(
                            smt2lib::extract((BYTE_SIZE_BIT - 1), 0, mod),   /* AH = mod */
                            smt2lib::extract((BYTE_SIZE_BIT - 1), 0, result) /* AL = res */
                          );
              /* Create symbolic expression */
              auto expr = triton::api.createSymbolicExpression(inst, node, ax, "DIV operation");
              /* Apply the taint */
              expr->isTainted = triton::api.taintUnion(ax, src);
              break;
            }

            case WORD_SIZE: {
              /* DX:AX */
              auto dx = triton::arch::OperandWrapper(TRITON_X86_REG_DX);
              auto ax = triton::arch::OperandWrapper(TRITON_X86_REG_AX);
              auto dividend = smt2lib::concat(triton::api.buildSymbolicOperand(dx), triton::api.buildSymbolicOperand(ax));
              /* res = DX:AX / Source */
              auto result = smt2lib::extract((WORD_SIZE_BIT - 1), 0, smt2lib::bvudiv(dividend, smt2lib::zx(WORD_SIZE_BIT, divisor)));
              /* mod = DX:AX % Source */
              auto mod = smt2lib::extract((WORD_SIZE_BIT - 1), 0, smt2lib::bvurem(dividend, smt2lib::zx(WORD_SIZE_BIT, divisor)));
              /* Create the symbolic expression for AX */
              auto expr1 = triton::api.createSymbolicExpression(inst, result, ax, "DIV operation");
              /* Apply the taint for AX */
              expr1->isTainted = triton::api.taintUnion(ax, src);
              /* Create the symbolic expression for DX */
              auto expr2 = triton::api.createSymbolicExpression(inst, mod, dx, "DIV operation");
              /* Apply the taint for DX */
              expr2->isTainted = triton::api.taintUnion(dx, src);
              break;
            }

            case DWORD_SIZE: {
              /* EDX:EAX */
              auto edx = triton::arch::OperandWrapper(TRITON_X86_REG_EDX);
              auto eax = triton::arch::OperandWrapper(TRITON_X86_REG_EAX);
              auto dividend = smt2lib::concat(triton::api.buildSymbolicOperand(edx), triton::api.buildSymbolicOperand(eax));
              /* res = EDX:EAX / Source */
              auto result = smt2lib::extract((DWORD_SIZE_BIT - 1), 0, smt2lib::bvudiv(dividend, smt2lib::zx(DWORD_SIZE_BIT, divisor)));
              /* mod = EDX:EAX % Source */
              auto mod = smt2lib::extract((DWORD_SIZE_BIT - 1), 0, smt2lib::bvurem(dividend, smt2lib::zx(DWORD_SIZE_BIT, divisor)));
              /* Create the symbolic expression for EAX */
              auto expr1 = triton::api.createSymbolicExpression(inst, result, eax, "DIV operation");
              /* Apply the taint for EAX */
              expr1->isTainted = triton::api.taintUnion(eax, src);
              /* Create the symbolic expression for EDX */
              auto expr2 = triton::api.createSymbolicExpression(inst, mod, edx, "DIV operation");
              /* Apply the taint for EDX */
              expr2->isTainted = triton::api.taintUnion(edx, src);
              break;
            }

            case QWORD_SIZE: {
              /* RDX:RAX */
              auto rdx = triton::arch::OperandWrapper(TRITON_X86_REG_RDX);
              auto rax = triton::arch::OperandWrapper(TRITON_X86_REG_RAX);
              auto dividend = smt2lib::concat(triton::api.buildSymbolicOperand(rdx), triton::api.buildSymbolicOperand(rax));
              /* res = RDX:RAX / Source */
              auto result = smt2lib::extract((QWORD_SIZE_BIT - 1), 0, smt2lib::bvudiv(dividend, smt2lib::zx(QWORD_SIZE_BIT, divisor)));
              /* mod = RDX:RAX % Source */
              auto mod = smt2lib::extract((QWORD_SIZE_BIT - 1), 0, smt2lib::bvurem(dividend, smt2lib::zx(QWORD_SIZE_BIT, divisor)));
              /* Create the symbolic expression for RAX */
              auto expr1 = triton::api.createSymbolicExpression(inst, result, rax, "DIV operation");
              /* Apply the taint for EAX */
              expr1->isTainted = triton::api.taintUnion(rax, src);
              /* Create the symbolic expression for RDX */
              auto expr2 = triton::api.createSymbolicExpression(inst, mod, rdx, "DIV operation");
              /* Apply the taint for EDX */
              expr2->isTainted = triton::api.taintUnion(rdx, src);
              break;
            }

          }

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void idiv_s(triton::arch::Instruction& inst) {
          auto src = inst.operands[0];

          /* Create symbolic operands */
          auto divisor = triton::api.buildSymbolicOperand(src);

          /* Create symbolic expression */
          switch (src.getSize()) {

            case BYTE_SIZE: {
              /* AX */
              auto ax = triton::arch::OperandWrapper(TRITON_X86_REG_AX);
              auto dividend = triton::api.buildSymbolicOperand(ax);
              /* res = AX / Source */
              auto result = smt2lib::bvsdiv(dividend, smt2lib::sx(BYTE_SIZE_BIT, divisor));
              /* mod = AX % Source */
              auto mod = smt2lib::bvsrem(dividend, smt2lib::sx(BYTE_SIZE_BIT, divisor));
              /* AH = mod */
              /* AL = res */
              auto node = smt2lib::concat(
                            smt2lib::extract((BYTE_SIZE_BIT - 1), 0, mod),   /* AH = mod */
                            smt2lib::extract((BYTE_SIZE_BIT - 1), 0, result) /* AL = res */
                          );
              /* Create symbolic expression */
              auto expr = triton::api.createSymbolicExpression(inst, node, ax, "IDIV operation");
              /* Apply the taint */
              expr->isTainted = triton::api.taintUnion(ax, src);
              break;
            }

            case WORD_SIZE: {
              /* DX:AX */
              auto dx = triton::arch::OperandWrapper(TRITON_X86_REG_DX);
              auto ax = triton::arch::OperandWrapper(TRITON_X86_REG_AX);
              auto dividend = smt2lib::concat(triton::api.buildSymbolicOperand(dx), triton::api.buildSymbolicOperand(ax));
              /* res = DX:AX / Source */
              auto result = smt2lib::extract((WORD_SIZE_BIT - 1), 0, smt2lib::bvsdiv(dividend, smt2lib::sx(WORD_SIZE_BIT, divisor)));
              /* mod = DX:AX % Source */
              auto mod = smt2lib::extract((WORD_SIZE_BIT - 1), 0, smt2lib::bvsrem(dividend, smt2lib::sx(WORD_SIZE_BIT, divisor)));
              /* Create the symbolic expression for AX */
              auto expr1 = triton::api.createSymbolicExpression(inst, result, ax, "IDIV operation");
              /* Apply the taint for AX */
              expr1->isTainted = triton::api.taintUnion(ax, src);
              /* Create the symbolic expression for DX */
              auto expr2 = triton::api.createSymbolicExpression(inst, mod, dx, "IDIV operation");
              /* Apply the taint for DX */
              expr2->isTainted = triton::api.taintUnion(dx, src);
              break;
            }

            case DWORD_SIZE: {
              /* EDX:EAX */
              auto edx = triton::arch::OperandWrapper(TRITON_X86_REG_EDX);
              auto eax = triton::arch::OperandWrapper(TRITON_X86_REG_EAX);
              auto dividend = smt2lib::concat(triton::api.buildSymbolicOperand(edx), triton::api.buildSymbolicOperand(eax));
              /* res = EDX:EAX / Source */
              auto result = smt2lib::extract((DWORD_SIZE_BIT - 1), 0, smt2lib::bvsdiv(dividend, smt2lib::sx(DWORD_SIZE_BIT, divisor)));
              /* mod = EDX:EAX % Source */
              auto mod = smt2lib::extract((DWORD_SIZE_BIT - 1), 0, smt2lib::bvsrem(dividend, smt2lib::sx(DWORD_SIZE_BIT, divisor)));
              /* Create the symbolic expression for EAX */
              auto expr1 = triton::api.createSymbolicExpression(inst, result, eax, "IDIV operation");
              /* Apply the taint for EAX */
              expr1->isTainted = triton::api.taintUnion(eax, src);
              /* Create the symbolic expression for EDX */
              auto expr2 = triton::api.createSymbolicExpression(inst, mod, edx, "IDIV operation");
              /* Apply the taint for EDX */
              expr2->isTainted = triton::api.taintUnion(edx, src);
              break;
            }

            case QWORD_SIZE: {
              /* RDX:RAX */
              auto rdx = triton::arch::OperandWrapper(TRITON_X86_REG_RDX);
              auto rax = triton::arch::OperandWrapper(TRITON_X86_REG_RAX);
              auto dividend = smt2lib::concat(triton::api.buildSymbolicOperand(rdx), triton::api.buildSymbolicOperand(rax));
              /* res = RDX:RAX / Source */
              auto result = smt2lib::extract((QWORD_SIZE_BIT - 1), 0, smt2lib::bvsdiv(dividend, smt2lib::sx(QWORD_SIZE_BIT, divisor)));
              /* mod = RDX:RAX % Source */
              auto mod = smt2lib::extract((QWORD_SIZE_BIT - 1), 0, smt2lib::bvsrem(dividend, smt2lib::sx(QWORD_SIZE_BIT, divisor)));
              /* Create the symbolic expression for RAX */
              auto expr1 = triton::api.createSymbolicExpression(inst, result, rax, "IDIV operation");
              /* Apply the taint for EAX */
              expr1->isTainted = triton::api.taintUnion(rax, src);
              /* Create the symbolic expression for RDX */
              auto expr2 = triton::api.createSymbolicExpression(inst, mod, rdx, "IDIV operation");
              /* Apply the taint for EDX */
              expr2->isTainted = triton::api.taintUnion(rdx, src);
              break;
            }

          }

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void imul_s(triton::arch::Instruction& inst) {
          switch (inst.operands.size()) {

            /* one operand */
            case 1: {
              auto src = inst.operands[0];

              /* Operand's size */
              switch (src.getSize()) {

                /* dst = AX */
                case BYTE_SIZE: {
                  auto ax   = triton::arch::OperandWrapper(TRITON_X86_REG_AX);
                  auto al   = triton::arch::OperandWrapper(TRITON_X86_REG_AL);
                  auto op1  = triton::api.buildSymbolicOperand(al);
                  auto op2  = triton::api.buildSymbolicOperand(src);
                  auto node = smt2lib::bvmul(smt2lib::sx(BYTE_SIZE_BIT, op1), smt2lib::sx(BYTE_SIZE_BIT, op2));
                  auto expr = triton::api.createSymbolicExpression(inst, node, ax, "IMUL operation");
                  expr->isTainted = triton::api.taintUnion(ax, src);
                  triton::arch::x86::semantics::cfImul_s(inst, expr, al, smt2lib::bvmul(op1, op2), node);
                  triton::arch::x86::semantics::ofImul_s(inst, expr, al, smt2lib::bvmul(op1, op2), node);
                  break;
                }

                /* dst = DX:AX */
                case WORD_SIZE: {
                  auto ax    = triton::arch::OperandWrapper(TRITON_X86_REG_AX);
                  auto dx    = triton::arch::OperandWrapper(TRITON_X86_REG_DX);
                  auto op1   = triton::api.buildSymbolicOperand(ax);
                  auto op2   = triton::api.buildSymbolicOperand(src);
                  auto node  = smt2lib::bvmul(smt2lib::sx(WORD_SIZE_BIT, op1), smt2lib::sx(WORD_SIZE_BIT, op2));
                  auto expr1 = triton::api.createSymbolicExpression(inst, smt2lib::extract(WORD_SIZE_BIT-1, 0, node), ax, "IMUL operation");
                  auto expr2 = triton::api.createSymbolicExpression(inst, smt2lib::extract(DWORD_SIZE_BIT-1, WORD_SIZE_BIT, node), dx, "IMUL operation");
                  expr1->isTainted = triton::api.taintUnion(ax, src);
                  expr2->isTainted = triton::api.taintUnion(dx, src);
                  triton::arch::x86::semantics::cfImul_s(inst, expr1, ax, smt2lib::bvmul(op1, op2), node);
                  triton::arch::x86::semantics::ofImul_s(inst, expr1, ax, smt2lib::bvmul(op1, op2), node);
                  break;
                }

                /* dst = EDX:EAX */
                case DWORD_SIZE: {
                  auto eax   = triton::arch::OperandWrapper(TRITON_X86_REG_EAX);
                  auto edx   = triton::arch::OperandWrapper(TRITON_X86_REG_EDX);
                  auto op1   = triton::api.buildSymbolicOperand(eax);
                  auto op2   = triton::api.buildSymbolicOperand(src);
                  auto node  = smt2lib::bvmul(smt2lib::sx(DWORD_SIZE_BIT, op1), smt2lib::sx(DWORD_SIZE_BIT, op2));
                  auto expr1 = triton::api.createSymbolicExpression(inst, smt2lib::extract(DWORD_SIZE_BIT-1, 0, node), eax, "IMUL operation");
                  auto expr2 = triton::api.createSymbolicExpression(inst, smt2lib::extract(QWORD_SIZE_BIT-1, DWORD_SIZE_BIT, node), edx, "IMUL operation");
                  expr1->isTainted = triton::api.taintUnion(eax, src);
                  expr2->isTainted = triton::api.taintUnion(edx, src);
                  triton::arch::x86::semantics::cfImul_s(inst, expr1, eax, smt2lib::bvmul(op1, op2), node);
                  triton::arch::x86::semantics::ofImul_s(inst, expr1, eax, smt2lib::bvmul(op1, op2), node);
                  break;
                }

                /* dst = RDX:RAX */
                case QWORD_SIZE: {
                  auto rax   = triton::arch::OperandWrapper(TRITON_X86_REG_RAX);
                  auto rdx   = triton::arch::OperandWrapper(TRITON_X86_REG_RDX);
                  auto op1   = triton::api.buildSymbolicOperand(rax);
                  auto op2   = triton::api.buildSymbolicOperand(src);
                  auto node  = smt2lib::bvmul(smt2lib::sx(QWORD_SIZE_BIT, op1), smt2lib::sx(QWORD_SIZE_BIT, op2));
                  auto expr1 = triton::api.createSymbolicExpression(inst, smt2lib::extract(QWORD_SIZE_BIT-1, 0, node), rax, "IMUL operation");
                  auto expr2 = triton::api.createSymbolicExpression(inst, smt2lib::extract(DQWORD_SIZE_BIT-1, QWORD_SIZE_BIT, node), rdx, "IMUL operation");
                  expr1->isTainted = triton::api.taintUnion(rax, src);
                  expr2->isTainted = triton::api.taintUnion(rdx, src);
                  triton::arch::x86::semantics::cfImul_s(inst, expr1, rax, smt2lib::bvmul(op1, op2), node);
                  triton::arch::x86::semantics::ofImul_s(inst, expr1, rax, smt2lib::bvmul(op1, op2), node);
                  break;
                }

              }
              break;
            }

            /* two operands */
            case 2: {
              auto dst  = inst.operands[0];
              auto src  = inst.operands[1];
              auto op1  = triton::api.buildSymbolicOperand(dst);
              auto op2  = triton::api.buildSymbolicOperand(src);
              auto node = smt2lib::bvmul(smt2lib::sx(dst.getBitSize(), op1), smt2lib::sx(src.getBitSize(), op2));
              auto expr = triton::api.createSymbolicExpression(inst, smt2lib::extract(dst.getBitSize()-1, 0, node), dst, "IMUL operation");
              expr->isTainted = triton::api.taintUnion(dst, src);
              triton::arch::x86::semantics::cfImul_s(inst, expr, dst, smt2lib::bvmul(op1, op2), node);
              triton::arch::x86::semantics::ofImul_s(inst, expr, dst, smt2lib::bvmul(op1, op2), node);
              break;
            }

            /* three operands */
            case 3: {
              auto dst  = inst.operands[0];
              auto src1 = inst.operands[1];
              auto src2 = inst.operands[2];
              auto op2  = triton::api.buildSymbolicOperand(src1);
              auto op3  = triton::api.buildSymbolicOperand(src2);
              auto node = smt2lib::bvmul(smt2lib::sx(src1.getBitSize(), op2), smt2lib::sx(src2.getBitSize(), op3));
              auto expr = triton::api.createSymbolicExpression(inst, smt2lib::extract(dst.getBitSize()-1, 0, node), dst, "IMUL operation");
              expr->isTainted = triton::api.taintUnion(dst, src1);
              expr->isTainted = triton::api.taintUnion(dst, src2);
              triton::arch::x86::semantics::cfImul_s(inst, expr, dst, smt2lib::bvmul(op2, op3), node);
              triton::arch::x86::semantics::ofImul_s(inst, expr, dst, smt2lib::bvmul(op2, op3), node);
              break;
            }

          }

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void inc_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = smt2lib::bv(1, dst.getBitSize());

          /* Create the SMT semantics */
          auto node = smt2lib::bvadd(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "INC operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::af_s(inst, expr, dst, op1, op2);
          triton::arch::x86::semantics::ofAdd_s(inst, expr, dst, op1, op2);
          triton::arch::x86::semantics::pf_s(inst, expr, dst);
          triton::arch::x86::semantics::sf_s(inst, expr, dst);
          triton::arch::x86::semantics::zf_s(inst, expr, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void ja_s(triton::arch::Instruction& inst) {
          auto pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto cf      = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
          auto zf      = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
          auto srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(cf);
          auto op2 = triton::api.buildSymbolicOperand(zf);
          auto op3 = triton::api.buildSymbolicOperand(srcImm1);
          auto op4 = triton::api.buildSymbolicOperand(srcImm2);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(
                        smt2lib::equal(
                          smt2lib::bvand(
                            smt2lib::bvnot(op1),
                            smt2lib::bvnot(op2)
                          ),
                          smt2lib::bvtrue()
                        ), op4, op3);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if ((!triton::api.getRegisterValue(TRITON_X86_REG_CF) & !triton::api.getRegisterValue(TRITON_X86_REG_ZF)) == true)
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, cf);
          expr->isTainted = triton::api.taintUnion(pc, zf);
        }


        void jae_s(triton::arch::Instruction& inst) {
          auto pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto cf      = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
          auto srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(cf);
          auto op2 = triton::api.buildSymbolicOperand(srcImm1);
          auto op3 = triton::api.buildSymbolicOperand(srcImm2);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(op1, smt2lib::bvfalse()), op3, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (!triton::api.getRegisterValue(TRITON_X86_REG_CF))
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, cf);
        }


        void jb_s(triton::arch::Instruction& inst) {
          auto pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto cf      = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
          auto srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(cf);
          auto op2 = triton::api.buildSymbolicOperand(srcImm1);
          auto op3 = triton::api.buildSymbolicOperand(srcImm2);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(op1, smt2lib::bvtrue()), op3, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_CF))
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, cf);
        }


        void jbe_s(triton::arch::Instruction& inst) {
          auto pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto cf      = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
          auto zf      = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
          auto srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(cf);
          auto op2 = triton::api.buildSymbolicOperand(zf);
          auto op3 = triton::api.buildSymbolicOperand(srcImm1);
          auto op4 = triton::api.buildSymbolicOperand(srcImm2);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(smt2lib::bvor(op1, op2), smt2lib::bvtrue()), op4, op3);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_CF) | triton::api.getRegisterValue(TRITON_X86_REG_ZF))
            inst.setConditionTaken(true);


          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, cf);
          expr->isTainted = triton::api.taintUnion(pc, zf);
        }


        void je_s(triton::arch::Instruction& inst) {
          auto pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto zf      = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
          auto srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(zf);
          auto op2 = triton::api.buildSymbolicOperand(srcImm1);
          auto op3 = triton::api.buildSymbolicOperand(srcImm2);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(op1, smt2lib::bvtrue()), op3, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_ZF))
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, zf);
        }


        void jg_s(triton::arch::Instruction& inst) {
          auto pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto sf      = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto of      = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
          auto zf      = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
          auto srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(sf);
          auto op2 = triton::api.buildSymbolicOperand(of);
          auto op3 = triton::api.buildSymbolicOperand(zf);
          auto op4 = triton::api.buildSymbolicOperand(srcImm1);
          auto op5 = triton::api.buildSymbolicOperand(srcImm2);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(smt2lib::bvor(smt2lib::bvxor(op1, op2), op3), smt2lib::bvfalse()), op5, op4);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (((triton::api.getRegisterValue(TRITON_X86_REG_SF) ^ triton::api.getRegisterValue(TRITON_X86_REG_OF)) | triton::api.getRegisterValue(TRITON_X86_REG_ZF)) == false)
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, sf);
          expr->isTainted = triton::api.taintUnion(pc, of);
          expr->isTainted = triton::api.taintUnion(pc, zf);
        }


        void jge_s(triton::arch::Instruction& inst) {
          auto pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto sf      = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto of      = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
          auto srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(sf);
          auto op2 = triton::api.buildSymbolicOperand(of);
          auto op3 = triton::api.buildSymbolicOperand(srcImm1);
          auto op4 = triton::api.buildSymbolicOperand(srcImm2);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(op1, op2), op4, op3);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_SF) == triton::api.getRegisterValue(TRITON_X86_REG_OF))
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, sf);
          expr->isTainted = triton::api.taintUnion(pc, of);
        }


        void jl_s(triton::arch::Instruction& inst) {
          auto pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto sf      = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto of      = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
          auto srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(sf);
          auto op2 = triton::api.buildSymbolicOperand(of);
          auto op3 = triton::api.buildSymbolicOperand(srcImm1);
          auto op4 = triton::api.buildSymbolicOperand(srcImm2);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(smt2lib::bvxor(op1, op2), smt2lib::bvtrue()), op4, op3);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_SF) ^ triton::api.getRegisterValue(TRITON_X86_REG_OF))
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, sf);
          expr->isTainted = triton::api.taintUnion(pc, of);
        }


        void jle_s(triton::arch::Instruction& inst) {
          auto pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto sf      = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto of      = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
          auto zf      = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
          auto srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(sf);
          auto op2 = triton::api.buildSymbolicOperand(of);
          auto op3 = triton::api.buildSymbolicOperand(zf);
          auto op4 = triton::api.buildSymbolicOperand(srcImm1);
          auto op5 = triton::api.buildSymbolicOperand(srcImm2);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(smt2lib::bvor(smt2lib::bvxor(op1, op2), op3), smt2lib::bvtrue()), op5, op4);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (((triton::api.getRegisterValue(TRITON_X86_REG_SF) ^ triton::api.getRegisterValue(TRITON_X86_REG_OF)) | triton::api.getRegisterValue(TRITON_X86_REG_ZF)) == true)
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, sf);
          expr->isTainted = triton::api.taintUnion(pc, of);
          expr->isTainted = triton::api.taintUnion(pc, zf);
        }


        void jmp_s(triton::arch::Instruction& inst) {
          auto pc  = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto src = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = op1;

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, src);
        }


        void jne_s(triton::arch::Instruction& inst) {
          auto pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto zf      = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
          auto srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(zf);
          auto op2 = triton::api.buildSymbolicOperand(srcImm1);
          auto op3 = triton::api.buildSymbolicOperand(srcImm2);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(op1, smt2lib::bvfalse()), op3, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (!triton::api.getRegisterValue(TRITON_X86_REG_ZF))
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, zf);
        }


        void jno_s(triton::arch::Instruction& inst) {
          auto pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto of      = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
          auto srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(of);
          auto op2 = triton::api.buildSymbolicOperand(srcImm1);
          auto op3 = triton::api.buildSymbolicOperand(srcImm2);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(op1, smt2lib::bvfalse()), op3, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (!triton::api.getRegisterValue(TRITON_X86_REG_OF))
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, of);
        }


        void jnp_s(triton::arch::Instruction& inst) {
          auto pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto pf      = triton::arch::OperandWrapper(TRITON_X86_REG_PF);
          auto srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(pf);
          auto op2 = triton::api.buildSymbolicOperand(srcImm1);
          auto op3 = triton::api.buildSymbolicOperand(srcImm2);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(op1, smt2lib::bvfalse()), op3, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (!triton::api.getRegisterValue(TRITON_X86_REG_PF))
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, pf);
        }


        void jns_s(triton::arch::Instruction& inst) {
          auto pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto sf      = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(sf);
          auto op2 = triton::api.buildSymbolicOperand(srcImm1);
          auto op3 = triton::api.buildSymbolicOperand(srcImm2);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(op1, smt2lib::bvfalse()), op3, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (!triton::api.getRegisterValue(TRITON_X86_REG_SF))
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, sf);
        }


        void jo_s(triton::arch::Instruction& inst) {
          auto pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto of      = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
          auto srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(of);
          auto op2 = triton::api.buildSymbolicOperand(srcImm1);
          auto op3 = triton::api.buildSymbolicOperand(srcImm2);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(op1, smt2lib::bvtrue()), op3, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_OF))
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, of);
        }


        void jp_s(triton::arch::Instruction& inst) {
          auto pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto pf      = triton::arch::OperandWrapper(TRITON_X86_REG_PF);
          auto srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(pf);
          auto op2 = triton::api.buildSymbolicOperand(srcImm1);
          auto op3 = triton::api.buildSymbolicOperand(srcImm2);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(op1, smt2lib::bvtrue()), op3, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_PF))
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, pf);
        }


        void js_s(triton::arch::Instruction& inst) {
          auto pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto sf      = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(sf);
          auto op2 = triton::api.buildSymbolicOperand(srcImm1);
          auto op3 = triton::api.buildSymbolicOperand(srcImm2);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(smt2lib::equal(op1, smt2lib::bvtrue()), op3, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_SF))
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, sf);
        }


        void lea_s(triton::arch::Instruction& inst) {
          auto dst                = inst.operands[0].getReg();
          auto srcDisp            = inst.operands[1].getMem().getDisplacement();
          auto srcBase            = inst.operands[1].getMem().getBaseReg();
          auto srcIndex           = inst.operands[1].getMem().getIndexReg();
          auto srcScale           = inst.operands[1].getMem().getScale();
          triton::uint32 leaSize  = 0;

          /* Setup LEA size */
          if (srcBase.isValid())
            leaSize = srcBase.getBitSize();
          else if (srcIndex.isValid())
            leaSize = srcIndex.getBitSize();
          else
            leaSize = srcDisp.getBitSize();

          /* Create symbolic operands */

          /* Displacement */
          auto op2 = triton::api.buildSymbolicImmediateOperand(srcDisp);
          if (leaSize > srcDisp.getBitSize())
            op2 = smt2lib::zx(leaSize - srcDisp.getBitSize(), op2);

          /* Base */
          smt2lib::smtAstAbstractNode* op3;
          if (srcBase.isValid())
            op3 = triton::api.buildSymbolicRegisterOperand(srcBase);
          else
            op3 = smt2lib::bv(0, leaSize);

          /* Base with PC */
          if (srcBase.isValid() && (srcBase.getParent().getId() == TRITON_X86_REG_PC.getId()))
            op3 = smt2lib::bvadd(op3, smt2lib::bv(inst.getOpcodesSize(), leaSize));

          /* Index */
          smt2lib::smtAstAbstractNode* op4;
          if (srcIndex.isValid())
            op4 = triton::api.buildSymbolicRegisterOperand(srcIndex);
          else
            op4 = smt2lib::bv(0, leaSize);

          /* Scale */
          auto op5 = triton::api.buildSymbolicImmediateOperand(srcScale);
          if (leaSize > srcScale.getBitSize())
            op5 = smt2lib::zx(leaSize - srcScale.getBitSize(), op5);

          /* Create the SMT semantics */
          /* Effective address = Displacement + BaseReg + IndexReg * Scale */
          auto node = smt2lib::bvadd(op2, smt2lib::bvadd(op3, smt2lib::bvmul(op4, op5)));

          if (dst.getBitSize() > leaSize)
            node = smt2lib::zx(dst.getBitSize() - leaSize, node);

          if (dst.getBitSize() < leaSize)
            node = smt2lib::extract(dst.getAbstractHigh(), dst.getAbstractLow(), node);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicRegisterExpression(inst, node, dst, "LEA operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignmentRegReg(dst, srcBase);
          expr->isTainted = triton::api.taintUnionRegReg(dst, srcIndex);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void leave_s(triton::arch::Instruction& inst) {
          auto stack      = TRITON_X86_REG_SP.getParent();
          auto stackValue = triton::api.getRegisterValue(stack).convert_to<triton::__uint>();
          auto bp1        = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue, stack.getSize()));
          auto bp2        = triton::arch::OperandWrapper(TRITON_X86_REG_BP.getParent());
          auto sp         = triton::arch::OperandWrapper(stack);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(bp2);

          /* RSP = RBP */
          auto node1 = op1;

          /* Create the symbolic expression */
          auto expr1 = triton::api.createSymbolicExpression(inst, node1, sp, "Stack Pointer");

          /* Spread taint */
          expr1->isTainted = triton::api.taintAssignment(sp, bp2);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(bp1);

          /* RBP = pop() */
          auto node2 = op2;

          /* Create the symbolic expression */
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, bp2, "Stack Top Pointer");

          /* Spread taint */
          expr2->isTainted = triton::api.taintAssignment(bp2, bp1);

          /* Create the SMT semantics - side effect */
          alignAddStack_s(inst, bp1.getSize());

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void mov_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create the SMT semantics */
          auto node = triton::api.buildSymbolicOperand(src);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOV operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movabs_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create the SMT semantics */
          auto node = triton::api.buildSymbolicOperand(src);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVABS operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movapd_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create the SMT semantics */
          auto node = triton::api.buildSymbolicOperand(src);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVAPD operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movaps_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create the SMT semantics */
          auto node = triton::api.buildSymbolicOperand(src);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVAPS operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movdqa_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create the SMT semantics */
          auto node = triton::api.buildSymbolicOperand(src);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVDQA operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movdqu_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create the SMT semantics */
          auto node = triton::api.buildSymbolicOperand(src);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVDQU operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movhlps_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = smt2lib::concat(
                        smt2lib::extract((DQWORD_SIZE_BIT - 1), QWORD_SIZE_BIT, op1), /* Destination[127..64] unchanged */
                        smt2lib::extract((DQWORD_SIZE_BIT - 1), QWORD_SIZE_BIT, op2)  /* Destination[63..0] = Source[127..64]; */
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVHLPS operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movhpd_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = smt2lib::concat(
                        smt2lib::extract((QWORD_SIZE_BIT - 1), 0, op2), /* Destination[127..64] = Source */
                        smt2lib::extract((QWORD_SIZE_BIT - 1), 0, op1)  /* Destination[63..0] unchanged */
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVHPD operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movhps_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = smt2lib::concat(
                        smt2lib::extract((QWORD_SIZE_BIT - 1), 0, op2), /* Destination[127..64] = Source */
                        smt2lib::extract((QWORD_SIZE_BIT - 1), 0, op1)  /* Destination[63..0] unchanged */
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVHPS operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movlhps_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = smt2lib::concat(
                        smt2lib::extract((QWORD_SIZE_BIT - 1), 0, op2), /* Destination[127..64] = Source[63..0] */
                        smt2lib::extract((QWORD_SIZE_BIT - 1), 0, op1)  /* Destination[63..0] unchanged */
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVLHPS operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movlpd_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = smt2lib::concat(
                        smt2lib::extract((DQWORD_SIZE_BIT - 1), QWORD_SIZE_BIT, op1), /* Destination[127..64] unchanged */
                        smt2lib::extract((QWORD_SIZE_BIT - 1), 0, op2)                /* Destination[63..0] = Source */
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVLPD operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movlps_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = smt2lib::concat(
                        smt2lib::extract((DQWORD_SIZE_BIT - 1), QWORD_SIZE_BIT, op1), /* Destination[127..64] unchanged */
                        smt2lib::extract((QWORD_SIZE_BIT - 1), 0, op2)                /* Destination[63..0] = Source */
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVLPS operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movsx_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = smt2lib::sx(dst.getBitSize() - src.getBitSize(), op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVSX operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movsxd_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = smt2lib::sx(dst.getBitSize() - src.getBitSize(), op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVSXD operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movzx_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = smt2lib::zx(dst.getBitSize() - src.getBitSize(), op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVZX operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void mul_s(triton::arch::Instruction& inst) {
          auto src2 = inst.operands[0];

          switch (src2.getSize()) {

            /* AX = AL * r/m8 */
            case BYTE_SIZE: {
              auto dst  = triton::arch::OperandWrapper(TRITON_X86_REG_AX);
              auto src1 = triton::arch::OperandWrapper(TRITON_X86_REG_AL);
              /* Create symbolic operands */
              auto op1 = triton::api.buildSymbolicOperand(src1);
              auto op2 = triton::api.buildSymbolicOperand(src2);
              /* Create the SMT semantics */
              auto node = smt2lib::bvmul(smt2lib::zx(BYTE_SIZE_BIT, op1), smt2lib::zx(BYTE_SIZE_BIT, op2));
              /* Create symbolic expression */
              auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MUL operation");
              /* Apply the taint */
              expr->isTainted = triton::api.taintUnion(dst, src2);
              /* Upate symbolic flags */
              auto ah = smt2lib::extract((WORD_SIZE_BIT - 1), BYTE_SIZE_BIT, node);
              triton::arch::x86::semantics::cfMul_s(inst, expr, src2, ah);
              triton::arch::x86::semantics::ofMul_s(inst, expr, src2, ah);
              break;
            }

            /* DX:AX = AX * r/m16 */
            case WORD_SIZE: {
              auto dst1 = triton::arch::OperandWrapper(TRITON_X86_REG_AX);
              auto dst2 = triton::arch::OperandWrapper(TRITON_X86_REG_DX);
              auto src1 = triton::arch::OperandWrapper(TRITON_X86_REG_AX);
              /* Create symbolic operands */
              auto op1 = triton::api.buildSymbolicOperand(src1);
              auto op2 = triton::api.buildSymbolicOperand(src2);
              /* Create the SMT semantics */
              auto node = smt2lib::bvmul(smt2lib::zx(WORD_SIZE_BIT, op1), smt2lib::zx(WORD_SIZE_BIT, op2));
              /* Create symbolic expression for ax */
              auto ax = smt2lib::extract((WORD_SIZE_BIT - 1), 0, node);
              auto expr1 = triton::api.createSymbolicExpression(inst, ax, dst1, "MUL operation");
              /* Apply the taint */
              expr1->isTainted = triton::api.taintUnion(dst1, src2);
              /* Create symbolic expression for dx */
              auto dx = smt2lib::extract((DWORD_SIZE_BIT - 1), WORD_SIZE_BIT, node);
              auto expr2 = triton::api.createSymbolicExpression(inst, dx, dst2, "MUL operation");
              /* Apply the taint */
              expr2->isTainted = triton::api.taintUnion(dst2, src2);
              expr2->isTainted = triton::api.taintUnion(dst2, src1);
              /* Upate symbolic flags */
              triton::arch::x86::semantics::cfMul_s(inst, expr2, src2, dx);
              triton::arch::x86::semantics::ofMul_s(inst, expr2, src2, dx);
              break;
            }

            /* EDX:EAX = EAX * r/m32 */
            case DWORD_SIZE: {
              auto dst1 = triton::arch::OperandWrapper(TRITON_X86_REG_EAX);
              auto dst2 = triton::arch::OperandWrapper(TRITON_X86_REG_EDX);
              auto src1 = triton::arch::OperandWrapper(TRITON_X86_REG_EAX);
              /* Create symbolic operands */
              auto op1 = triton::api.buildSymbolicOperand(src1);
              auto op2 = triton::api.buildSymbolicOperand(src2);
              /* Create the SMT semantics */
              auto node = smt2lib::bvmul(smt2lib::zx(DWORD_SIZE_BIT, op1), smt2lib::zx(DWORD_SIZE_BIT, op2));
              /* Create symbolic expression for eax */
              auto eax = smt2lib::extract((DWORD_SIZE_BIT - 1), 0, node);
              auto expr1 = triton::api.createSymbolicExpression(inst, eax, dst1, "MUL operation");
              /* Apply the taint */
              expr1->isTainted = triton::api.taintUnion(dst1, src2);
              /* Create symbolic expression for edx */
              auto edx = smt2lib::extract((QWORD_SIZE_BIT - 1), DWORD_SIZE_BIT, node);
              auto expr2 = triton::api.createSymbolicExpression(inst, edx, dst2, "MUL operation");
              /* Apply the taint */
              expr2->isTainted = triton::api.taintUnion(dst2, src2);
              expr2->isTainted = triton::api.taintUnion(dst2, src1);
              /* Upate symbolic flags */
              triton::arch::x86::semantics::cfMul_s(inst, expr2, src2, edx);
              triton::arch::x86::semantics::ofMul_s(inst, expr2, src2, edx);
              break;
            }

            /* RDX:RAX = RAX * r/m64 */
            case QWORD_SIZE: {
              auto dst1 = triton::arch::OperandWrapper(TRITON_X86_REG_RAX);
              auto dst2 = triton::arch::OperandWrapper(TRITON_X86_REG_RDX);
              auto src1 = triton::arch::OperandWrapper(TRITON_X86_REG_RAX);
              /* Create symbolic operands */
              auto op1 = triton::api.buildSymbolicOperand(src1);
              auto op2 = triton::api.buildSymbolicOperand(src2);
              /* Create the SMT semantics */
              auto node = smt2lib::bvmul(smt2lib::zx(QWORD_SIZE_BIT, op1), smt2lib::zx(QWORD_SIZE_BIT, op2));
              /* Create symbolic expression for eax */
              auto rax = smt2lib::extract((QWORD_SIZE_BIT - 1), 0, node);
              auto expr1 = triton::api.createSymbolicExpression(inst, rax, dst1, "MUL operation");
              /* Apply the taint */
              expr1->isTainted = triton::api.taintUnion(dst1, src2);
              /* Create symbolic expression for rdx */
              auto rdx = smt2lib::extract((DQWORD_SIZE_BIT - 1), QWORD_SIZE_BIT, node);
              auto expr2 = triton::api.createSymbolicExpression(inst, rdx, dst2, "MUL operation");
              /* Apply the taint */
              expr2->isTainted = triton::api.taintUnion(dst2, src2);
              expr2->isTainted = triton::api.taintUnion(dst2, src1);
              /* Upate symbolic flags */
              triton::arch::x86::semantics::cfMul_s(inst, expr2, src2, rdx);
              triton::arch::x86::semantics::ofMul_s(inst, expr2, src2, rdx);
              break;
            }

          }

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void neg_s(triton::arch::Instruction& inst) {
          auto src = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = smt2lib::bvneg(op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, src, "NEG operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(src, src);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::afNeg_s(inst, expr, src, op1);
          triton::arch::x86::semantics::cfNeg_s(inst, expr, src, op1);
          triton::arch::x86::semantics::ofNeg_s(inst, expr, src, op1);
          triton::arch::x86::semantics::pf_s(inst, expr, src);
          triton::arch::x86::semantics::sf_s(inst, expr, src);
          triton::arch::x86::semantics::zf_s(inst, expr, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void nop_s(triton::arch::Instruction& inst) {
          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void not_s(triton::arch::Instruction& inst) {
          auto src = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = smt2lib::bvnot(op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, src, "NOT operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(src, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void or_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = smt2lib::bvor(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "OR operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::clearFlag_s(inst, TRITON_X86_REG_CF, "Clears carry flag");
          triton::arch::x86::semantics::clearFlag_s(inst, TRITON_X86_REG_OF, "Clears overflow flag");
          triton::arch::x86::semantics::pf_s(inst, expr, dst);
          triton::arch::x86::semantics::sf_s(inst, expr, dst);
          triton::arch::x86::semantics::zf_s(inst, expr, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void orpd_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = smt2lib::bvor(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "ORPD operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void orps_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = smt2lib::bvor(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "ORPS operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pcmpeqb_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          std::list<smt2lib::smtAstAbstractNode *> pck;
          for (triton::uint32 index = 0; index < dst.getSize(); index++) {
            uint32 high = (dst.getBitSize() - 1) - (index * BYTE_SIZE_BIT);
            uint32 low  = (dst.getBitSize() - BYTE_SIZE_BIT) - (index * BYTE_SIZE_BIT);
            pck.push_back(smt2lib::ite(
                            smt2lib::equal(
                              smt2lib::extract(high, low, op1),
                              smt2lib::extract(high, low, op2)),
                            smt2lib::bv(0xff, BYTE_SIZE_BIT),
                            smt2lib::bv(0x00, BYTE_SIZE_BIT))
                         );
          }

          auto node = smt2lib::concat(pck);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PCMPEQB operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pcmpeqd_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          std::list<smt2lib::smtAstAbstractNode *> pck;
          for (triton::uint32 index = 0; index < dst.getSize() / DWORD_SIZE; index++) {
            uint32 high = (dst.getBitSize() - 1) - (index * DWORD_SIZE_BIT);
            uint32 low  = (dst.getBitSize() - DWORD_SIZE_BIT) - (index * DWORD_SIZE_BIT);
            pck.push_back(smt2lib::ite(
                            smt2lib::equal(
                              smt2lib::extract(high, low, op1),
                              smt2lib::extract(high, low, op2)),
                            smt2lib::bv(0xffffffff, DWORD_SIZE_BIT),
                            smt2lib::bv(0x00000000, DWORD_SIZE_BIT))
                         );
          }

          auto node = smt2lib::concat(pck);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PCMPEQD operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pcmpeqw_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          std::list<smt2lib::smtAstAbstractNode *> pck;
          for (triton::uint32 index = 0; index < dst.getSize() / WORD_SIZE; index++) {
            uint32 high = (dst.getBitSize() - 1) - (index * WORD_SIZE_BIT);
            uint32 low  = (dst.getBitSize() - WORD_SIZE_BIT) - (index * WORD_SIZE_BIT);
            pck.push_back(smt2lib::ite(
                            smt2lib::equal(
                              smt2lib::extract(high, low, op1),
                              smt2lib::extract(high, low, op2)),
                            smt2lib::bv(0xffff, WORD_SIZE_BIT),
                            smt2lib::bv(0x0000, WORD_SIZE_BIT))
                         );
          }

          auto node = smt2lib::concat(pck);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PCMPEQW operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pmovmskb_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          std::list<smt2lib::smtAstAbstractNode *> mskb;
          switch (src.getSize()) {
            case DQWORD_SIZE:
              mskb.push_back(smt2lib::extract(127, 127, op2));
              mskb.push_back(smt2lib::extract(119, 119, op2));
              mskb.push_back(smt2lib::extract(111, 111, op2));
              mskb.push_back(smt2lib::extract(103, 103, op2));
              mskb.push_back(smt2lib::extract(95,  95,  op2));
              mskb.push_back(smt2lib::extract(87,  87,  op2));
              mskb.push_back(smt2lib::extract(79,  79,  op2));
              mskb.push_back(smt2lib::extract(71,  71,  op2));

            case QWORD_SIZE:
              mskb.push_back(smt2lib::extract(63,  63,  op2));
              mskb.push_back(smt2lib::extract(55,  55,  op2));
              mskb.push_back(smt2lib::extract(47,  47,  op2));
              mskb.push_back(smt2lib::extract(39,  39,  op2));
              mskb.push_back(smt2lib::extract(31,  31,  op2));
              mskb.push_back(smt2lib::extract(23,  23,  op2));
              mskb.push_back(smt2lib::extract(15,  15,  op2));
              mskb.push_back(smt2lib::extract(7,   7,   op2));
          }

          auto node = smt2lib::zx(dst.getBitSize() - mskb.size(), smt2lib::concat(mskb));

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PMOVMSKB operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pop_s(triton::arch::Instruction& inst) {
          auto stack      = TRITON_X86_REG_SP.getParent();
          auto stackValue = triton::api.getRegisterValue(stack).convert_to<triton::__uint>();
          auto dst        = inst.operands[0];
          auto src        = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue, stack.getSize()));

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = op1;

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "POP operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Create the SMT semantics - side effect */
          alignAddStack_s(inst, src.getSize());

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void push_s(triton::arch::Instruction& inst) {
          auto stack      = TRITON_X86_REG_SP.getParent();
          auto stackValue = triton::api.getRegisterValue(stack).convert_to<triton::__uint>();
          auto dst        = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue, stack.getSize()));
          auto src        = inst.operands[0];

          /* Create the SMT semantics - side effect */
          alignSubStack_s(inst, dst.getSize());

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = op1;

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PUSH operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pxor_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = smt2lib::bvxor(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PXOR operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void rcl_s(triton::arch::Instruction& inst) {
          auto dst   = inst.operands[0];
          auto src   = inst.operands[1];
          auto srcCf = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          /*
           * Note that the SMT2-LIB doesn't support expression as rotate's value.
           * The op2 must be the concretization's value.
           */
          auto op2 = smt2lib::decimal(src.getConcreteValue());
          auto op3 = triton::api.buildSymbolicOperand(srcCf);

          /* Create the SMT semantics */
          auto node1 = smt2lib::bvrol(op2, smt2lib::concat(op3, op1));

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicVolatileExpression(inst, node1, "RCL tempory operation");

          /* Spread taint */
          expr1->isTainted = triton::api.isTainted(dst) | triton::api.isTainted(src);

          /* Create the SMT semantics */
          auto node2 = smt2lib::extract(dst.getBitSize()-1, 0, node1);

          /* Create symbolic expression */
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, dst, "RCL operation");

          /* Spread taint */
          expr2->isTainted = triton::api.taintUnion(dst, src);
          expr2->isTainted = triton::api.taintUnion(dst, srcCf);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::cfRcl_s(inst, expr1, dst, op2, true);
          triton::arch::x86::semantics::ofRol_s(inst, expr1, dst, op2, true); /* Same as ROL */

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void rcr_s(triton::arch::Instruction& inst) {
          auto dst   = inst.operands[0];
          auto src   = inst.operands[1];
          auto srcCf = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          /*
           * Note that the SMT2-LIB doesn't support expression as rotate's value.
           * The op2 must be the concretization's value.
           */
          auto op2 = smt2lib::decimal(src.getConcreteValue());
          auto op3 = triton::api.buildSymbolicOperand(srcCf);

          /* Create the SMT semantics */
          auto node1 = smt2lib::bvror(op2, smt2lib::concat(op3, op1));

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicVolatileExpression(inst, node1, "RCR tempory operation");

          /* Spread taint */
          expr1->isTainted = triton::api.isTainted(dst) | triton::api.isTainted(src);

          /* Create the SMT semantics */
          auto node2 = smt2lib::extract(dst.getBitSize()-1, 0, node1);

          /* Create symbolic expression */
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, dst, "RCR operation");

          /* Spread taint */
          expr2->isTainted = triton::api.taintUnion(dst, src);
          expr2->isTainted = triton::api.taintUnion(dst, srcCf);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::cfRcl_s(inst, expr1, dst, op2, true); /* Same as RCL */
          triton::arch::x86::semantics::ofRor_s(inst, expr1, dst, op2, true); /* Same as ROR */

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void ret_s(triton::arch::Instruction& inst) {
          auto stack      = TRITON_X86_REG_SP.getParent();
          auto stackValue = triton::api.getRegisterValue(stack).convert_to<triton::__uint>();
          auto pc         = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto sp         = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue, stack.getSize()));

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(sp);

          /* Create the SMT semantics */
          auto node = op1;

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, sp);

          /* Create the SMT semantics - side effect */
          alignAddStack_s(inst, sp.getSize());

          /* Create the SMT semantics - side effect */
          if (inst.operands.size() > 0)
            alignAddStack_s(inst, inst.operands[0].getImm().getValue());
        }


        void rol_s(triton::arch::Instruction& inst) {
          auto dst   = inst.operands[0];
          auto src   = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          /*
           * Note that the SMT2-LIB doesn't support expression as rotate's value.
           * The op2 must be the concretization's value.
           */
          auto op2 = smt2lib::decimal(src.getConcreteValue());

          /* Create the SMT semantics */
          auto node = smt2lib::bvrol(op2, op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "ROL operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::cfRol_s(inst, expr, dst, op2);
          triton::arch::x86::semantics::ofRol_s(inst, expr, dst, op2);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void ror_s(triton::arch::Instruction& inst) {
          auto dst   = inst.operands[0];
          auto src   = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          /*
           * Note that the SMT2-LIB doesn't support expression as rotate's value.
           * The op2 must be the concretization's value.
           */
          auto op2 = smt2lib::decimal(src.getConcreteValue());

          /* Create the SMT semantics */
          auto node = smt2lib::bvror(op2, op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "ROR operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::cfRor_s(inst, expr, dst, op2);
          triton::arch::x86::semantics::ofRor_s(inst, expr, dst, op2);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void sar_s(triton::arch::Instruction& inst) {
          auto dst   = inst.operands[0];
          auto src   = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = smt2lib::zx(dst.getBitSize() - src.getBitSize(), triton::api.buildSymbolicOperand(src));

          /* Create the SMT semantics */
          auto node = smt2lib::bvashr(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "SAR operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::cfSar_s(inst, expr, dst, op1, op2);
          triton::arch::x86::semantics::ofSar_s(inst, expr, dst, op2);
          triton::arch::x86::semantics::pfShl_s(inst, expr, dst, op2); /* Same that shl */
          triton::arch::x86::semantics::sfShl_s(inst, expr, dst, op2); /* Same that shl */
          triton::arch::x86::semantics::zfShl_s(inst, expr, dst, op2); /* Same that shl */

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void sbb_s(triton::arch::Instruction& inst) {
          auto dst   = inst.operands[0];
          auto src   = inst.operands[1];
          auto srcCf = triton::arch::OperandWrapper(RegisterOperand(TRITON_X86_REG_CF));

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);
          auto op3 = smt2lib::zx(src.getBitSize()-1, triton::api.buildSymbolicOperand(srcCf));

          /* Create the SMT semantics */
          auto node = smt2lib::bvsub(op1, smt2lib::bvadd(op2, op3));

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "SBB operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);
          expr->isTainted = triton::api.taintUnion(dst, srcCf);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::af_s(inst, expr, dst, op1, op2);
          triton::arch::x86::semantics::cfSub_s(inst, expr, dst, op1, op2);
          triton::arch::x86::semantics::ofSub_s(inst, expr, dst, op1, op2);
          triton::arch::x86::semantics::pf_s(inst, expr, dst);
          triton::arch::x86::semantics::sf_s(inst, expr, dst);
          triton::arch::x86::semantics::zf_s(inst, expr, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void seta_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
          auto zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(cf);
          auto op3 = triton::api.buildSymbolicOperand(zf);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(
                        smt2lib::equal(
                          smt2lib::bvand(
                            smt2lib::bvnot(op2),
                            smt2lib::bvnot(op3)
                          ),
                          smt2lib::bvtrue()
                        ),
                        smt2lib::bv(1, dst.getBitSize()),
                        smt2lib::bv(0, dst.getBitSize())
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "SETA operation");

          /* Spread taint and condition flag */
          if (((!triton::api.getRegisterValue(TRITON_X86_REG_CF) & !triton::api.getRegisterValue(TRITON_X86_REG_ZF))) == true) {
            expr->isTainted = triton::api.taintUnion(dst, cf);
            expr->isTainted = triton::api.taintUnion(dst, zf);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void setae_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(cf);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(
                        smt2lib::equal(op2, smt2lib::bvfalse()),
                        smt2lib::bv(1, dst.getBitSize()),
                        smt2lib::bv(0, dst.getBitSize())
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "SETAE operation");

          /* Spread taint and condition flag */
          if (!triton::api.getRegisterValue(TRITON_X86_REG_CF)) {
            expr->isTainted = triton::api.taintUnion(dst, cf);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void setb_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(cf);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(
                        smt2lib::equal(op2, smt2lib::bvtrue()),
                        smt2lib::bv(1, dst.getBitSize()),
                        smt2lib::bv(0, dst.getBitSize())
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "SETB operation");

          /* Spread taint and condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_CF)) {
            expr->isTainted = triton::api.taintUnion(dst, cf);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void setbe_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
          auto zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(cf);
          auto op3 = triton::api.buildSymbolicOperand(zf);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(
                        smt2lib::equal(smt2lib::bvor(op2, op3), smt2lib::bvtrue()),
                        smt2lib::bv(1, dst.getBitSize()),
                        smt2lib::bv(0, dst.getBitSize())
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "SETBE operation");

          /* Spread taint and condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_CF) | triton::api.getRegisterValue(TRITON_X86_REG_ZF)) {
            expr->isTainted = triton::api.taintUnion(dst, cf);
            expr->isTainted = triton::api.taintUnion(dst, zf);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void sete_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(zf);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(
                        smt2lib::equal(op2, smt2lib::bvtrue()),
                        smt2lib::bv(1, dst.getBitSize()),
                        smt2lib::bv(0, dst.getBitSize())
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "SETE operation");

          /* Spread taint and condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_ZF)) {
            expr->isTainted = triton::api.taintUnion(dst, zf);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void setg_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
          auto zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(sf);
          auto op3 = triton::api.buildSymbolicOperand(of);
          auto op4 = triton::api.buildSymbolicOperand(zf);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(
                        smt2lib::equal(smt2lib::bvor(smt2lib::bvxor(op2, op3), op4), smt2lib::bvfalse()),
                        smt2lib::bv(1, dst.getBitSize()),
                        smt2lib::bv(0, dst.getBitSize())
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "SETG operation");

          /* Spread taint and condition flag */
          if (((triton::api.getRegisterValue(TRITON_X86_REG_SF) ^ triton::api.getRegisterValue(TRITON_X86_REG_OF)) | triton::api.getRegisterValue(TRITON_X86_REG_ZF)) == false) {
            expr->isTainted = triton::api.taintUnion(dst, sf);
            expr->isTainted = triton::api.taintUnion(dst, of);
            expr->isTainted = triton::api.taintUnion(dst, zf);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void setge_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(sf);
          auto op3 = triton::api.buildSymbolicOperand(of);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(
                        smt2lib::equal(op2, op3),
                        smt2lib::bv(1, dst.getBitSize()),
                        smt2lib::bv(0, dst.getBitSize())
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "SETGE operation");

          /* Spread taint and condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_SF) == triton::api.getRegisterValue(TRITON_X86_REG_OF)) {
            expr->isTainted = triton::api.taintUnion(dst, sf);
            expr->isTainted = triton::api.taintUnion(dst, of);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void setl_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(sf);
          auto op3 = triton::api.buildSymbolicOperand(of);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(
                        smt2lib::equal(smt2lib::bvxor(op2, op3), smt2lib::bvtrue()),
                        smt2lib::bv(1, dst.getBitSize()),
                        smt2lib::bv(0, dst.getBitSize())
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "SETL operation");

          /* Spread taint and condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_SF) ^ triton::api.getRegisterValue(TRITON_X86_REG_OF)) {
            expr->isTainted = triton::api.taintUnion(dst, sf);
            expr->isTainted = triton::api.taintUnion(dst, of);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void setle_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
          auto zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(sf);
          auto op3 = triton::api.buildSymbolicOperand(of);
          auto op4 = triton::api.buildSymbolicOperand(zf);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(
                        smt2lib::equal(smt2lib::bvor(smt2lib::bvxor(op2, op3), op4), smt2lib::bvtrue()),
                        smt2lib::bv(1, dst.getBitSize()),
                        smt2lib::bv(0, dst.getBitSize())
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "SETLE operation");

          /* Spread taint and condition flag */
          if (((triton::api.getRegisterValue(TRITON_X86_REG_SF) ^ triton::api.getRegisterValue(TRITON_X86_REG_OF)) | triton::api.getRegisterValue(TRITON_X86_REG_ZF)) == true) {
            expr->isTainted = triton::api.taintUnion(dst, sf);
            expr->isTainted = triton::api.taintUnion(dst, of);
            expr->isTainted = triton::api.taintUnion(dst, zf);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void setne_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(zf);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(
                        smt2lib::equal(op2, smt2lib::bvfalse()),
                        smt2lib::bv(1, dst.getBitSize()),
                        smt2lib::bv(0, dst.getBitSize())
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "SETNE operation");

          /* Spread taint and condition flag */
          if (!triton::api.getRegisterValue(TRITON_X86_REG_ZF)) {
            expr->isTainted = triton::api.taintUnion(dst, zf);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void setno_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(of);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(
                        smt2lib::equal(op2, smt2lib::bvfalse()),
                        smt2lib::bv(1, dst.getBitSize()),
                        smt2lib::bv(0, dst.getBitSize())
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "SETNO operation");

          /* Spread taint and condition flag */
          if (!triton::api.getRegisterValue(TRITON_X86_REG_OF)) {
            expr->isTainted = triton::api.taintUnion(dst, of);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void setnp_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto pf  = triton::arch::OperandWrapper(TRITON_X86_REG_PF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(pf);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(
                        smt2lib::equal(op2, smt2lib::bvfalse()),
                        smt2lib::bv(1, dst.getBitSize()),
                        smt2lib::bv(0, dst.getBitSize())
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "SETNP operation");

          /* Spread taint and condition flag */
          if (!triton::api.getRegisterValue(TRITON_X86_REG_PF)) {
            expr->isTainted = triton::api.taintUnion(dst, pf);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void setns_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(sf);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(
                        smt2lib::equal(op2, smt2lib::bvfalse()),
                        smt2lib::bv(1, dst.getBitSize()),
                        smt2lib::bv(0, dst.getBitSize())
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "SETNS operation");

          /* Spread taint and condition flag */
          if (!triton::api.getRegisterValue(TRITON_X86_REG_SF)) {
            expr->isTainted = triton::api.taintUnion(dst, sf);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void seto_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(of);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(
                        smt2lib::equal(op2, smt2lib::bvtrue()),
                        smt2lib::bv(1, dst.getBitSize()),
                        smt2lib::bv(0, dst.getBitSize())
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "SETO operation");

          /* Spread taint and condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_OF)) {
            expr->isTainted = triton::api.taintUnion(dst, of);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void setp_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto pf  = triton::arch::OperandWrapper(TRITON_X86_REG_PF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(pf);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(
                        smt2lib::equal(op2, smt2lib::bvtrue()),
                        smt2lib::bv(1, dst.getBitSize()),
                        smt2lib::bv(0, dst.getBitSize())
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "SETP operation");

          /* Spread taint and condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_PF)) {
            expr->isTainted = triton::api.taintUnion(dst, pf);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void sets_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(sf);

          /* Create the SMT semantics */
          auto node = smt2lib::ite(
                        smt2lib::equal(op2, smt2lib::bvtrue()),
                        smt2lib::bv(1, dst.getBitSize()),
                        smt2lib::bv(0, dst.getBitSize())
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "SETS operation");

          /* Spread taint and condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_SF)) {
            expr->isTainted = triton::api.taintUnion(dst, sf);
            inst.setConditionTaken(true);
          }
          else
            expr->isTainted = triton::api.taintUnion(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void shl_s(triton::arch::Instruction& inst) {
          auto dst   = inst.operands[0];
          auto src   = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = smt2lib::zx(dst.getBitSize() - src.getBitSize(), triton::api.buildSymbolicOperand(src));

          /* Create the SMT semantics */
          auto node = smt2lib::bvshl(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "SHL operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::cfShl_s(inst, expr, dst, op1, op2);
          triton::arch::x86::semantics::ofShl_s(inst, expr, dst, op1, op2);
          triton::arch::x86::semantics::pfShl_s(inst, expr, dst, op2);
          triton::arch::x86::semantics::sfShl_s(inst, expr, dst, op2);
          triton::arch::x86::semantics::zfShl_s(inst, expr, dst, op2);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void shr_s(triton::arch::Instruction& inst) {
          auto dst   = inst.operands[0];
          auto src   = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = smt2lib::zx(dst.getBitSize() - src.getBitSize(), triton::api.buildSymbolicOperand(src));

          /* Create the SMT semantics */
          auto node = smt2lib::bvlshr(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "SHR operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::cfShr_s(inst, expr, dst, op1, op2);
          triton::arch::x86::semantics::ofShr_s(inst, expr, dst, op1, op2);
          triton::arch::x86::semantics::pfShl_s(inst, expr, dst, op2); /* Same that shl */
          triton::arch::x86::semantics::sfShl_s(inst, expr, dst, op2); /* Same that shl */
          triton::arch::x86::semantics::zfShl_s(inst, expr, dst, op2); /* Same that shl */

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void stc_s(triton::arch::Instruction& inst) {
          triton::arch::x86::semantics::setFlag_s(inst, TRITON_X86_REG_CF, "Sets carry flag");
          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void std_s(triton::arch::Instruction& inst) {
          triton::arch::x86::semantics::setFlag_s(inst, TRITON_X86_REG_DF, "Sets direction flag");
          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void sub_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = smt2lib::bvsub(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "SUB operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::af_s(inst, expr, dst, op1, op2);
          triton::arch::x86::semantics::cfSub_s(inst, expr, dst, op1, op2);
          triton::arch::x86::semantics::ofSub_s(inst, expr, dst, op1, op2);
          triton::arch::x86::semantics::pf_s(inst, expr, dst);
          triton::arch::x86::semantics::sf_s(inst, expr, dst);
          triton::arch::x86::semantics::zf_s(inst, expr, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void test_s(triton::arch::Instruction& inst) {
          auto src1 = inst.operands[0];
          auto src2 = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(src1);
          auto op2 = triton::api.buildSymbolicOperand(src2);

          /* Create the SMT semantics */
          auto node = smt2lib::bvand(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicVolatileExpression(inst, node, "AND operation");

          /* Spread taint */
          expr->isTainted = triton::api.isTainted(src1) | triton::api.isTainted(src2);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::clearFlag_s(inst, TRITON_X86_REG_CF, "Clears carry flag");
          triton::arch::x86::semantics::clearFlag_s(inst, TRITON_X86_REG_OF, "Clears overflow flag");
          triton::arch::x86::semantics::pf_s(inst, expr, src1, true);
          triton::arch::x86::semantics::sf_s(inst, expr, src1, true);
          triton::arch::x86::semantics::zf_s(inst, expr, src1, true);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void xadd_s(triton::arch::Instruction& inst) {
          auto dst  = inst.operands[0];
          auto src  = inst.operands[1];
          bool dstT = triton::api.isTainted(dst);
          bool srcT = triton::api.isTainted(src);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node1 = op2;
          auto node2 = op1;

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicExpression(inst, node1, dst, "XCHG operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, src, "XCHG operation");

          /* Spread taint */
          expr1->isTainted = triton::api.setTaint(dst, srcT);
          expr2->isTainted = triton::api.setTaint(src, dstT);

          /* Create symbolic operands */
          op1 = triton::api.buildSymbolicOperand(dst);
          op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node3 = smt2lib::bvadd(op1, op2);

          /* Create symbolic expression */
          auto expr3 = triton::api.createSymbolicExpression(inst, node3, dst, "ADD operation");

          /* Spread taint */
          expr3->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void xchg_s(triton::arch::Instruction& inst) {
          auto dst  = inst.operands[0];
          auto src  = inst.operands[1];
          bool dstT = triton::api.isTainted(dst);
          bool srcT = triton::api.isTainted(src);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node1 = op2;
          auto node2 = op1;

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicExpression(inst, node1, dst, "XCHG operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, src, "XCHG operation");

          /* Spread taint */
          expr1->isTainted = triton::api.setTaint(dst, srcT);
          expr2->isTainted = triton::api.setTaint(src, dstT);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void xor_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = smt2lib::bvxor(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "XOR operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::clearFlag_s(inst, TRITON_X86_REG_CF, "Clears carry flag");
          triton::arch::x86::semantics::clearFlag_s(inst, TRITON_X86_REG_OF, "Clears overflow flag");
          triton::arch::x86::semantics::pf_s(inst, expr, dst);
          triton::arch::x86::semantics::sf_s(inst, expr, dst);
          triton::arch::x86::semantics::zf_s(inst, expr, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void xorpd_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = smt2lib::bvxor(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "XORPD operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void xorps_s(triton::arch::Instruction& inst) {
          auto dst = inst.operands[0];
          auto src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(dst);
          auto op2 = triton::api.buildSymbolicOperand(src);

          /* Create the SMT semantics */
          auto node = smt2lib::bvxor(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "XORPS operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


      }; /* semantics namespace */
    }; /* x86 namespace */
  }; /* arch namespace */
}; /* triton namespace */

