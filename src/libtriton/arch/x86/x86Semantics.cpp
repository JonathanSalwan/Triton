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

Here is the instructions' list of what **Triton** can convert into \ref py_ast_page. Please note that our main
objective is not to support all semantics right now, we are currently focusing on the design of **Triton**'s
engines. When engines will be reliable, we will write the last semantics :-). However, feel free to add your
own semantics into the [appropriate file](x86Semantics_8cpp_source.html). Thanks to `wisk` and his
[Medusa project](https://github.com/wisk/medusa/blob/dev/arch/x86.yaml) which has been really useful.

\subsection SMT_Semantics_Supported_x86 x86 and x86-64 SMT semantics supported


Mnemonic                     | Extensions | Description
-----------------------------|------------|----------------------------------------------------
ADC                          |            | Add with Carry
ADD                          |            | Add
AND                          |            | Logical AND
ANDNPD                       | sse2       | Bitwise Logical AND NOT of Packed Double-Precision Floating-Point Values
ANDNPS                       | sse1       | Bitwise Logical AND NOT of Packed Single-Precision Floating-Point Values
ANDPD                        | sse2       | Bitwise Logical AND of Packed Double-Precision Floating-Point Values
ANDPS                        | sse1       | Bitwise Logical AND of Packed Single-Precision Floating-Point Values
BSF                          |            | Bit Scan Forward
BSR                          |            | Bit Scan Reverse
BSWAP                        |            | Byte Swap
BT                           |            | Bit Test
BTC                          |            | Bit Test and Complement
BTR                          |            | Bit Test and Reset
BTS                          |            | Bit Test and Set
CALL                         |            | Call Procedure
CBW                          |            | Convert byte (al) to word (ax).
CDQE                         |            | Convert dword (eax) to qword (rax).
CLC                          |            | Clear Carry Flag
CLD                          |            | Clear Direction Flag
CMC                          |            | Complement Carry Flag
CMOVA                        |            | Move if not below
CMOVAE                       |            | Move if not below or equal
CMOVB                        |            | Move if below
CMOVBE                       |            | Move if below or equal
CMOVE                        |            | Move if zero
CMOVG                        |            | Move if not less
CMOVGE                       |            | Move if not less or equal
CMOVL                        |            | Move if less
CMOVLE                       |            | Move if less or equal
CMOVNE                       |            | Move if not zero
CMOVNO                       |            | Move if not overflow
CMOVNP                       |            | Move if not parity
CMOVNS                       |            | Move if not sign
CMOVO                        |            | Move if overflow
CMOVP                        |            | Move if parity
CMOVS                        |            | Move if sign
CMP                          |            | Compare Two Operands
CMPSB                        |            | Compare byte at address
CMPSD                        |            | Compare doubleword at address
CMPSQ                        |            | Compare quadword at address
CMPSW                        |            | Compare word at address
CMPXCHG                      |            | Compare and Exchange
CMPXCHG16B                   |            | Compare and Exchange 16 Bytes
CMPXCHG8B                    |            | Compare and Exchange 8 Bytes
CPUID                        |            | CPU Identification
CQO                          |            | convert qword (rax) to oword (rdx:rax)
CWDE                         |            | Convert word (ax) to dword (eax).
DEC                          |            | Decrement by 1
DIV                          |            | Unsigned Divide
IDIV                         |            | Signed Divide
IMUL                         |            | Signed Multiply
INC                          |            | Increment by 1
JA                           |            | Jump if not below (Jump if above)
JAE                          |            | Jump if not below or equal (Jump if above or equal)
JB                           |            | Jump if below
JBE                          |            | Jump if below or equal
JE                           |            | Jump if zero (Jump if equal)
JG                           |            | Jump if not less or equal (Jump if greater)
JGE                          |            | Jump if not less (Jump if not less)
JL                           |            | Jump if less
JLE                          |            | Jump if less or equal
JMP                          |            | Jump
JNE                          |            | Jump if not equal
JNO                          |            | Jump if not overflow
JNP                          |            | Jump if not parity
JNS                          |            | Jump if not sign
JO                           |            | Jump if overflow
JP                           |            | Jump if parity
JS                           |            | Jump if sign
LDDQU                        | sse3       | Load Unaligned Integer 128 Bits
LDMXCSR                      | sse1       | Load MXCSR Register
LEA                          |            | Load Effective Address
LEAVE                        |            | High Level Procedure Exit
LODSB                        |            | Load byte at address
LODSD                        |            | Load doubleword at address
LODSQ                        |            | Load quadword at address
LODSW                        |            | Load word at address
MOV                          |            | Move
MOVABS                       |            | Move
MOVAPD                       | sse2       | Move Aligned Packed Double-Precision Floating-Point Values
MOVAPS                       | sse1       | Move Aligned Packed Single-Precision Floating-Point Values
MOVD                         | mmx/sse2   | Move Doubleword
MOVDDUP                      | sse3       | Move One Double-FP and Duplicate
MOVDQ2Q                      | sse2       | Move Quadword from XMM to MMX Technology Register
MOVDQA                       | sse2       | Move Aligned Double Quadword
MOVDQU                       | sse2       | Move Unaligned Double Quadword
MOVHLPS                      | sse1       | Move Packed Single-Precision Floating-Point Values High to Low
MOVHPD                       | sse2       | Move High Packed Double-Precision Floating-Point Values
MOVHPS                       | sse1       | Move High Packed Single-Precision Floating-Point Values
MOVLHPS                      | sse1       | Move Packed Single-Precision Floating-Point Values Low to High
MOVLPD                       | sse2       | Move Low Packed Double-Precision Floating-Point Values
MOVLPS                       | sse1       | Move Low Packed Single-Precision Floating-Point Values
MOVMSKPD                     | sse2       | Extract Packed Double-Precision Floating-Point Sign Mask
MOVMSKPS                     | sse1       | Extract Packed Single-Precision Floating-Point Sign Mask
MOVNTDQ                      | sse2       | Store Double Quadword Using Non-Temporal Hint
MOVNTI                       | sse2       | Store Doubleword Using Non-Temporal Hint
MOVNTPD                      | sse2       | Store Packed Double-Precision Floating-Point Values Using Non-Temporal Hint
MOVNTPS                      | sse1       | Store Packed Single-Precision Floating-Point Values Using Non-Temporal Hint
MOVNTQ                       | sse1       | Store of Quadword Using Non-Temporal Hint
MOVQ                         | mmx/sse2   | Move Quadword
MOVQ2DQ                      | sse2       | Move Quadword from MMX Technology to XMM Register
MOVSB                        |            | Move byte at address
MOVSD                        |            | Move doubleword at address
MOVSHDUP                     | sse3       | Move Packed Single-FP High and Duplicate
MOVSLDUP                     | sse3       | Move Packed Single-FP Low and Duplicate
MOVSQ                        |            | Move quadword at address
MOVSW                        |            | Move word at address
MOVSX                        |            | Move with Sign-Extension
MOVSXD                       |            | Move with Sign-Extension
MOVUPD                       | see2       | Move Unaligned Packed Double-Precision Floating- Point Values
MOVUPS                       | see1       | Move Unaligned Packed Single-Precision Floating- Point Values
MOVZX                        |            | Move with Zero-Extend
MUL                          |            | Unsigned Multiply
NEG                          |            | Two's Complement Negation
NOP                          |            | No Operation
NOT                          |            | One's Complement Negation
OR                           |            | Logical Inclusive OR
ORPD                         | sse2       | Bitwise Logical OR of Double-Precision Floating-Point Values
ORPS                         | sse1       | Bitwise Logical OR of Single-Precision Floating-Point Values
PADDB                        | mmx/sse2   | Add packed byte integers
PADDD                        | mmx/sse2   | Add packed doubleword integers
PADDQ                        | mmx/sse2   | Add packed quadword integers
PADDW                        | mmx/sse2   | Add packed word integers
PAND                         | mmx/sse2   | Logical AND
PANDN                        | mmx/sse2   | Logical AND NOT
PCMPEQB                      | mmx/sse2   | Compare Packed Data for Equal (bytes)
PCMPEQD                      | mmx/sse2   | Compare Packed Data for Equal (dwords)
PCMPEQW                      | mmx/sse2   | Compare Packed Data for Equal (words)
PCMPGTB                      | mmx/sse2   | Compare Packed Data for Greater Than (bytes)
PCMPGTD                      | mmx/sse2   | Compare Packed Data for Greater Than (dwords)
PCMPGTW                      | mmx/sse2   | Compare Packed Data for Greater Than (words)
PMAXSB                       | sse4.1     | Maximum of Packed Signed Byte Integers
PMAXSD                       | sse4.1     | Maximum of Packed Signed Doubleword Integers
PMAXSW                       | sse1       | Maximum of Packed Signed Word Integers
PMAXUB                       | sse1       | Maximum of Packed Unsigned Byte Integers
PMAXUD                       | sse4.1     | Maximum of Packed Unsigned Doubleword Integers
PMAXUW                       | sse4.1     | Maximum of Packed Unsigned Word Integers
PMINSB                       | sse4.1     | Minimum of Packed Signed Byte Integers
PMINSD                       | sse4.1     | Minimum of Packed Signed Doubleword Integers
PMINSW                       | sse1       | Minimum of Packed Signed Word Integers
PMINUB                       | sse1       | Minimum of Packed Unsigned Byte Integers
PMINUD                       | sse4.1     | Minimum of Packed Unsigned Doubleword Integers
PMINUW                       | sse4.1     | Minimum of Packed Unsigned Word Integers
PMOVMSKB                     | sse1       | Move Byte Mask
POP                          |            | Pop a Value from the Stack
POPAL/POPAD                  |            | Pop All General-Purpose Registers
POPFD                        |            | Pop Stack into EFLAGS Register
POPFQ                        |            | Pop Stack into RFLAGS Register
POR                          | mmx/sse2   | Bitwise Logical OR
PREFETCH                     | 3DNow      | Move data from m8 closer to the processor without expecting to write back
PREFETCHNTA                  | mmx/sse1   | Move data from m8 closer to the processor using NTA hint
PREFETCHT0                   | mmx/sse1   | Move data from m8 closer to the processor using T0 hint
PREFETCHT1                   | mmx/sse1   | Move data from m8 closer to the processor using T1 hint
PREFETCHT2                   | mmx/sse1   | Move data from m8 closer to the processor using T2 hint
PREFETCHW                    | 3DNow      | Move data from m8 closer to the processor in anticipation of a write
PSHUFD                       | sse2       | Shuffle Packed Doublewords
PSHUFHW                      | sse2       | Shuffle Packed High Words
PSHUFLW                      | sse2       | Shuffle Packed Low Words
PSHUFW                       | sse1       | Shuffle Packed Words
PSLLDQ                       | sse2       | Shift Double Quadword Left Logical
PSRLDQ                       | sse2       | Shift Double Quadword Right Logical
PSUBB                        | mmx/sse2   | Subtract packed byte integers
PSUBD                        | mmx/sse2   | Subtract packed doubleword integers
PSUBQ                        | mmx/sse2   | Subtract packed quadword integers
PSUBW                        | mmx/sse2   | Subtract packed word integers
PTEST                        | sse4.1     | Logical Compare
PUNPCKHBW                    | mmx,sse2   | Unpack High Data (Unpack and interleave high-order bytes)
PUNPCKHDQ                    | mmx,sse2   | Unpack High Data (Unpack and interleave high-order doublewords)
PUNPCKHQDQ                   | sse2       | Unpack High Data (Unpack and interleave high-order quadwords)
PUNPCKHWD                    | mmx,sse2   | Unpack High Data (Unpack and interleave high-order words)
PUNPCKLBW                    | mmx,sse2   | Unpack Low Data (Unpack and interleave low-order bytes)
PUNPCKLDQ                    | mmx,sse2   | Unpack Low Data (Unpack and interleave low-order doublewords)
PUNPCKLQDQ                   | sse2       | Unpack Low Data (Unpack and interleave low-order quadwords)
PUNPCKLWD                    | mmx,sse2   | Unpack Low Data (Unpack and interleave low-order words)
PUSH                         |            | Push a Value onto the Stack
PUSHAL/PUSHAD                |            | Push All General-Purpose Registers
PUSHFD                       |            | Push EFLAGS Register onto the Stack
PUSHFQ                       |            | Push RFLAGS Register onto the Stack
PXOR                         | mmx/sse2   | Logical Exclusive OR
RCL                          |            | Rotate Left with Carry
RCR                          |            | Rotate Right with Carry
RDTSC                        |            | Read Time-Stamp Counter
RET                          |            | Return from Procedure
ROL                          |            | Rotate Left
ROR                          |            | Rotate Right
SAL                          |            | Shift Left
SAR                          |            | Shift Right Signed
SBB                          |            | Integer Subtraction with Borrow
SCASB                        |            | Scan byte at address
SCASD                        |            | Scan doubleword at address
SCASQ                        |            | Scan quadword at address
SCASW                        |            | Scan word at address
SETA                         |            | Set byte if above
SETAE                        |            | Set byte if above or equal
SETB                         |            | Set byte if below
SETBE                        |            | Set byte if below or equal
SETE                         |            | Set byte if zero
SETG                         |            | Set byte if greater
SETGE                        |            | Set byte if greater or equal
SETL                         |            | Set byte if less
SETLE                        |            | Set byte if less or equal
SETNE                        |            | Set byte if not zero
SETNO                        |            | Set byte if not overflow
SETNP                        |            | Set byte if not parity
SETNS                        |            | Set byte if not sign
SETO                         |            | Set byte if overflow
SETP                         |            | Set byte if parity
SETS                         |            | Set byte if sign
SHL                          |            | Shift Left
SHR                          |            | Shift Right Unsigned
STC                          |            | Set Carry Flag
STD                          |            | Set Direction Flag
STMXCSR                      | sse1       | Store MXCSR Register State
STOSB                        |            | Store byte at address
STOSD                        |            | Store doubleword at address
STOSQ                        |            | Store quadword at address
STOSW                        |            | Store word at address
SUB                          |            | Subtract
TEST                         |            | Logical Compare
UNPCKHPD                     | sse2       | Unpack and Interleave High Packed Double- Precision Floating-Point Values
UNPCKHPS                     | sse1       | Unpack and Interleave High Packed Single-Precision Floating-Point Values
UNPCKLPD                     | sse2       | Unpack and Interleave Low Packed Double-Precision Floating-Point Values
UNPCKLPS                     | sse1       | Unpack and Interleave Low Packed Single-Precision Floating-Point Values
VMOVDQA                      | avx        | VEX Move aligned packed integer values
VPTEST                       | avx        | VEX Logical Compare
XADD                         |            | Exchange and Add
XCHG                         |            | Exchange Register/Memory with Register
XOR                          |            | Logical Exclusive OR
XORPD                        | sse2       | Bitwise Logical XOR for Double-Precision Floating-Point Values
XORPS                        | sse1       | Bitwise Logical XOR for Single-Precision Floating-Point Values

*/



namespace triton {
  namespace arch {
    namespace x86 {
      namespace semantics {


        void build(triton::arch::Instruction& inst) {
          switch (inst.getType()) {
            case ID_INS_ADC:            triton::arch::x86::semantics::adc_s(inst);          break;
            case ID_INS_ADD:            triton::arch::x86::semantics::add_s(inst);          break;
            case ID_INS_AND:            triton::arch::x86::semantics::and_s(inst);          break;
            case ID_INS_ANDNPD:         triton::arch::x86::semantics::andnpd_s(inst);       break;
            case ID_INS_ANDNPS:         triton::arch::x86::semantics::andnps_s(inst);       break;
            case ID_INS_ANDPD:          triton::arch::x86::semantics::andpd_s(inst);        break;
            case ID_INS_ANDPS:          triton::arch::x86::semantics::andps_s(inst);        break;
            case ID_INS_BSF:            triton::arch::x86::semantics::bsf_s(inst);          break;
            case ID_INS_BSR:            triton::arch::x86::semantics::bsr_s(inst);          break;
            case ID_INS_BSWAP:          triton::arch::x86::semantics::bswap_s(inst);        break;
            case ID_INS_BT:             triton::arch::x86::semantics::bt_s(inst);           break;
            case ID_INS_BTC:            triton::arch::x86::semantics::btc_s(inst);          break;
            case ID_INS_BTR:            triton::arch::x86::semantics::btr_s(inst);          break;
            case ID_INS_BTS:            triton::arch::x86::semantics::bts_s(inst);          break;
            case ID_INS_CALL:           triton::arch::x86::semantics::call_s(inst);         break;
            case ID_INS_CBW:            triton::arch::x86::semantics::cbw_s(inst);          break;
            case ID_INS_CDQE:           triton::arch::x86::semantics::cdqe_s(inst);         break;
            case ID_INS_CLC:            triton::arch::x86::semantics::clc_s(inst);          break;
            case ID_INS_CLD:            triton::arch::x86::semantics::cld_s(inst);          break;
            case ID_INS_CMC:            triton::arch::x86::semantics::cmc_s(inst);          break;
            case ID_INS_CMOVA:          triton::arch::x86::semantics::cmova_s(inst);        break;
            case ID_INS_CMOVAE:         triton::arch::x86::semantics::cmovae_s(inst);       break;
            case ID_INS_CMOVB:          triton::arch::x86::semantics::cmovb_s(inst);        break;
            case ID_INS_CMOVBE:         triton::arch::x86::semantics::cmovbe_s(inst);       break;
            case ID_INS_CMOVE:          triton::arch::x86::semantics::cmove_s(inst);        break;
            case ID_INS_CMOVG:          triton::arch::x86::semantics::cmovg_s(inst);        break;
            case ID_INS_CMOVGE:         triton::arch::x86::semantics::cmovge_s(inst);       break;
            case ID_INS_CMOVL:          triton::arch::x86::semantics::cmovl_s(inst);        break;
            case ID_INS_CMOVLE:         triton::arch::x86::semantics::cmovle_s(inst);       break;
            case ID_INS_CMOVNE:         triton::arch::x86::semantics::cmovne_s(inst);       break;
            case ID_INS_CMOVNO:         triton::arch::x86::semantics::cmovno_s(inst);       break;
            case ID_INS_CMOVNP:         triton::arch::x86::semantics::cmovnp_s(inst);       break;
            case ID_INS_CMOVNS:         triton::arch::x86::semantics::cmovns_s(inst);       break;
            case ID_INS_CMOVO:          triton::arch::x86::semantics::cmovo_s(inst);        break;
            case ID_INS_CMOVP:          triton::arch::x86::semantics::cmovp_s(inst);        break;
            case ID_INS_CMOVS:          triton::arch::x86::semantics::cmovs_s(inst);        break;
            case ID_INS_CMP:            triton::arch::x86::semantics::cmp_s(inst);          break;
            case ID_INS_CMPSB:          triton::arch::x86::semantics::cmpsb_s(inst);        break;
            case ID_INS_CMPSD:          triton::arch::x86::semantics::cmpsd_s(inst);        break;
            case ID_INS_CMPSQ:          triton::arch::x86::semantics::cmpsq_s(inst);        break;
            case ID_INS_CMPSW:          triton::arch::x86::semantics::cmpsw_s(inst);        break;
            case ID_INS_CMPXCHG:        triton::arch::x86::semantics::cmpxchg_s(inst);      break;
            case ID_INS_CMPXCHG16B:     triton::arch::x86::semantics::cmpxchg16b_s(inst);   break;
            case ID_INS_CMPXCHG8B:      triton::arch::x86::semantics::cmpxchg8b_s(inst);    break;
            case ID_INS_CPUID:          triton::arch::x86::semantics::cpuid_s(inst);        break;
            case ID_INS_CQO:            triton::arch::x86::semantics::cqo_s(inst);          break;
            case ID_INS_CWDE:           triton::arch::x86::semantics::cwde_s(inst);         break;
            case ID_INS_DEC:            triton::arch::x86::semantics::dec_s(inst);          break;
            case ID_INS_DIV:            triton::arch::x86::semantics::div_s(inst);          break;
            case ID_INS_IDIV:           triton::arch::x86::semantics::idiv_s(inst);         break;
            case ID_INS_IMUL:           triton::arch::x86::semantics::imul_s(inst);         break;
            case ID_INS_INC:            triton::arch::x86::semantics::inc_s(inst);          break;
            case ID_INS_JA:             triton::arch::x86::semantics::ja_s(inst);           break;
            case ID_INS_JAE:            triton::arch::x86::semantics::jae_s(inst);          break;
            case ID_INS_JB:             triton::arch::x86::semantics::jb_s(inst);           break;
            case ID_INS_JBE:            triton::arch::x86::semantics::jbe_s(inst);          break;
            case ID_INS_JE:             triton::arch::x86::semantics::je_s(inst);           break;
            case ID_INS_JG:             triton::arch::x86::semantics::jg_s(inst);           break;
            case ID_INS_JGE:            triton::arch::x86::semantics::jge_s(inst);          break;
            case ID_INS_JL:             triton::arch::x86::semantics::jl_s(inst);           break;
            case ID_INS_JLE:            triton::arch::x86::semantics::jle_s(inst);          break;
            case ID_INS_JMP:            triton::arch::x86::semantics::jmp_s(inst);          break;
            case ID_INS_JNE:            triton::arch::x86::semantics::jne_s(inst);          break;
            case ID_INS_JNO:            triton::arch::x86::semantics::jno_s(inst);          break;
            case ID_INS_JNP:            triton::arch::x86::semantics::jnp_s(inst);          break;
            case ID_INS_JNS:            triton::arch::x86::semantics::jns_s(inst);          break;
            case ID_INS_JO:             triton::arch::x86::semantics::jo_s(inst);           break;
            case ID_INS_JP:             triton::arch::x86::semantics::jp_s(inst);           break;
            case ID_INS_JS:             triton::arch::x86::semantics::js_s(inst);           break;
            case ID_INS_LDDQU:          triton::arch::x86::semantics::lddqu_s(inst);        break;
            case ID_INS_LDMXCSR:        triton::arch::x86::semantics::ldmxcsr_s(inst);      break;
            case ID_INS_LEA:            triton::arch::x86::semantics::lea_s(inst);          break;
            case ID_INS_LEAVE:          triton::arch::x86::semantics::leave_s(inst);        break;
            case ID_INS_LODSB:          triton::arch::x86::semantics::lodsb_s(inst);        break;
            case ID_INS_LODSD:          triton::arch::x86::semantics::lodsd_s(inst);        break;
            case ID_INS_LODSQ:          triton::arch::x86::semantics::lodsq_s(inst);        break;
            case ID_INS_LODSW:          triton::arch::x86::semantics::lodsw_s(inst);        break;
            case ID_INS_MOV:            triton::arch::x86::semantics::mov_s(inst);          break;
            case ID_INS_MOVABS:         triton::arch::x86::semantics::movabs_s(inst);       break;
            case ID_INS_MOVAPD:         triton::arch::x86::semantics::movapd_s(inst);       break;
            case ID_INS_MOVAPS:         triton::arch::x86::semantics::movaps_s(inst);       break;
            case ID_INS_MOVD:           triton::arch::x86::semantics::movd_s(inst);         break;
            case ID_INS_MOVDDUP:        triton::arch::x86::semantics::movddup_s(inst);      break;
            case ID_INS_MOVDQ2Q:        triton::arch::x86::semantics::movdq2q_s(inst);      break;
            case ID_INS_MOVDQA:         triton::arch::x86::semantics::movdqa_s(inst);       break;
            case ID_INS_MOVDQU:         triton::arch::x86::semantics::movdqu_s(inst);       break;
            case ID_INS_MOVHLPS:        triton::arch::x86::semantics::movhlps_s(inst);      break;
            case ID_INS_MOVHPD:         triton::arch::x86::semantics::movhpd_s(inst);       break;
            case ID_INS_MOVHPS:         triton::arch::x86::semantics::movhps_s(inst);       break;
            case ID_INS_MOVLHPS:        triton::arch::x86::semantics::movlhps_s(inst);      break;
            case ID_INS_MOVLPD:         triton::arch::x86::semantics::movlpd_s(inst);       break;
            case ID_INS_MOVLPS:         triton::arch::x86::semantics::movlps_s(inst);       break;
            case ID_INS_MOVMSKPD:       triton::arch::x86::semantics::movmskpd_s(inst);     break;
            case ID_INS_MOVMSKPS:       triton::arch::x86::semantics::movmskps_s(inst);     break;
            case ID_INS_MOVNTDQ:        triton::arch::x86::semantics::movntdq_s(inst);      break;
            case ID_INS_MOVNTI:         triton::arch::x86::semantics::movnti_s(inst);       break;
            case ID_INS_MOVNTPD:        triton::arch::x86::semantics::movntpd_s(inst);      break;
            case ID_INS_MOVNTPS:        triton::arch::x86::semantics::movntps_s(inst);      break;
            case ID_INS_MOVNTQ:         triton::arch::x86::semantics::movntq_s(inst);       break;
            case ID_INS_MOVQ2DQ:        triton::arch::x86::semantics::movq2dq_s(inst);      break;
            case ID_INS_MOVQ:           triton::arch::x86::semantics::movq_s(inst);         break;
            case ID_INS_MOVSB:          triton::arch::x86::semantics::movsb_s(inst);        break;
            case ID_INS_MOVSD:          triton::arch::x86::semantics::movsd_s(inst);        break;
            case ID_INS_MOVSHDUP:       triton::arch::x86::semantics::movshdup_s(inst);     break;
            case ID_INS_MOVSLDUP:       triton::arch::x86::semantics::movsldup_s(inst);     break;
            case ID_INS_MOVSQ:          triton::arch::x86::semantics::movsq_s(inst);        break;
            case ID_INS_MOVSW:          triton::arch::x86::semantics::movsw_s(inst);        break;
            case ID_INS_MOVSX:          triton::arch::x86::semantics::movsx_s(inst);        break;
            case ID_INS_MOVSXD:         triton::arch::x86::semantics::movsxd_s(inst);       break;
            case ID_INS_MOVUPD:         triton::arch::x86::semantics::movupd_s(inst);       break;
            case ID_INS_MOVUPS:         triton::arch::x86::semantics::movups_s(inst);       break;
            case ID_INS_MOVZX:          triton::arch::x86::semantics::movzx_s(inst);        break;
            case ID_INS_MUL:            triton::arch::x86::semantics::mul_s(inst);          break;
            case ID_INS_NEG:            triton::arch::x86::semantics::neg_s(inst);          break;
            case ID_INS_NOP:            triton::arch::x86::semantics::nop_s(inst);          break;
            case ID_INS_NOT:            triton::arch::x86::semantics::not_s(inst);          break;
            case ID_INS_OR:             triton::arch::x86::semantics::or_s(inst);           break;
            case ID_INS_ORPD:           triton::arch::x86::semantics::orpd_s(inst);         break;
            case ID_INS_ORPS:           triton::arch::x86::semantics::orps_s(inst);         break;
            case ID_INS_PADDB:          triton::arch::x86::semantics::paddb_s(inst);        break;
            case ID_INS_PADDD:          triton::arch::x86::semantics::paddd_s(inst);        break;
            case ID_INS_PADDQ:          triton::arch::x86::semantics::paddq_s(inst);        break;
            case ID_INS_PADDW:          triton::arch::x86::semantics::paddw_s(inst);        break;
            case ID_INS_PAND:           triton::arch::x86::semantics::pand_s(inst);         break;
            case ID_INS_PANDN:          triton::arch::x86::semantics::pandn_s(inst);        break;
            case ID_INS_PCMPEQB:        triton::arch::x86::semantics::pcmpeqb_s(inst);      break;
            case ID_INS_PCMPEQD:        triton::arch::x86::semantics::pcmpeqd_s(inst);      break;
            case ID_INS_PCMPEQW:        triton::arch::x86::semantics::pcmpeqw_s(inst);      break;
            case ID_INS_PCMPGTB:        triton::arch::x86::semantics::pcmpgtb_s(inst);      break;
            case ID_INS_PCMPGTD:        triton::arch::x86::semantics::pcmpgtd_s(inst);      break;
            case ID_INS_PCMPGTW:        triton::arch::x86::semantics::pcmpgtw_s(inst);      break;
            case ID_INS_PMAXSB:         triton::arch::x86::semantics::pmaxsb_s(inst);       break;
            case ID_INS_PMAXSD:         triton::arch::x86::semantics::pmaxsd_s(inst);       break;
            case ID_INS_PMAXSW:         triton::arch::x86::semantics::pmaxsw_s(inst);       break;
            case ID_INS_PMAXUB:         triton::arch::x86::semantics::pmaxub_s(inst);       break;
            case ID_INS_PMAXUD:         triton::arch::x86::semantics::pmaxud_s(inst);       break;
            case ID_INS_PMAXUW:         triton::arch::x86::semantics::pmaxuw_s(inst);       break;
            case ID_INS_PMINSB:         triton::arch::x86::semantics::pminsb_s(inst);       break;
            case ID_INS_PMINSD:         triton::arch::x86::semantics::pminsd_s(inst);       break;
            case ID_INS_PMINSW:         triton::arch::x86::semantics::pminsw_s(inst);       break;
            case ID_INS_PMINUB:         triton::arch::x86::semantics::pminub_s(inst);       break;
            case ID_INS_PMINUD:         triton::arch::x86::semantics::pminud_s(inst);       break;
            case ID_INS_PMINUW:         triton::arch::x86::semantics::pminuw_s(inst);       break;
            case ID_INS_PMOVMSKB:       triton::arch::x86::semantics::pmovmskb_s(inst);     break;
            case ID_INS_POP:            triton::arch::x86::semantics::pop_s(inst);          break;
            case ID_INS_POPAL:          triton::arch::x86::semantics::popal_s(inst);        break;
            case ID_INS_POPFD:          triton::arch::x86::semantics::popfd_s(inst);        break;
            case ID_INS_POPFQ:          triton::arch::x86::semantics::popfq_s(inst);        break;
            case ID_INS_POR:            triton::arch::x86::semantics::por_s(inst);          break;
            case ID_INS_PREFETCH:       triton::arch::x86::semantics::prefetchx_s(inst);    break;
            case ID_INS_PREFETCHNTA:    triton::arch::x86::semantics::prefetchx_s(inst);    break;
            case ID_INS_PREFETCHT0:     triton::arch::x86::semantics::prefetchx_s(inst);    break;
            case ID_INS_PREFETCHT1:     triton::arch::x86::semantics::prefetchx_s(inst);    break;
            case ID_INS_PREFETCHT2:     triton::arch::x86::semantics::prefetchx_s(inst);    break;
            case ID_INS_PREFETCHW:      triton::arch::x86::semantics::prefetchx_s(inst);    break;
            case ID_INS_PSHUFD:         triton::arch::x86::semantics::pshufd_s(inst);       break;
            case ID_INS_PSHUFHW:        triton::arch::x86::semantics::pshufhw_s(inst);      break;
            case ID_INS_PSHUFLW:        triton::arch::x86::semantics::pshuflw_s(inst);      break;
            case ID_INS_PSHUFW:         triton::arch::x86::semantics::pshufw_s(inst);       break;
            case ID_INS_PSLLDQ:         triton::arch::x86::semantics::pslldq_s(inst);       break;
            case ID_INS_PSRLDQ:         triton::arch::x86::semantics::psrldq_s(inst);       break;
            case ID_INS_PSUBB:          triton::arch::x86::semantics::psubb_s(inst);        break;
            case ID_INS_PSUBD:          triton::arch::x86::semantics::psubd_s(inst);        break;
            case ID_INS_PSUBQ:          triton::arch::x86::semantics::psubq_s(inst);        break;
            case ID_INS_PSUBW:          triton::arch::x86::semantics::psubw_s(inst);        break;
            case ID_INS_PTEST:          triton::arch::x86::semantics::ptest_s(inst);        break;
            case ID_INS_PUNPCKHBW:      triton::arch::x86::semantics::punpckhbw_s(inst);    break;
            case ID_INS_PUNPCKHDQ:      triton::arch::x86::semantics::punpckhdq_s(inst);    break;
            case ID_INS_PUNPCKHQDQ:     triton::arch::x86::semantics::punpckhqdq_s(inst);   break;
            case ID_INS_PUNPCKHWD:      triton::arch::x86::semantics::punpckhwd_s(inst);    break;
            case ID_INS_PUNPCKLBW:      triton::arch::x86::semantics::punpcklbw_s(inst);    break;
            case ID_INS_PUNPCKLDQ:      triton::arch::x86::semantics::punpckldq_s(inst);    break;
            case ID_INS_PUNPCKLQDQ:     triton::arch::x86::semantics::punpcklqdq_s(inst);   break;
            case ID_INS_PUNPCKLWD:      triton::arch::x86::semantics::punpcklwd_s(inst);    break;
            case ID_INS_PUSH:           triton::arch::x86::semantics::push_s(inst);         break;
            case ID_INS_PUSHAL:         triton::arch::x86::semantics::pushal_s(inst);       break;
            case ID_INS_PUSHFD:         triton::arch::x86::semantics::pushfd_s(inst);       break;
            case ID_INS_PUSHFQ:         triton::arch::x86::semantics::pushfq_s(inst);       break;
            case ID_INS_PXOR:           triton::arch::x86::semantics::pxor_s(inst);         break;
            case ID_INS_RCL:            triton::arch::x86::semantics::rcl_s(inst);          break;
            case ID_INS_RCR:            triton::arch::x86::semantics::rcr_s(inst);          break;
            case ID_INS_RDTSC:          triton::arch::x86::semantics::rdtsc_s(inst);        break;
            case ID_INS_RET:            triton::arch::x86::semantics::ret_s(inst);          break;
            case ID_INS_ROL:            triton::arch::x86::semantics::rol_s(inst);          break;
            case ID_INS_ROR:            triton::arch::x86::semantics::ror_s(inst);          break;
            case ID_INS_SAL:            triton::arch::x86::semantics::shl_s(inst);          break;
            case ID_INS_SAR:            triton::arch::x86::semantics::sar_s(inst);          break;
            case ID_INS_SBB:            triton::arch::x86::semantics::sbb_s(inst);          break;
            case ID_INS_SCASB:          triton::arch::x86::semantics::scasb_s(inst);        break;
            case ID_INS_SCASD:          triton::arch::x86::semantics::scasd_s(inst);        break;
            case ID_INS_SCASQ:          triton::arch::x86::semantics::scasq_s(inst);        break;
            case ID_INS_SCASW:          triton::arch::x86::semantics::scasw_s(inst);        break;
            case ID_INS_SETA:           triton::arch::x86::semantics::seta_s(inst);         break;
            case ID_INS_SETAE:          triton::arch::x86::semantics::setae_s(inst);        break;
            case ID_INS_SETB:           triton::arch::x86::semantics::setb_s(inst);         break;
            case ID_INS_SETBE:          triton::arch::x86::semantics::setbe_s(inst);        break;
            case ID_INS_SETE:           triton::arch::x86::semantics::sete_s(inst);         break;
            case ID_INS_SETG:           triton::arch::x86::semantics::setg_s(inst);         break;
            case ID_INS_SETGE:          triton::arch::x86::semantics::setge_s(inst);        break;
            case ID_INS_SETL:           triton::arch::x86::semantics::setl_s(inst);         break;
            case ID_INS_SETLE:          triton::arch::x86::semantics::setle_s(inst);        break;
            case ID_INS_SETNE:          triton::arch::x86::semantics::setne_s(inst);        break;
            case ID_INS_SETNO:          triton::arch::x86::semantics::setno_s(inst);        break;
            case ID_INS_SETNP:          triton::arch::x86::semantics::setnp_s(inst);        break;
            case ID_INS_SETNS:          triton::arch::x86::semantics::setns_s(inst);        break;
            case ID_INS_SETO:           triton::arch::x86::semantics::seto_s(inst);         break;
            case ID_INS_SETP:           triton::arch::x86::semantics::setp_s(inst);         break;
            case ID_INS_SETS:           triton::arch::x86::semantics::sets_s(inst);         break;
            case ID_INS_SHL:            triton::arch::x86::semantics::shl_s(inst);          break;
            case ID_INS_SHR:            triton::arch::x86::semantics::shr_s(inst);          break;
            case ID_INS_STC:            triton::arch::x86::semantics::stc_s(inst);          break;
            case ID_INS_STD:            triton::arch::x86::semantics::std_s(inst);          break;
            case ID_INS_STMXCSR:        triton::arch::x86::semantics::stmxcsr_s(inst);      break;
            case ID_INS_STOSB:          triton::arch::x86::semantics::stosb_s(inst);        break;
            case ID_INS_STOSD:          triton::arch::x86::semantics::stosd_s(inst);        break;
            case ID_INS_STOSQ:          triton::arch::x86::semantics::stosq_s(inst);        break;
            case ID_INS_STOSW:          triton::arch::x86::semantics::stosw_s(inst);        break;
            case ID_INS_SUB:            triton::arch::x86::semantics::sub_s(inst);          break;
            case ID_INS_TEST:           triton::arch::x86::semantics::test_s(inst);         break;
            case ID_INS_UNPCKHPD:       triton::arch::x86::semantics::unpckhpd_s(inst);     break;
            case ID_INS_UNPCKHPS:       triton::arch::x86::semantics::unpckhps_s(inst);     break;
            case ID_INS_UNPCKLPD:       triton::arch::x86::semantics::unpcklpd_s(inst);     break;
            case ID_INS_UNPCKLPS:       triton::arch::x86::semantics::unpcklps_s(inst);     break;
            case ID_INS_VMOVDQA:        triton::arch::x86::semantics::vmovdqa_s(inst);      break;
            case ID_INS_VPTEST:         triton::arch::x86::semantics::vptest_s(inst);       break;
            case ID_INS_XADD:           triton::arch::x86::semantics::xadd_s(inst);         break;
            case ID_INS_XCHG:           triton::arch::x86::semantics::xchg_s(inst);         break;
            case ID_INS_XOR:            triton::arch::x86::semantics::xor_s(inst);          break;
            case ID_INS_XORPD:          triton::arch::x86::semantics::xorpd_s(inst);        break;
            case ID_INS_XORPS:          triton::arch::x86::semantics::xorps_s(inst);        break;
          }
        }


        void alignAddStack_s(triton::arch::Instruction& inst, triton::uint32 delta) {
          auto dst = triton::arch::OperandWrapper(TRITON_X86_REG_SP.getParent());

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::ast::bv(delta, dst.getBitSize());

          /* Create the semantics */
          auto node = triton::ast::bvadd(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "Stack alignment");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, dst);
        }


        void alignSubStack_s(triton::arch::Instruction& inst, triton::uint32 delta) {
          auto dst = triton::arch::OperandWrapper(TRITON_X86_REG_SP.getParent());

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::ast::bv(delta, dst.getBitSize());

          /* Create the semantics */
          auto node = triton::ast::bvsub(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "Stack alignment");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, dst);
        }


        void clearFlag_s(triton::arch::Instruction& inst, triton::arch::RegisterOperand& flag, std::string comment) {
          /* Create the semantics */
          auto node = triton::ast::bv(0, 1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, flag, comment);

          /* Spread taint */
          expr->isTainted = triton::api.setTaintRegister(flag, triton::engines::taint::UNTAINTED);
        }


        void setFlag_s(triton::arch::Instruction& inst, triton::arch::RegisterOperand& flag, std::string comment) {
          /* Create the semantics */
          auto node = triton::ast::bv(1, 1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, flag, comment);

          /* Spread taint */
          expr->isTainted = triton::api.setTaintRegister(flag, triton::engines::taint::UNTAINTED);
        }


        void controlFlow_s(triton::arch::Instruction& inst) {
          auto pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC.getParent());
          auto counter = triton::arch::OperandWrapper(TRITON_X86_REG_CX.getParent());
          auto zf      = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          switch (inst.getPrefix()) {

            case triton::arch::x86::ID_PREFIX_REP: {
              /* Create symbolic operands */
              auto op1 = triton::api.buildSymbolicOperand(inst, counter);

              /* Create the semantics for Counter */
              auto node1 = triton::ast::bvsub(op1, triton::ast::bv(1, counter.getBitSize()));

              /* Create the semantics for PC */
              auto node2 = triton::ast::ite(
                       triton::ast::equal(node1, triton::ast::bv(0, counter.getBitSize())),
                       triton::ast::bv(inst.getNextAddress(), pc.getBitSize()),
                       triton::ast::bv(inst.getAddress(), pc.getBitSize())
                     );

              /* Create symbolic expression */
              auto expr1 = triton::api.createSymbolicExpression(inst, node1, counter, "Counter operation");
              auto expr2 = triton::api.createSymbolicExpression(inst, node2, pc, "Program Counter");

              /* Spread taint for PC */
              expr1->isTainted = triton::api.taintUnion(counter, counter);
              expr2->isTainted = triton::api.taintAssignment(pc, counter);
              break;
            }

            case triton::arch::x86::ID_PREFIX_REPE: {
              /* Create symbolic operands */
              auto op1 = triton::api.buildSymbolicOperand(inst, counter);
              auto op2 = triton::api.buildSymbolicOperand(inst, zf);

              /* Create the semantics for Counter */
              auto node1 = triton::ast::bvsub(op1, triton::ast::bv(1, counter.getBitSize()));

              /* Create the semantics for PC */
              auto node2 = triton::ast::ite(
                       triton::ast::lor(
                         triton::ast::equal(node1, triton::ast::bv(0, counter.getBitSize())),
                         triton::ast::equal(op2, triton::ast::bvfalse())
                       ),
                       triton::ast::bv(inst.getNextAddress(), pc.getBitSize()),
                       triton::ast::bv(inst.getAddress(), pc.getBitSize())
                     );

              /* Create symbolic expression */
              auto expr1 = triton::api.createSymbolicExpression(inst, node1, counter, "Counter operation");
              auto expr2 = triton::api.createSymbolicExpression(inst, node2, pc, "Program Counter");

              /* Spread taint */
              expr1->isTainted = triton::api.taintUnion(counter, counter);
              expr2->isTainted = triton::api.taintAssignment(pc, counter);
              break;
            }

            case triton::arch::x86::ID_PREFIX_REPNE: {
              /* Create symbolic operands */
              auto op1 = triton::api.buildSymbolicOperand(inst, counter);
              auto op2 = triton::api.buildSymbolicOperand(inst, zf);

              /* Create the semantics for Counter */
              auto node1 = triton::ast::bvsub(op1, triton::ast::bv(1, counter.getBitSize()));

              /* Create the semantics for PC */
              auto node2 = triton::ast::ite(
                       triton::ast::lor(
                         triton::ast::equal(node1, triton::ast::bv(0, counter.getBitSize())),
                         triton::ast::equal(op2, triton::ast::bvtrue())
                       ),
                       triton::ast::bv(inst.getNextAddress(), pc.getBitSize()),
                       triton::ast::bv(inst.getAddress(), pc.getBitSize())
                     );

              /* Create symbolic expression */
              auto expr1 = triton::api.createSymbolicExpression(inst, node1, counter, "Counter operation");
              auto expr2 = triton::api.createSymbolicExpression(inst, node2, pc, "Program Counter");

              /* Spread taint */
              expr1->isTainted = triton::api.taintUnion(counter, counter);
              expr2->isTainted = triton::api.taintAssignment(pc, counter);
              break;
            }

            default: {
              /* Create the semantics */
              auto node = triton::ast::bv(inst.getNextAddress(), pc.getBitSize());

              /* Create symbolic expression */
              auto expr = triton::api.createSymbolicRegisterExpression(inst, node, TRITON_X86_REG_PC, "Program Counter");

              /* Spread taint */
              expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_PC, triton::engines::taint::UNTAINTED);
              break;
            }

          }
        }


        void af_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, triton::ast::AbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();

          /*
           * Create the semantic.
           * af = 0x10 == (0x10 & (regDst ^ op1 ^ op2))
           */
          auto node = triton::ast::ite(
                        triton::ast::equal(
                          triton::ast::bv(0x10, bvSize),
                          triton::ast::bvand(
                            triton::ast::bv(0x10, bvSize),
                            triton::ast::bvxor(
                              triton::ast::extract(high, low, triton::ast::reference(parent->getId())),
                              triton::ast::bvxor(op1, op2)
                            )
                          )
                        ),
                        triton::ast::bv(1, 1),
                        triton::ast::bv(0, 1)
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_AF, "Adjust flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_AF, parent->isTainted);
        }


        void afNeg_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();

          /*
           * Create the semantic.
           * af = 0x10 == (0x10 & (op1 ^ regDst))
           */
          auto node = triton::ast::ite(
                        triton::ast::equal(
                          triton::ast::bv(0x10, bvSize),
                          triton::ast::bvand(
                            triton::ast::bv(0x10, bvSize),
                            triton::ast::bvxor(
                              op1,
                              triton::ast::extract(high, low, triton::ast::reference(parent->getId()))
                            )
                          )
                        ),
                        triton::ast::bv(1, 1),
                        triton::ast::bv(0, 1)
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_AF, "Adjust flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_AF, parent->isTainted);
        }


        void cfAdd_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, triton::ast::AbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();

          /*
           * Create the semantic.
           * cf = extract(bvSize, bvSize, ((op0 & op1) ^ ((op0 ^ op1 ^ parent) & (op0 ^ op1))));
           */
          auto node = triton::ast::extract(high, high,
                        triton::ast::bvxor(
                          triton::ast::bvand(op1, op2),
                          triton::ast::bvand(
                            triton::ast::bvxor(
                              triton::ast::bvxor(op1, op2),
                              triton::ast::extract(high, low, triton::ast::reference(parent->getId()))
                            ),
                          triton::ast::bvxor(op1, op2))
                        )
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
        }


        void cfImul_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, triton::ast::AbstractNode* res, bool vol) {
          /*
           * Create the semantic.
           * cf = 0 if sx(dst) == node else 1
           */
          auto node = triton::ast::ite(
                        triton::ast::equal(
                          triton::ast::sx(dst.getBitSize(), op1),
                          res
                        ),
                        triton::ast::bv(0, 1),
                        triton::ast::bv(1, 1)
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
        }


        void cfMul_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, bool vol) {
          auto bvSize = dst.getBitSize();

          /*
           * Create the semantic.
           * cf = 0 if op1 == 0 else 1
           */
          auto node = triton::ast::ite(
                        triton::ast::equal(
                          op1,
                          triton::ast::bv(0, bvSize)
                        ),
                        triton::ast::bv(0, 1),
                        triton::ast::bv(1, 1)
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
        }


        void cfNeg_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, bool vol) {
          auto bvSize = dst.getBitSize();

          /*
           * Create the semantic.
           * cf = 0 if op1 == 0 else 1
           */
          auto node = triton::ast::ite(
                        triton::ast::equal(
                          op1,
                          triton::ast::bv(0, bvSize)
                        ),
                        triton::ast::bv(0, 1),
                        triton::ast::bv(1, 1)
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
        }


        void cfPtest_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();

          /*
           * Create the semantic.
           * cf = 0 == regDst
           */
          auto node = triton::ast::ite(
                        triton::ast::equal(
                          triton::ast::extract(high, low, triton::ast::reference(parent->getId())),
                          triton::ast::bv(0, bvSize)
                        ),
                        triton::ast::bv(1, 1),
                        triton::ast::bv(0, 1)
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
        }


        void cfRcl_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();
          auto cf     = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

          /*
           * Create the semantic.
           * cf = high(res & 1) if op2 != 0 else undefined
           * As the second operand can't be symbolized, there is
           * no symbolic expression available. So, we must use the
           * concretization of the op2.
           */
          triton::ast::AbstractNode* node;
          if (op2->getKind() != triton::ast::DECIMAL_NODE)
            throw std::runtime_error("triton::arch::x86::semantics::cfRcl_s(): op2 must be a DecimalNode node.");

          if (reinterpret_cast<triton::ast::DecimalNode*>(op2)->getValue() != 0)
            node = triton::ast::extract(high, high, triton::ast::reference(parent->getId()));
          else
            node = triton::api.buildSymbolicOperand(inst, cf);

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
        }


        void cfRol_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op2, bool vol) {
          auto low = vol ? 0 : dst.getAbstractLow();
          auto cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

          /*
           * Create the semantic.
           * cf = (res & 1) if op2 != 0 else undefined
           * As the second operand can't be symbolized, there is
           * no symbolic expression available. So, we must use the
           * concretization of the op2.
           */
          triton::ast::AbstractNode* node;
          if (op2->getKind() != triton::ast::DECIMAL_NODE)
            throw std::runtime_error("triton::arch::x86::semantics::cfRol_s(): op2 must be a DecimalNode node.");

          if (reinterpret_cast<triton::ast::DecimalNode*>(op2)->getValue() != 0)
            node = triton::ast::extract(low, low, triton::ast::reference(parent->getId()));
          else
            node = triton::api.buildSymbolicOperand(inst, cf);

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
        }


        void cfRor_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();
          auto cf     = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

          /*
           * Create the semantic.
           * cf = (res >> bvSize - 1) & 1 if op2 != 0 else undefined
           * As the second operand can't be symbolized, there is
           * no symbolic expression available. So, we must use the
           * concretization of the op2.
           */
          if (op2->getKind() != triton::ast::DECIMAL_NODE)
            throw std::runtime_error("triton::arch::x86::semantics::cfRor_s(): op2 must be a DecimalNode node.");

          triton::ast::AbstractNode* node;
          if (reinterpret_cast<triton::ast::DecimalNode*>(op2)->getValue() != 0) {
            node = triton::ast::extract(0, 0,
              triton::ast::bvlshr(
                triton::ast::extract(high, low, triton::ast::reference(parent->getId())),
                triton::ast::bvsub(
                  triton::ast::bv(bvSize, bvSize),
                  triton::ast::bv(1, bvSize)
                )
              )
            );
          }
          else {
            node = triton::api.buildSymbolicOperand(inst, cf);
          }

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
        }


        void cfSar_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, triton::ast::AbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto cf     = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

          /*
           * Create the semantic.
           * if op2 != 0:
           *   if op2 > bvSize:
           *     cf.id = ((op1 >> (bvSize - 1)) & 1)
           *   else:
           *     cf.id = ((op1 >> (op2 - 1)) & 1)
           */
          auto node = triton::ast::ite(
                        triton::ast::equal(op2, triton::ast::bv(0, bvSize)),
                        triton::api.buildSymbolicOperand(inst, cf),
                        triton::ast::ite(
                          triton::ast::bvugt(op2, triton::ast::bv(bvSize, bvSize)),
                          triton::ast::extract(0, 0, triton::ast::bvlshr(op1, triton::ast::bvsub(triton::ast::bv(bvSize, bvSize), triton::ast::bv(1, bvSize)))),
                          triton::ast::extract(0, 0, triton::ast::bvlshr(op1, triton::ast::bvsub(op2, triton::ast::bv(1, bvSize))))
                        )
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
        }


        void cfShl_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, triton::ast::AbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto cf     = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

          /*
           * Create the semantic.
           * cf = (op1 >> ((bvSize - op2) & 1) if op2 != 0
           */
          auto node = triton::ast::ite(
                        triton::ast::equal(op2, triton::ast::bv(0, bvSize)),
                        triton::api.buildSymbolicOperand(inst, cf),
                        triton::ast::extract(0, 0,
                          triton::ast::bvlshr(
                            op1,
                            triton::ast::bvsub(
                              triton::ast::bv(bvSize, bvSize),
                              op2
                            )
                          )
                        )
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
        }


        void cfShr_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, triton::ast::AbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto cf     = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

          /*
           * Create the semantic.
           * cf = ((op1 >> (op2 - 1)) & 1) if op2 != 0
           */
          auto node = triton::ast::ite(
                        triton::ast::equal(op2, triton::ast::bv(0, bvSize)),
                        triton::api.buildSymbolicOperand(inst, cf),
                        triton::ast::extract(0, 0,
                          triton::ast::bvlshr(
                            op1,
                            triton::ast::bvsub(
                              op2,
                              triton::ast::bv(1, bvSize))
                          )
                        )
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
        }


        void cfSub_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, triton::ast::AbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();

          /*
           * Create the semantic.
           * cf = extract(bvSize, bvSize (((op1 ^ op2 ^ res) ^ ((op1 ^ res) & (op1 ^ op2)))))
           */
          auto node = triton::ast::extract(high, high,
                        triton::ast::bvxor(
                          triton::ast::bvxor(op1, triton::ast::bvxor(op2, triton::ast::extract(high, low, triton::ast::reference(parent->getId())))),
                          triton::ast::bvand(
                            triton::ast::bvxor(op1, triton::ast::extract(high, low, triton::ast::reference(parent->getId()))),
                            triton::ast::bvxor(op1, op2)
                          )
                        )
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
        }


        void ofAdd_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, triton::ast::AbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();

          /*
           * Create the semantic.
           * of = high:bool((op1 ^ ~op2) & (op1 ^ regDst))
           */
          auto node = triton::ast::extract(high, high,
                        triton::ast::bvand(
                          triton::ast::bvxor(op1, triton::ast::bvnot(op2)),
                          triton::ast::bvxor(op1, triton::ast::extract(high, low, triton::ast::reference(parent->getId())))
                        )
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_OF, parent->isTainted);
        }


        void ofImul_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, triton::ast::AbstractNode* res, bool vol) {
          /*
           * Create the semantic.
           * of = 0 if sx(dst) == node else 1
           */
          auto node = triton::ast::ite(
                        triton::ast::equal(
                          triton::ast::sx(dst.getBitSize(), op1),
                          res
                        ),
                        triton::ast::bv(0, 1),
                        triton::ast::bv(1, 1)
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_OF, parent->isTainted);
        }


        void ofMul_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, bool vol) {
          auto bvSize = dst.getBitSize();

          /*
           * Create the semantic.
           * of = 0 if up == 0 else 1
           */
          auto node = triton::ast::ite(
                        triton::ast::equal(
                          op1,
                          triton::ast::bv(0, bvSize)
                        ),
                        triton::ast::bv(0, 1),
                        triton::ast::bv(1, 1)
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_OF, parent->isTainted);
        }


        void ofNeg_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();

          /*
           * Create the semantic.
           * of = (res & op1) >> (bvSize - 1) & 1
           */
          auto node = triton::ast::extract(0, 0,
                        triton::ast::bvshl(
                          triton::ast::bvand(triton::ast::extract(high, low, triton::ast::reference(parent->getId())), op1),
                          triton::ast::bvsub(triton::ast::bv(bvSize, bvSize), triton::ast::bv(1, bvSize))
                        )
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_OF, parent->isTainted);
        }


        void ofRol_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();
          auto cf     = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
          auto of     = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

          /*
           * Create the semantic.
           * of = ((cf ^ (res >> (bvsize - 1))) & 1) if op2 == 1 else undefined
           * As the second operand can't be symbolized, there is
           * no symbolic expression available. So, we must use the
           * concretization of the op2.
           */
          if (op2->getKind() != triton::ast::DECIMAL_NODE)
            throw std::runtime_error("triton::arch::x86::semantics::ofRol_s(): op2 must be a DecimalNode node.");

          triton::ast::AbstractNode* node;
          if (reinterpret_cast<triton::ast::DecimalNode*>(op2)->getValue() == 1) {
            node = triton::ast::extract(0, 0,
                      triton::ast::bvxor(
                        triton::ast::zx(bvSize-1, triton::api.buildSymbolicOperand(inst, cf)),
                        triton::ast::bvshl(
                          triton::ast::extract(high, low, triton::ast::reference(parent->getId())),
                          triton::ast::bvsub(triton::ast::bv(bvSize, bvSize), triton::ast::bv(1, bvSize))
                        )
                      )
                    );
          }
          else {
            node = triton::api.buildSymbolicOperand(inst, of);
          }

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_OF, parent->isTainted);
        }


        void ofRor_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();
          auto of     = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

          /*
           * Create the semantic.
           * of = (((res >> (bvSize - 1)) ^ (res >> (bvSize - 2))) & 1) if op2 == 1 else undefined
           * As the second operand can't be symbolized, there is
           * no symbolic expression available. So, we must use the
           * concretization of the op2.
           */
          if (op2->getKind() != triton::ast::DECIMAL_NODE)
            throw std::runtime_error("triton::arch::x86::semantics::ofRor_s(): op2 must be a DecimalNode node.");

          triton::ast::AbstractNode* node;
          if (reinterpret_cast<triton::ast::DecimalNode *>(op2)->getValue() == 1) {
            node = triton::ast::extract(0, 0,
                     triton::ast::bvxor(
                       triton::ast::bvshl(
                         triton::ast::extract(high, low, triton::ast::reference(parent->getId())),
                         triton::ast::bvsub(triton::ast::bv(bvSize, bvSize), triton::ast::bv(1, bvSize))
                       ),
                       triton::ast::bvshl(
                         triton::ast::extract(high, low, triton::ast::reference(parent->getId())),
                         triton::ast::bvsub(triton::ast::bv(bvSize, bvSize), triton::ast::bv(2, bvSize))
                       )
                     )
                   );
          }
          else {
            node = triton::api.buildSymbolicOperand(inst, of);
          }

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_OF, parent->isTainted);
        }


        void ofSar_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto of     = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

          /*
           * Create the semantic.
           * of = 0 if op2 == 1
           */
          auto node = triton::ast::ite(
                        triton::ast::equal(
                          op2,
                          triton::ast::bv(1, bvSize)),
                        triton::ast::bv(0, 1),
                        triton::api.buildSymbolicOperand(inst, of)
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_OF, parent->isTainted);
        }


        void ofShl_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, triton::ast::AbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto of     = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

          /*
           * Create the semantic.
           * of = bit_cast((op1 >> (bvSize - 1)) ^ (op1 >> (bvSize - 2)), int1(1)); if op2 == 1
           */
          auto node = triton::ast::ite(
                        triton::ast::equal(
                          op2,
                          triton::ast::bv(1, bvSize)),
                        triton::ast::extract(0, 0,
                          triton::ast::bvxor(
                            triton::ast::bvlshr(op1, triton::ast::bvsub(triton::ast::bv(bvSize, bvSize), triton::ast::bv(1, bvSize))),
                            triton::ast::bvlshr(op1, triton::ast::bvsub(triton::ast::bv(bvSize, bvSize), triton::ast::bv(2, bvSize)))
                          )
                        ),
                        triton::api.buildSymbolicOperand(inst, of)
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_OF, parent->isTainted);
        }


        void ofShr_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, triton::ast::AbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto of     = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

          /*
           * Create the semantic.
           * of = ((op1 >> (bvSize - 1)) & 1) if op2 == 1
           */
          auto node = triton::ast::ite(
                        triton::ast::equal(
                          op2,
                          triton::ast::bv(1, bvSize)),
                        triton::ast::extract(0, 0, triton::ast::bvlshr(op1, triton::ast::bvsub(triton::ast::bv(bvSize, bvSize), triton::ast::bv(1, bvSize)))),
                        triton::api.buildSymbolicOperand(inst, of)
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_OF, parent->isTainted);
        }


        void ofSub_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op1, triton::ast::AbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();

          /*
           * Create the semantic.
           * of = high:bool((op1 ^ op2) & (op1 ^ regDst))
           */
          auto node = triton::ast::extract(high, high,
                        triton::ast::bvand(
                          triton::ast::bvxor(op1, op2),
                          triton::ast::bvxor(op1, triton::ast::extract(high, low, triton::ast::reference(parent->getId())))
                        )
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_OF, parent->isTainted);
        }


        void pf_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, bool vol) {
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? BYTE_SIZE_BIT-1 : !low ? BYTE_SIZE_BIT-1 : WORD_SIZE_BIT-1;

          /*
           * Create the semantics.
           *
           * pf is set to one if there is an even number of bit set to 1 in the least
           * significant byte of the result.
           */
          auto node = triton::ast::bv(1, 1);
          for (triton::uint32 counter = 0; counter <= BYTE_SIZE_BIT-1; counter++) {
            node = triton::ast::bvxor(
                     node,
                     triton::ast::extract(0, 0,
                       triton::ast::bvlshr(
                         triton::ast::extract(high, low, triton::ast::reference(parent->getId())),
                         triton::ast::bv(counter, BYTE_SIZE_BIT)
                       )
                    )
                  );
          }

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_PF, "Parity flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_PF, parent->isTainted);
        }


        void pfShl_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? BYTE_SIZE_BIT-1 : !low ? BYTE_SIZE_BIT-1 : WORD_SIZE_BIT-1;
          auto pf     = triton::arch::OperandWrapper(TRITON_X86_REG_PF);

          /*
           * Create the semantics.
           * pf if op2 != 0
           */
          auto node1 = triton::ast::bv(1, 1);
          for (triton::uint32 counter = 0; counter <= BYTE_SIZE_BIT-1; counter++) {
            node1 = triton::ast::bvxor(
                     node1,
                     triton::ast::extract(0, 0,
                       triton::ast::bvlshr(
                         triton::ast::extract(high, low, triton::ast::reference(parent->getId())),
                         triton::ast::bv(counter, BYTE_SIZE_BIT)
                       )
                    )
                  );
          }

          auto node2 = triton::ast::ite(
                         triton::ast::equal(op2, triton::ast::bv(0, bvSize)),
                         triton::api.buildSymbolicOperand(inst, pf),
                         node1
                       );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node2, TRITON_X86_REG_PF, "Parity flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_PF, parent->isTainted);
        }


        void sf_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, bool vol) {
          auto bvSize = dst.getBitSize();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();

          /*
           * Create the semantic.
           * sf = high:bool(regDst)
           */
          auto node = triton::ast::extract(high, high, triton::ast::reference(parent->getId()));

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_SF, "Sign flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_SF, parent->isTainted);
        }


        void sfShl_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();
          auto sf     = triton::arch::OperandWrapper(TRITON_X86_REG_SF);

          /*
           * Create the semantic.
           * sf if op2 != 0
           */
          auto node = triton::ast::ite(
                        triton::ast::equal(op2, triton::ast::bv(0, bvSize)),
                        triton::api.buildSymbolicOperand(inst, sf),
                        triton::ast::extract(high, high, triton::ast::reference(parent->getId()))
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_SF, "Sign flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_SF, parent->isTainted);
        }


        void zf_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();

          /*
           * Create the semantic.
           * zf = 0 == regDst
           */
          auto node = triton::ast::ite(
                        triton::ast::equal(
                          triton::ast::extract(high, low, triton::ast::reference(parent->getId())),
                          triton::ast::bv(0, bvSize)
                        ),
                        triton::ast::bv(1, 1),
                        triton::ast::bv(0, 1)
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_ZF, "Zero flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_ZF, parent->isTainted);
        }


        void zfBsf_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& src, triton::ast::AbstractNode* op2, bool vol) {
          auto bvSize = src.getBitSize();

          /*
           * Create the semantic.
           * zf = 1 if op2 == 0 else 0
           */
          auto node = triton::ast::ite(
                        triton::ast::equal(op2, triton::ast::bv(0, bvSize)),
                        triton::ast::bvtrue(),
                        triton::ast::bvfalse()
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_ZF, "Zero flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_ZF, parent->isTainted);
        }


        void zfShl_s(triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* parent, triton::arch::OperandWrapper& dst, triton::ast::AbstractNode* op2, bool vol) {
          auto bvSize = dst.getBitSize();
          auto low    = vol ? 0 : dst.getAbstractLow();
          auto high   = vol ? bvSize-1 : dst.getAbstractHigh();
          auto zf     = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          /*
           * Create the semantic.
           * zf if op2 != 0
           */
          auto node = triton::ast::ite(
                        triton::ast::equal(op2, triton::ast::bv(0, bvSize)),
                        triton::api.buildSymbolicOperand(inst, zf),
                        triton::ast::ite(
                          triton::ast::equal(
                            triton::ast::extract(high, low, triton::ast::reference(parent->getId())),
                            triton::ast::bv(0, bvSize)
                          ),
                          triton::ast::bv(1, 1),
                          triton::ast::bv(0, 1)
                        )
                      );

          /* Create the symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_ZF, "Zero flag");

          /* Spread the taint from the parent to the child */
          expr->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_ZF, parent->isTainted);
        }


        void adc_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];
          auto  cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, cf);

          /* Create the semantics */
          auto node = triton::ast::bvadd(triton::ast::bvadd(op1, op2), triton::ast::zx(dst.getBitSize()-1, op3));

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
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::bvadd(op1, op2);

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
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::bvand(op1, op2);

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
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::bvand(triton::ast::bvnot(op1), op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "ANDNPD operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void andnps_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::bvand(triton::ast::bvnot(op1), op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "ANDNPS operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void andpd_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::bvand(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "ANDPD operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void andps_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::bvand(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "ANDPS operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void bsf_s(triton::arch::Instruction& inst) {
          auto& dst     = inst.operands[0];
          auto& src     = inst.operands[1];
          auto  bvSize1 = dst.getBitSize();
          auto  bvSize2 = src.getBitSize();

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          triton::ast::AbstractNode* node = nullptr;
          switch (src.getSize()) {
            case BYTE_SIZE:
              node = triton::ast::ite(
                       triton::ast::equal(op2, triton::ast::bv(0, bvSize2)), /* Apply BSF only if op2 != 0 */
                       op1,
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(0, 0, op2), triton::ast::bvtrue()), triton::ast::bv(0, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(1, 1, op2), triton::ast::bvtrue()), triton::ast::bv(1, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(2, 2, op2), triton::ast::bvtrue()), triton::ast::bv(2, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(3, 3, op2), triton::ast::bvtrue()), triton::ast::bv(3, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(4, 4, op2), triton::ast::bvtrue()), triton::ast::bv(4, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(5, 5, op2), triton::ast::bvtrue()), triton::ast::bv(5, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(6, 6, op2), triton::ast::bvtrue()), triton::ast::bv(6, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(7, 7, op2), triton::ast::bvtrue()), triton::ast::bv(7, bvSize1),
                       triton::ast::bv(0, bvSize1)
                       ))))))))
                     );
              break;
            case WORD_SIZE:
              node = triton::ast::ite(
                       triton::ast::equal(op2, triton::ast::bv(0, bvSize2)), /* Apply BSF only if op2 != 0 */
                       op1,
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(0, 0, op2), triton::ast::bvtrue()), triton::ast::bv(0, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(1, 1, op2), triton::ast::bvtrue()), triton::ast::bv(1, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(2, 2, op2), triton::ast::bvtrue()), triton::ast::bv(2, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(3, 3, op2), triton::ast::bvtrue()), triton::ast::bv(3, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(4, 4, op2), triton::ast::bvtrue()), triton::ast::bv(4, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(5, 5, op2), triton::ast::bvtrue()), triton::ast::bv(5, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(6, 6, op2), triton::ast::bvtrue()), triton::ast::bv(6, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(7, 7, op2), triton::ast::bvtrue()), triton::ast::bv(7, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(8, 8, op2), triton::ast::bvtrue()), triton::ast::bv(8, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(9, 9, op2), triton::ast::bvtrue()), triton::ast::bv(9, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(10, 10, op2), triton::ast::bvtrue()), triton::ast::bv(10, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(11, 11, op2), triton::ast::bvtrue()), triton::ast::bv(11, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(12, 12, op2), triton::ast::bvtrue()), triton::ast::bv(12, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(13, 13, op2), triton::ast::bvtrue()), triton::ast::bv(13, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(14, 14, op2), triton::ast::bvtrue()), triton::ast::bv(14, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(15, 15, op2), triton::ast::bvtrue()), triton::ast::bv(15, bvSize1),
                       triton::ast::bv(0, bvSize1)
                       ))))))))))))))))
                     );
              break;
            case DWORD_SIZE:
              node = triton::ast::ite(
                       triton::ast::equal(op2, triton::ast::bv(0, bvSize2)), /* Apply BSF only if op2 != 0 */
                       op1,
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(0, 0, op2), triton::ast::bvtrue()), triton::ast::bv(0, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(1, 1, op2), triton::ast::bvtrue()), triton::ast::bv(1, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(2, 2, op2), triton::ast::bvtrue()), triton::ast::bv(2, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(3, 3, op2), triton::ast::bvtrue()), triton::ast::bv(3, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(4, 4, op2), triton::ast::bvtrue()), triton::ast::bv(4, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(5, 5, op2), triton::ast::bvtrue()), triton::ast::bv(5, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(6, 6, op2), triton::ast::bvtrue()), triton::ast::bv(6, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(7, 7, op2), triton::ast::bvtrue()), triton::ast::bv(7, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(8, 8, op2), triton::ast::bvtrue()), triton::ast::bv(8, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(9, 9, op2), triton::ast::bvtrue()), triton::ast::bv(9, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(10, 10, op2), triton::ast::bvtrue()), triton::ast::bv(10, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(11, 11, op2), triton::ast::bvtrue()), triton::ast::bv(11, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(12, 12, op2), triton::ast::bvtrue()), triton::ast::bv(12, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(13, 13, op2), triton::ast::bvtrue()), triton::ast::bv(13, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(14, 14, op2), triton::ast::bvtrue()), triton::ast::bv(14, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(15, 15, op2), triton::ast::bvtrue()), triton::ast::bv(15, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(16, 16, op2), triton::ast::bvtrue()), triton::ast::bv(16, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(17, 17, op2), triton::ast::bvtrue()), triton::ast::bv(17, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(18, 18, op2), triton::ast::bvtrue()), triton::ast::bv(18, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(19, 19, op2), triton::ast::bvtrue()), triton::ast::bv(19, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(20, 20, op2), triton::ast::bvtrue()), triton::ast::bv(20, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(21, 21, op2), triton::ast::bvtrue()), triton::ast::bv(21, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(22, 22, op2), triton::ast::bvtrue()), triton::ast::bv(22, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(23, 23, op2), triton::ast::bvtrue()), triton::ast::bv(23, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(24, 24, op2), triton::ast::bvtrue()), triton::ast::bv(24, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(25, 25, op2), triton::ast::bvtrue()), triton::ast::bv(25, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(26, 26, op2), triton::ast::bvtrue()), triton::ast::bv(26, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(27, 27, op2), triton::ast::bvtrue()), triton::ast::bv(27, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(28, 28, op2), triton::ast::bvtrue()), triton::ast::bv(28, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(29, 29, op2), triton::ast::bvtrue()), triton::ast::bv(29, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(30, 30, op2), triton::ast::bvtrue()), triton::ast::bv(30, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(31, 31, op2), triton::ast::bvtrue()), triton::ast::bv(31, bvSize1),
                       triton::ast::bv(0, bvSize1)
                       ))))))))))))))))))))))))))))))))
                     );
              break;
            case QWORD_SIZE:
              node = triton::ast::ite(
                       triton::ast::equal(op2, triton::ast::bv(0, bvSize2)), /* Apply BSF only if op2 != 0 */
                       op1,
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(0, 0, op2), triton::ast::bvtrue()), triton::ast::bv(0, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(1, 1, op2), triton::ast::bvtrue()), triton::ast::bv(1, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(2, 2, op2), triton::ast::bvtrue()), triton::ast::bv(2, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(3, 3, op2), triton::ast::bvtrue()), triton::ast::bv(3, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(4, 4, op2), triton::ast::bvtrue()), triton::ast::bv(4, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(5, 5, op2), triton::ast::bvtrue()), triton::ast::bv(5, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(6, 6, op2), triton::ast::bvtrue()), triton::ast::bv(6, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(7, 7, op2), triton::ast::bvtrue()), triton::ast::bv(7, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(8, 8, op2), triton::ast::bvtrue()), triton::ast::bv(8, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(9, 9, op2), triton::ast::bvtrue()), triton::ast::bv(9, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(10, 10, op2), triton::ast::bvtrue()), triton::ast::bv(10, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(11, 11, op2), triton::ast::bvtrue()), triton::ast::bv(11, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(12, 12, op2), triton::ast::bvtrue()), triton::ast::bv(12, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(13, 13, op2), triton::ast::bvtrue()), triton::ast::bv(13, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(14, 14, op2), triton::ast::bvtrue()), triton::ast::bv(14, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(15, 15, op2), triton::ast::bvtrue()), triton::ast::bv(15, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(16, 16, op2), triton::ast::bvtrue()), triton::ast::bv(16, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(17, 17, op2), triton::ast::bvtrue()), triton::ast::bv(17, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(18, 18, op2), triton::ast::bvtrue()), triton::ast::bv(18, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(19, 19, op2), triton::ast::bvtrue()), triton::ast::bv(19, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(20, 20, op2), triton::ast::bvtrue()), triton::ast::bv(20, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(21, 21, op2), triton::ast::bvtrue()), triton::ast::bv(21, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(22, 22, op2), triton::ast::bvtrue()), triton::ast::bv(22, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(23, 23, op2), triton::ast::bvtrue()), triton::ast::bv(23, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(24, 24, op2), triton::ast::bvtrue()), triton::ast::bv(24, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(25, 25, op2), triton::ast::bvtrue()), triton::ast::bv(25, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(26, 26, op2), triton::ast::bvtrue()), triton::ast::bv(26, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(27, 27, op2), triton::ast::bvtrue()), triton::ast::bv(27, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(28, 28, op2), triton::ast::bvtrue()), triton::ast::bv(28, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(29, 29, op2), triton::ast::bvtrue()), triton::ast::bv(29, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(30, 30, op2), triton::ast::bvtrue()), triton::ast::bv(30, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(31, 31, op2), triton::ast::bvtrue()), triton::ast::bv(31, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(32, 32, op2), triton::ast::bvtrue()), triton::ast::bv(32, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(33, 33, op2), triton::ast::bvtrue()), triton::ast::bv(33, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(34, 34, op2), triton::ast::bvtrue()), triton::ast::bv(34, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(35, 35, op2), triton::ast::bvtrue()), triton::ast::bv(35, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(36, 36, op2), triton::ast::bvtrue()), triton::ast::bv(36, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(37, 37, op2), triton::ast::bvtrue()), triton::ast::bv(37, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(38, 38, op2), triton::ast::bvtrue()), triton::ast::bv(38, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(39, 39, op2), triton::ast::bvtrue()), triton::ast::bv(39, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(40, 40, op2), triton::ast::bvtrue()), triton::ast::bv(40, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(41, 41, op2), triton::ast::bvtrue()), triton::ast::bv(41, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(42, 42, op2), triton::ast::bvtrue()), triton::ast::bv(42, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(43, 43, op2), triton::ast::bvtrue()), triton::ast::bv(43, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(44, 44, op2), triton::ast::bvtrue()), triton::ast::bv(44, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(45, 45, op2), triton::ast::bvtrue()), triton::ast::bv(45, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(46, 46, op2), triton::ast::bvtrue()), triton::ast::bv(46, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(47, 47, op2), triton::ast::bvtrue()), triton::ast::bv(47, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(48, 48, op2), triton::ast::bvtrue()), triton::ast::bv(48, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(49, 49, op2), triton::ast::bvtrue()), triton::ast::bv(49, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(50, 50, op2), triton::ast::bvtrue()), triton::ast::bv(50, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(51, 51, op2), triton::ast::bvtrue()), triton::ast::bv(51, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(52, 52, op2), triton::ast::bvtrue()), triton::ast::bv(52, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(53, 53, op2), triton::ast::bvtrue()), triton::ast::bv(53, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(54, 54, op2), triton::ast::bvtrue()), triton::ast::bv(54, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(55, 55, op2), triton::ast::bvtrue()), triton::ast::bv(55, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(56, 56, op2), triton::ast::bvtrue()), triton::ast::bv(56, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(57, 57, op2), triton::ast::bvtrue()), triton::ast::bv(57, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(58, 58, op2), triton::ast::bvtrue()), triton::ast::bv(58, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(59, 59, op2), triton::ast::bvtrue()), triton::ast::bv(59, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(60, 60, op2), triton::ast::bvtrue()), triton::ast::bv(60, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(61, 61, op2), triton::ast::bvtrue()), triton::ast::bv(61, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(62, 62, op2), triton::ast::bvtrue()), triton::ast::bv(62, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(63, 63, op2), triton::ast::bvtrue()), triton::ast::bv(63, bvSize1),
                       triton::ast::bv(0, bvSize1)
                       ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                     );
              break;
            default:
              throw std::runtime_error("Error: triton::arch::x86::semantics::bsf_s(): Invalid operand size.");
          }

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "BSF operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::zfBsf_s(inst, expr, src, op2);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void bsr_s(triton::arch::Instruction& inst) {
          auto& dst     = inst.operands[0];
          auto& src     = inst.operands[1];
          auto  bvSize1 = dst.getBitSize();
          auto  bvSize2 = src.getBitSize();

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          triton::ast::AbstractNode* node = nullptr;
          switch (src.getSize()) {
            case BYTE_SIZE:
              node = triton::ast::ite(
                       triton::ast::equal(op2, triton::ast::bv(0, bvSize2)), /* Apply BSR only if op2 != 0 */
                       op1,
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(7, 7, op2), triton::ast::bvtrue()), triton::ast::bv(7, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(6, 6, op2), triton::ast::bvtrue()), triton::ast::bv(6, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(5, 5, op2), triton::ast::bvtrue()), triton::ast::bv(5, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(4, 4, op2), triton::ast::bvtrue()), triton::ast::bv(4, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(3, 3, op2), triton::ast::bvtrue()), triton::ast::bv(3, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(2, 2, op2), triton::ast::bvtrue()), triton::ast::bv(2, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(1, 1, op2), triton::ast::bvtrue()), triton::ast::bv(1, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(0, 0, op2), triton::ast::bvtrue()), triton::ast::bv(0, bvSize1),
                       triton::ast::bv(0, bvSize1)
                       ))))))))
                     );
              break;
            case WORD_SIZE:
              node = triton::ast::ite(
                       triton::ast::equal(op2, triton::ast::bv(0, bvSize2)), /* Apply BSR only if op2 != 0 */
                       op1,
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(15, 15, op2), triton::ast::bvtrue()), triton::ast::bv(15, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(14, 14, op2), triton::ast::bvtrue()), triton::ast::bv(14, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(13, 13, op2), triton::ast::bvtrue()), triton::ast::bv(13, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(12, 12, op2), triton::ast::bvtrue()), triton::ast::bv(12, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(11, 11, op2), triton::ast::bvtrue()), triton::ast::bv(11, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(10, 10, op2), triton::ast::bvtrue()), triton::ast::bv(10, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(9, 9, op2), triton::ast::bvtrue()), triton::ast::bv(9, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(8, 8, op2), triton::ast::bvtrue()), triton::ast::bv(8, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(7, 7, op2), triton::ast::bvtrue()), triton::ast::bv(7, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(6, 6, op2), triton::ast::bvtrue()), triton::ast::bv(6, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(5, 5, op2), triton::ast::bvtrue()), triton::ast::bv(5, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(4, 4, op2), triton::ast::bvtrue()), triton::ast::bv(4, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(3, 3, op2), triton::ast::bvtrue()), triton::ast::bv(3, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(2, 2, op2), triton::ast::bvtrue()), triton::ast::bv(2, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(1, 1, op2), triton::ast::bvtrue()), triton::ast::bv(1, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(0, 0, op2), triton::ast::bvtrue()), triton::ast::bv(0, bvSize1),
                       triton::ast::bv(0, bvSize1)
                       ))))))))))))))))
                     );
              break;
            case DWORD_SIZE:
              node = triton::ast::ite(
                       triton::ast::equal(op2, triton::ast::bv(0, bvSize2)), /* Apply BSR only if op2 != 0 */
                       op1,
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(31, 31, op2), triton::ast::bvtrue()), triton::ast::bv(31, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(30, 30, op2), triton::ast::bvtrue()), triton::ast::bv(30, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(29, 29, op2), triton::ast::bvtrue()), triton::ast::bv(29, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(28, 28, op2), triton::ast::bvtrue()), triton::ast::bv(28, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(27, 27, op2), triton::ast::bvtrue()), triton::ast::bv(27, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(26, 26, op2), triton::ast::bvtrue()), triton::ast::bv(26, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(25, 25, op2), triton::ast::bvtrue()), triton::ast::bv(25, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(24, 24, op2), triton::ast::bvtrue()), triton::ast::bv(24, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(23, 23, op2), triton::ast::bvtrue()), triton::ast::bv(23, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(22, 22, op2), triton::ast::bvtrue()), triton::ast::bv(22, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(21, 21, op2), triton::ast::bvtrue()), triton::ast::bv(21, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(20, 20, op2), triton::ast::bvtrue()), triton::ast::bv(20, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(19, 19, op2), triton::ast::bvtrue()), triton::ast::bv(19, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(18, 18, op2), triton::ast::bvtrue()), triton::ast::bv(18, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(17, 17, op2), triton::ast::bvtrue()), triton::ast::bv(17, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(16, 16, op2), triton::ast::bvtrue()), triton::ast::bv(16, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(15, 15, op2), triton::ast::bvtrue()), triton::ast::bv(15, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(14, 14, op2), triton::ast::bvtrue()), triton::ast::bv(14, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(13, 13, op2), triton::ast::bvtrue()), triton::ast::bv(13, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(12, 12, op2), triton::ast::bvtrue()), triton::ast::bv(12, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(11, 11, op2), triton::ast::bvtrue()), triton::ast::bv(11, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(10, 10, op2), triton::ast::bvtrue()), triton::ast::bv(10, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(9, 9, op2), triton::ast::bvtrue()), triton::ast::bv(9, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(8, 8, op2), triton::ast::bvtrue()), triton::ast::bv(8, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(7, 7, op2), triton::ast::bvtrue()), triton::ast::bv(7, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(6, 6, op2), triton::ast::bvtrue()), triton::ast::bv(6, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(5, 5, op2), triton::ast::bvtrue()), triton::ast::bv(5, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(4, 4, op2), triton::ast::bvtrue()), triton::ast::bv(4, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(3, 3, op2), triton::ast::bvtrue()), triton::ast::bv(3, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(2, 2, op2), triton::ast::bvtrue()), triton::ast::bv(2, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(1, 1, op2), triton::ast::bvtrue()), triton::ast::bv(1, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(0, 0, op2), triton::ast::bvtrue()), triton::ast::bv(0, bvSize1),
                       triton::ast::bv(0, bvSize1)
                       ))))))))))))))))))))))))))))))))
                     );
              break;
            case QWORD_SIZE:
              node = triton::ast::ite(
                       triton::ast::equal(op2, triton::ast::bv(0, bvSize2)), /* Apply BSR only if op2 != 0 */
                       op1,
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(63, 63, op2), triton::ast::bvtrue()), triton::ast::bv(63, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(62, 62, op2), triton::ast::bvtrue()), triton::ast::bv(62, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(61, 61, op2), triton::ast::bvtrue()), triton::ast::bv(61, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(60, 60, op2), triton::ast::bvtrue()), triton::ast::bv(60, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(59, 59, op2), triton::ast::bvtrue()), triton::ast::bv(59, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(58, 58, op2), triton::ast::bvtrue()), triton::ast::bv(58, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(57, 57, op2), triton::ast::bvtrue()), triton::ast::bv(57, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(56, 56, op2), triton::ast::bvtrue()), triton::ast::bv(56, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(55, 55, op2), triton::ast::bvtrue()), triton::ast::bv(55, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(54, 54, op2), triton::ast::bvtrue()), triton::ast::bv(54, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(53, 53, op2), triton::ast::bvtrue()), triton::ast::bv(53, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(52, 52, op2), triton::ast::bvtrue()), triton::ast::bv(52, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(51, 51, op2), triton::ast::bvtrue()), triton::ast::bv(51, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(50, 50, op2), triton::ast::bvtrue()), triton::ast::bv(50, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(49, 49, op2), triton::ast::bvtrue()), triton::ast::bv(49, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(48, 48, op2), triton::ast::bvtrue()), triton::ast::bv(48, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(47, 47, op2), triton::ast::bvtrue()), triton::ast::bv(47, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(46, 46, op2), triton::ast::bvtrue()), triton::ast::bv(46, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(45, 45, op2), triton::ast::bvtrue()), triton::ast::bv(45, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(44, 44, op2), triton::ast::bvtrue()), triton::ast::bv(44, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(43, 43, op2), triton::ast::bvtrue()), triton::ast::bv(43, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(42, 42, op2), triton::ast::bvtrue()), triton::ast::bv(42, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(41, 41, op2), triton::ast::bvtrue()), triton::ast::bv(41, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(40, 40, op2), triton::ast::bvtrue()), triton::ast::bv(40, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(39, 39, op2), triton::ast::bvtrue()), triton::ast::bv(39, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(38, 38, op2), triton::ast::bvtrue()), triton::ast::bv(38, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(37, 37, op2), triton::ast::bvtrue()), triton::ast::bv(37, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(36, 36, op2), triton::ast::bvtrue()), triton::ast::bv(36, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(35, 35, op2), triton::ast::bvtrue()), triton::ast::bv(35, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(34, 34, op2), triton::ast::bvtrue()), triton::ast::bv(34, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(33, 33, op2), triton::ast::bvtrue()), triton::ast::bv(33, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(32, 32, op2), triton::ast::bvtrue()), triton::ast::bv(32, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(31, 31, op2), triton::ast::bvtrue()), triton::ast::bv(31, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(30, 30, op2), triton::ast::bvtrue()), triton::ast::bv(30, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(29, 29, op2), triton::ast::bvtrue()), triton::ast::bv(29, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(28, 28, op2), triton::ast::bvtrue()), triton::ast::bv(28, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(27, 27, op2), triton::ast::bvtrue()), triton::ast::bv(27, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(26, 26, op2), triton::ast::bvtrue()), triton::ast::bv(26, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(25, 25, op2), triton::ast::bvtrue()), triton::ast::bv(25, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(24, 24, op2), triton::ast::bvtrue()), triton::ast::bv(24, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(23, 23, op2), triton::ast::bvtrue()), triton::ast::bv(23, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(22, 22, op2), triton::ast::bvtrue()), triton::ast::bv(22, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(21, 21, op2), triton::ast::bvtrue()), triton::ast::bv(21, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(20, 20, op2), triton::ast::bvtrue()), triton::ast::bv(20, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(19, 19, op2), triton::ast::bvtrue()), triton::ast::bv(19, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(18, 18, op2), triton::ast::bvtrue()), triton::ast::bv(18, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(17, 17, op2), triton::ast::bvtrue()), triton::ast::bv(17, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(16, 16, op2), triton::ast::bvtrue()), triton::ast::bv(16, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(15, 15, op2), triton::ast::bvtrue()), triton::ast::bv(15, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(14, 14, op2), triton::ast::bvtrue()), triton::ast::bv(14, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(13, 13, op2), triton::ast::bvtrue()), triton::ast::bv(13, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(12, 12, op2), triton::ast::bvtrue()), triton::ast::bv(12, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(11, 11, op2), triton::ast::bvtrue()), triton::ast::bv(11, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(10, 10, op2), triton::ast::bvtrue()), triton::ast::bv(10, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(9, 9, op2), triton::ast::bvtrue()), triton::ast::bv(9, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(8, 8, op2), triton::ast::bvtrue()), triton::ast::bv(8, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(7, 7, op2), triton::ast::bvtrue()), triton::ast::bv(7, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(6, 6, op2), triton::ast::bvtrue()), triton::ast::bv(6, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(5, 5, op2), triton::ast::bvtrue()), triton::ast::bv(5, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(4, 4, op2), triton::ast::bvtrue()), triton::ast::bv(4, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(3, 3, op2), triton::ast::bvtrue()), triton::ast::bv(3, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(2, 2, op2), triton::ast::bvtrue()), triton::ast::bv(2, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(1, 1, op2), triton::ast::bvtrue()), triton::ast::bv(1, bvSize1),
                       triton::ast::ite(triton::ast::equal(triton::ast::extract(0, 0, op2), triton::ast::bvtrue()), triton::ast::bv(0, bvSize1),
                       triton::ast::bv(0, bvSize1)
                       ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                     );
              break;
            default:
              throw std::runtime_error("Error: triton::arch::x86::semantics::bsr_s(): Invalid operand size.");
          }

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "BSR operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::zfBsf_s(inst, expr, src, op2); /* same as bsf */

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void bswap_s(triton::arch::Instruction& inst) {
          auto& src = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode *> bytes;
          switch (src.getSize()) {
            case QWORD_SIZE:
              bytes.push_front(triton::ast::extract(63, 56, op1));
              bytes.push_front(triton::ast::extract(55, 48, op1));
              bytes.push_front(triton::ast::extract(47, 40, op1));
              bytes.push_front(triton::ast::extract(39, 32, op1));
            case DWORD_SIZE:
              bytes.push_front(triton::ast::extract(31, 24, op1));
              bytes.push_front(triton::ast::extract(23, 16, op1));
            case WORD_SIZE:
              bytes.push_front(triton::ast::extract(15, 8, op1));
              bytes.push_front(triton::ast::extract(7,  0, op1));
              break;
            default:
              throw std::runtime_error("Error: triton::arch::x86::semantics::bswap_s(): Invalid operand size.");
          }

          auto node = triton::ast::concat(bytes);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, src, "BSWAP operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(src, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void bt_s(triton::arch::Instruction& inst) {
          auto  dst  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
          auto& src1 = inst.operands[0];
          auto& src2 = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src1);
          auto op2 = triton::api.buildSymbolicOperand(inst, src2);

          /* Create the semantics */
          auto node = triton::ast::extract(0, 0,
                        triton::ast::bvlshr(
                          op1,
                          triton::ast::bvsmod(
                            op2,
                            triton::ast::bv(src1.getBitSize(), src1.getBitSize())
                          )
                        )
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "BT operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src1);
          expr->isTainted = triton::api.taintUnion(dst, src2);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void btc_s(triton::arch::Instruction& inst) {
          auto  dst1 = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
          auto& dst2 = inst.operands[0];
          auto& src1 = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst2);
          auto op2 = triton::api.buildSymbolicOperand(inst, src1);

          /* Create the semantics */
          auto node1 = triton::ast::extract(0, 0,
                         triton::ast::bvlshr(
                           op1,
                           triton::ast::bvsmod(
                             op2,
                             triton::ast::bv(dst2.getBitSize(), dst2.getBitSize())
                           )
                         )
                       );
          auto node2 = triton::ast::ite(
                         triton::ast::equal(node1, triton::ast::bvfalse()),
                         /* BTS */
                         triton::ast::bvor(
                           op1,
                           triton::ast::bvshl(
                             triton::ast::bv(1, dst2.getBitSize()),
                             triton::ast::bvsmod(
                               op2,
                               triton::ast::bv(dst2.getBitSize(), dst2.getBitSize())
                             )
                           )
                         ),
                         /* BTR */
                         triton::ast::bvand(
                           op1,
                           triton::ast::bvsub(
                             op1,
                             triton::ast::bvshl(
                               triton::ast::bv(1, dst2.getBitSize()),
                               triton::ast::bvsmod(
                                 op2,
                                 triton::ast::bv(dst2.getBitSize(), dst2.getBitSize())
                               )
                             )
                           )
                         )
                       );

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicFlagExpression(inst, node1, TRITON_X86_REG_CF, "BTC carry operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, dst2, "BTC complement operation");

          /* Spread taint */
          expr1->isTainted = triton::api.taintUnion(dst1, dst2);
          expr1->isTainted = triton::api.taintUnion(dst1, src1);
          expr2->isTainted = triton::api.taintUnion(dst2, dst1);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void btr_s(triton::arch::Instruction& inst) {
          auto  dst1 = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
          auto& dst2 = inst.operands[0];
          auto& src1 = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst2);
          auto op2 = triton::api.buildSymbolicOperand(inst, src1);

          /* Create the semantics */
          auto node1 = triton::ast::extract(0, 0,
                         triton::ast::bvlshr(
                           op1,
                           triton::ast::bvsmod(
                             op2,
                             triton::ast::bv(dst2.getBitSize(), dst2.getBitSize())
                           )
                         )
                       );
          auto node2 = triton::ast::ite(
                         triton::ast::equal(node1, triton::ast::bvfalse()),
                         op1,
                         triton::ast::bvand(
                           op1,
                           triton::ast::bvsub(
                             op1,
                             triton::ast::bvshl(
                               triton::ast::bv(1, dst2.getBitSize()),
                               triton::ast::bvsmod(
                                 op2,
                                 triton::ast::bv(dst2.getBitSize(), dst2.getBitSize())
                               )
                             )
                           )
                         )
                       );

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicFlagExpression(inst, node1, TRITON_X86_REG_CF, "BTR carry operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, dst2, "BTR reset operation");

          /* Spread taint */
          expr1->isTainted = triton::api.taintUnion(dst1, dst2);
          expr1->isTainted = triton::api.taintUnion(dst1, src1);
          expr2->isTainted = triton::api.taintUnion(dst2, dst1);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void bts_s(triton::arch::Instruction& inst) {
          auto  dst1 = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
          auto& dst2 = inst.operands[0];
          auto& src1 = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst2);
          auto op2 = triton::api.buildSymbolicOperand(inst, src1);

          /* Create the semantics */
          auto node1 = triton::ast::extract(0, 0,
                         triton::ast::bvlshr(
                           op1,
                           triton::ast::bvsmod(
                             op2,
                             triton::ast::bv(dst2.getBitSize(), dst2.getBitSize())
                           )
                         )
                       );
          auto node2 = triton::ast::bvor(
                         op1,
                         triton::ast::bvshl(
                           triton::ast::bv(1, dst2.getBitSize()),
                           triton::ast::bvsmod(
                             op2,
                             triton::ast::bv(dst2.getBitSize(), dst2.getBitSize())
                           )
                         )
                       );

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicFlagExpression(inst, node1, TRITON_X86_REG_CF, "BTS carry operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, dst2, "BTS set operation");

          /* Spread taint */
          expr1->isTainted = triton::api.taintUnion(dst1, dst2);
          expr1->isTainted = triton::api.taintUnion(dst1, src1);
          expr2->isTainted = triton::api.taintUnion(dst2, dst1);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void call_s(triton::arch::Instruction& inst) {
          auto stack = TRITON_X86_REG_SP.getParent();

          /* Create the semantics - side effect */
          alignSubStack_s(inst, stack.getSize());

          auto  stackValue = triton::api.getRegisterValue(stack).convert_to<triton::__uint>();
          auto  pc         = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto  sp         = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue, stack.getSize()));
          auto& src        = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics - side effect */
          auto node1 = triton::ast::bv(inst.getNextAddress(), pc.getBitSize());

          /* Create the semantics */
          auto node2 = op1;

          /* Create the symbolic expression */
          auto expr1 = triton::api.createSymbolicExpression(inst, node1, sp, "Saved Program Counter");

          /* Create symbolic expression */
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, pc, "Program Counter");

          /* Spread taint */
          expr1->isTainted = triton::api.taintAssignmentMemoryImmediate(sp.getMemory());
          expr2->isTainted = triton::api.taintAssignment(pc, src);

          /* Create the path constraint */
          triton::api.addPathConstraint(expr2);
        }


        void cbw_s(triton::arch::Instruction& inst) {
          auto dst = triton::arch::OperandWrapper(TRITON_X86_REG_AX);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);

          /* Create the semantics */
          auto node = triton::ast::sx(BYTE_SIZE_BIT, triton::ast::extract(BYTE_SIZE_BIT-1, 0, op1));

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
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);

          /* Create the semantics */
          auto node = triton::ast::sx(DWORD_SIZE_BIT, triton::ast::extract(DWORD_SIZE_BIT-1, 0, op1));

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
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);

          /* Create the semantics */
          auto node = triton::ast::bvnot(op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicFlagExpression(inst, node, dst.getRegister(), "CMC operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cmova_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];
          auto  cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
          auto  zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, cf);
          auto op4 = triton::api.buildSymbolicOperand(inst, zf);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(triton::ast::bvand(triton::ast::bvnot(op3), triton::ast::bvnot(op4)), triton::ast::bvtrue()), op2, op1);

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
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];
          auto  cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, cf);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(op3, triton::ast::bvfalse()), op2, op1);

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
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];
          auto  cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, cf);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(op3, triton::ast::bvtrue()), op2, op1);

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
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];
          auto  cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
          auto  zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, cf);
          auto op4 = triton::api.buildSymbolicOperand(inst, zf);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(triton::ast::bvor(op3, op4), triton::ast::bvtrue()), op2, op1);

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
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];
          auto  zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, zf);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(op3, triton::ast::bvtrue()), op2, op1);

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
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];
          auto  sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto  of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
          auto  zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, sf);
          auto op4 = triton::api.buildSymbolicOperand(inst, of);
          auto op5 = triton::api.buildSymbolicOperand(inst, zf);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(triton::ast::bvor(triton::ast::bvxor(op3, op4), op5), triton::ast::bvfalse()), op2, op1);

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
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];
          auto  sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto  of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, sf);
          auto op4 = triton::api.buildSymbolicOperand(inst, of);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(op3, op4), op2, op1);

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
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];
          auto  sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto  of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, sf);
          auto op4 = triton::api.buildSymbolicOperand(inst, of);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(triton::ast::bvxor(op3, op4), triton::ast::bvtrue()), op2, op1);

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
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];
          auto  sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto  of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
          auto  zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, sf);
          auto op4 = triton::api.buildSymbolicOperand(inst, of);
          auto op5 = triton::api.buildSymbolicOperand(inst, zf);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(triton::ast::bvor(triton::ast::bvxor(op3, op4), op5), triton::ast::bvtrue()), op2, op1);

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
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];
          auto  zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, zf);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(op3, triton::ast::bvfalse()), op2, op1);

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
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];
          auto  of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, of);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(op3, triton::ast::bvfalse()), op2, op1);

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
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];
          auto  pf  = triton::arch::OperandWrapper(TRITON_X86_REG_PF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, pf);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(op3, triton::ast::bvfalse()), op2, op1);

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
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];
          auto  sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, sf);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(op3, triton::ast::bvfalse()), op2, op1);

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
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];
          auto  of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, of);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(op3, triton::ast::bvtrue()), op2, op1);

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
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];
          auto  pf  = triton::arch::OperandWrapper(TRITON_X86_REG_PF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, pf);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(op3, triton::ast::bvtrue()), op2, op1);

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
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];
          auto  sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, sf);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(op3, triton::ast::bvtrue()), op2, op1);

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
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::ast::sx(dst.getBitSize() - src.getBitSize(), triton::api.buildSymbolicOperand(inst, src));

          /* Create the semantics */
          auto node = triton::ast::bvsub(op1, op2);

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


        void cmpsb_s(triton::arch::Instruction& inst) {
          auto& dst    = inst.operands[0];
          auto& src    = inst.operands[1];
          auto  index1 = triton::arch::OperandWrapper(TRITON_X86_REG_SI.getParent());
          auto  index2 = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
          auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

          /* If the REP prefix is defined, convert REP into REPE */
          if (inst.getPrefix() == triton::arch::x86::ID_PREFIX_REP)
            inst.setPrefix(triton::arch::x86::ID_PREFIX_REPE);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, index1);
          auto op4 = triton::api.buildSymbolicOperand(inst, index2);
          auto op5 = triton::api.buildSymbolicOperand(inst, df);

          /* Create the semantics */
          auto node1 = triton::ast::bvsub(op1, op2);
          auto node2 = triton::ast::ite(
                         triton::ast::equal(op5, triton::ast::bvfalse()),
                         triton::ast::bvadd(op3, triton::ast::bv(BYTE_SIZE, index1.getBitSize())),
                         triton::ast::bvsub(op3, triton::ast::bv(BYTE_SIZE, index1.getBitSize()))
                       );
          auto node3 = triton::ast::ite(
                         triton::ast::equal(op5, triton::ast::bvfalse()),
                         triton::ast::bvadd(op4, triton::ast::bv(BYTE_SIZE, index2.getBitSize())),
                         triton::ast::bvsub(op4, triton::ast::bv(BYTE_SIZE, index2.getBitSize()))
                       );

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicVolatileExpression(inst, node1, "CMPSB operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, index1, "Index (SI) operation");
          auto expr3 = triton::api.createSymbolicExpression(inst, node3, index2, "Index (DI) operation");

          /* Spread taint */
          expr1->isTainted = triton::api.isTainted(dst) | triton::api.isTainted(src);
          expr2->isTainted = triton::api.taintUnion(index1, index1);
          expr3->isTainted = triton::api.taintUnion(index2, index2);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::af_s(inst, expr1, dst, op1, op2, true);
          triton::arch::x86::semantics::cfSub_s(inst, expr1, dst, op1, op2, true);
          triton::arch::x86::semantics::ofSub_s(inst, expr1, dst, op1, op2, true);
          triton::arch::x86::semantics::pf_s(inst, expr1, dst, true);
          triton::arch::x86::semantics::sf_s(inst, expr1, dst, true);
          triton::arch::x86::semantics::zf_s(inst, expr1, dst, true);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cmpsd_s(triton::arch::Instruction& inst) {
          auto& dst    = inst.operands[0];
          auto& src    = inst.operands[1];
          auto  index1 = triton::arch::OperandWrapper(TRITON_X86_REG_SI.getParent());
          auto  index2 = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
          auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

          /* If the REP prefix is defined, convert REP into REPE */
          if (inst.getPrefix() == triton::arch::x86::ID_PREFIX_REP)
            inst.setPrefix(triton::arch::x86::ID_PREFIX_REPE);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, index1);
          auto op4 = triton::api.buildSymbolicOperand(inst, index2);
          auto op5 = triton::api.buildSymbolicOperand(inst, df);

          /* Create the semantics */
          auto node1 = triton::ast::bvsub(op1, op2);
          auto node2 = triton::ast::ite(
                         triton::ast::equal(op5, triton::ast::bvfalse()),
                         triton::ast::bvadd(op3, triton::ast::bv(DWORD_SIZE, index1.getBitSize())),
                         triton::ast::bvsub(op3, triton::ast::bv(DWORD_SIZE, index1.getBitSize()))
                       );
          auto node3 = triton::ast::ite(
                         triton::ast::equal(op5, triton::ast::bvfalse()),
                         triton::ast::bvadd(op4, triton::ast::bv(DWORD_SIZE, index2.getBitSize())),
                         triton::ast::bvsub(op4, triton::ast::bv(DWORD_SIZE, index2.getBitSize()))
                       );

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicVolatileExpression(inst, node1, "CMPSD operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, index1, "Index (SI) operation");
          auto expr3 = triton::api.createSymbolicExpression(inst, node3, index2, "Index (DI) operation");

          /* Spread taint */
          expr1->isTainted = triton::api.isTainted(dst) | triton::api.isTainted(src);
          expr2->isTainted = triton::api.taintUnion(index1, index1);
          expr3->isTainted = triton::api.taintUnion(index2, index2);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::af_s(inst, expr1, dst, op1, op2, true);
          triton::arch::x86::semantics::cfSub_s(inst, expr1, dst, op1, op2, true);
          triton::arch::x86::semantics::ofSub_s(inst, expr1, dst, op1, op2, true);
          triton::arch::x86::semantics::pf_s(inst, expr1, dst, true);
          triton::arch::x86::semantics::sf_s(inst, expr1, dst, true);
          triton::arch::x86::semantics::zf_s(inst, expr1, dst, true);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cmpsq_s(triton::arch::Instruction& inst) {
          auto& dst    = inst.operands[0];
          auto& src    = inst.operands[1];
          auto  index1 = triton::arch::OperandWrapper(TRITON_X86_REG_SI.getParent());
          auto  index2 = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
          auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

          /* If the REP prefix is defined, convert REP into REPE */
          if (inst.getPrefix() == triton::arch::x86::ID_PREFIX_REP)
            inst.setPrefix(triton::arch::x86::ID_PREFIX_REPE);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, index1);
          auto op4 = triton::api.buildSymbolicOperand(inst, index2);
          auto op5 = triton::api.buildSymbolicOperand(inst, df);

          /* Create the semantics */
          auto node1 = triton::ast::bvsub(op1, op2);
          auto node2 = triton::ast::ite(
                         triton::ast::equal(op5, triton::ast::bvfalse()),
                         triton::ast::bvadd(op3, triton::ast::bv(QWORD_SIZE, index1.getBitSize())),
                         triton::ast::bvsub(op3, triton::ast::bv(QWORD_SIZE, index1.getBitSize()))
                       );
          auto node3 = triton::ast::ite(
                         triton::ast::equal(op5, triton::ast::bvfalse()),
                         triton::ast::bvadd(op4, triton::ast::bv(QWORD_SIZE, index2.getBitSize())),
                         triton::ast::bvsub(op4, triton::ast::bv(QWORD_SIZE, index2.getBitSize()))
                       );

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicVolatileExpression(inst, node1, "CMPSQ operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, index1, "Index (SI) operation");
          auto expr3 = triton::api.createSymbolicExpression(inst, node3, index2, "Index (DI) operation");

          /* Spread taint */
          expr1->isTainted = triton::api.isTainted(dst) | triton::api.isTainted(src);
          expr2->isTainted = triton::api.taintUnion(index1, index1);
          expr3->isTainted = triton::api.taintUnion(index2, index2);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::af_s(inst, expr1, dst, op1, op2, true);
          triton::arch::x86::semantics::cfSub_s(inst, expr1, dst, op1, op2, true);
          triton::arch::x86::semantics::ofSub_s(inst, expr1, dst, op1, op2, true);
          triton::arch::x86::semantics::pf_s(inst, expr1, dst, true);
          triton::arch::x86::semantics::sf_s(inst, expr1, dst, true);
          triton::arch::x86::semantics::zf_s(inst, expr1, dst, true);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cmpsw_s(triton::arch::Instruction& inst) {
          auto& dst    = inst.operands[0];
          auto& src    = inst.operands[1];
          auto  index1 = triton::arch::OperandWrapper(TRITON_X86_REG_SI.getParent());
          auto  index2 = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
          auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

          /* If the REP prefix is defined, convert REP into REPE */
          if (inst.getPrefix() == triton::arch::x86::ID_PREFIX_REP)
            inst.setPrefix(triton::arch::x86::ID_PREFIX_REPE);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, index1);
          auto op4 = triton::api.buildSymbolicOperand(inst, index2);
          auto op5 = triton::api.buildSymbolicOperand(inst, df);

          /* Create the semantics */
          auto node1 = triton::ast::bvsub(op1, op2);
          auto node2 = triton::ast::ite(
                         triton::ast::equal(op5, triton::ast::bvfalse()),
                         triton::ast::bvadd(op3, triton::ast::bv(WORD_SIZE, index1.getBitSize())),
                         triton::ast::bvsub(op3, triton::ast::bv(WORD_SIZE, index1.getBitSize()))
                       );
          auto node3 = triton::ast::ite(
                         triton::ast::equal(op5, triton::ast::bvfalse()),
                         triton::ast::bvadd(op4, triton::ast::bv(WORD_SIZE, index2.getBitSize())),
                         triton::ast::bvsub(op4, triton::ast::bv(WORD_SIZE, index2.getBitSize()))
                       );

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicVolatileExpression(inst, node1, "CMPSW operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, index1, "Index (SI) operation");
          auto expr3 = triton::api.createSymbolicExpression(inst, node3, index2, "Index (DI) operation");

          /* Spread taint */
          expr1->isTainted = triton::api.isTainted(dst) | triton::api.isTainted(src);
          expr2->isTainted = triton::api.taintUnion(index1, index1);
          expr3->isTainted = triton::api.taintUnion(index2, index2);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::af_s(inst, expr1, dst, op1, op2, true);
          triton::arch::x86::semantics::cfSub_s(inst, expr1, dst, op1, op2, true);
          triton::arch::x86::semantics::ofSub_s(inst, expr1, dst, op1, op2, true);
          triton::arch::x86::semantics::pf_s(inst, expr1, dst, true);
          triton::arch::x86::semantics::sf_s(inst, expr1, dst, true);
          triton::arch::x86::semantics::zf_s(inst, expr1, dst, true);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cmpxchg_s(triton::arch::Instruction& inst) {
          auto& src1 = inst.operands[0];
          auto& src2 = inst.operands[1];

          triton::arch::OperandWrapper accumulator(TRITON_X86_REG_AL);
          switch (src1.getSize()) {
            case WORD_SIZE:
              accumulator.setRegister(TRITON_X86_REG_AX);
              break;
            case DWORD_SIZE:
              accumulator.setRegister(TRITON_X86_REG_EAX);
              break;
            case QWORD_SIZE:
              accumulator.setRegister(TRITON_X86_REG_RAX);
              break;
          }

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, accumulator);
          auto op2 = triton::api.buildSymbolicOperand(inst, src1);
          auto op3 = triton::api.buildSymbolicOperand(inst, src2);

          /* Create the semantics */
          auto node1 = triton::ast::bvsub(op1, op2);
          auto node2 = triton::ast::ite(triton::ast::equal(op1, op2), op3, op2);
          auto node3 = triton::ast::ite(triton::ast::equal(op1, op2), op1, op2);

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


        void cmpxchg16b_s(triton::arch::Instruction& inst) {
          auto& src1 = inst.operands[0];
          auto  src2 = triton::arch::OperandWrapper(TRITON_X86_REG_RDX);
          auto  src3 = triton::arch::OperandWrapper(TRITON_X86_REG_RAX);
          auto  src4 = triton::arch::OperandWrapper(TRITON_X86_REG_RCX);
          auto  src5 = triton::arch::OperandWrapper(TRITON_X86_REG_RBX);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src1);
          auto op2 = triton::api.buildSymbolicOperand(inst, src2);
          auto op3 = triton::api.buildSymbolicOperand(inst, src3);
          auto op4 = triton::api.buildSymbolicOperand(inst, src4);
          auto op5 = triton::api.buildSymbolicOperand(inst, src5);

          /* Create the semantics */
          /* CMP8B */
          auto node1 = triton::ast::bvsub(triton::ast::concat(op2, op3), op1);
          /* Destination */
          auto node2 = triton::ast::ite(triton::ast::equal(node1, triton::ast::bv(0, DQWORD_SIZE_BIT)), triton::ast::concat(op4, op5), op1);
          /* EDX:EAX */
          auto node3 = triton::ast::ite(triton::ast::equal(node1, triton::ast::bv(0, DQWORD_SIZE_BIT)), triton::ast::concat(op2, op3), op1);

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicVolatileExpression(inst, node1, "CMP operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, src1, "XCHG16B memory operation");
          auto expr3 = triton::api.createSymbolicExpression(inst, triton::ast::extract(127, 64, node3), src2, "XCHG16B RDX operation");
          auto expr4 = triton::api.createSymbolicExpression(inst, triton::ast::extract(63, 0, node3), src3, "XCHG16B RAX operation");

          /* Spread taint */
          expr1->isTainted = triton::api.isTainted(src1) | triton::api.isTainted(src2) | triton::api.isTainted(src3);
          expr2->isTainted = triton::api.taintAssignment(src1, src2);
          expr2->isTainted = triton::api.taintUnion(src1, src3);
          expr3->isTainted = triton::api.taintAssignment(src2, src1);
          expr4->isTainted = triton::api.taintAssignment(src3, src1);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::zf_s(inst, expr1, src1, true);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cmpxchg8b_s(triton::arch::Instruction& inst) {
          auto& src1 = inst.operands[0];
          auto  src2 = triton::arch::OperandWrapper(TRITON_X86_REG_EDX);
          auto  src3 = triton::arch::OperandWrapper(TRITON_X86_REG_EAX);
          auto  src4 = triton::arch::OperandWrapper(TRITON_X86_REG_ECX);
          auto  src5 = triton::arch::OperandWrapper(TRITON_X86_REG_EBX);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src1);
          auto op2 = triton::api.buildSymbolicOperand(inst, src2);
          auto op3 = triton::api.buildSymbolicOperand(inst, src3);
          auto op4 = triton::api.buildSymbolicOperand(inst, src4);
          auto op5 = triton::api.buildSymbolicOperand(inst, src5);

          /* Create the semantics */
          /* CMP8B */
          auto node1 = triton::ast::bvsub(triton::ast::concat(op2, op3), op1);
          /* Destination */
          auto node2 = triton::ast::ite(triton::ast::equal(node1, triton::ast::bv(0, QWORD_SIZE_BIT)), triton::ast::concat(op4, op5), op1);
          /* EDX:EAX */
          auto node3 = triton::ast::ite(triton::ast::equal(node1, triton::ast::bv(0, QWORD_SIZE_BIT)), triton::ast::concat(op2, op3), op1);

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicVolatileExpression(inst, node1, "CMP operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, src1, "XCHG8B memory operation");
          auto expr3 = triton::api.createSymbolicExpression(inst, triton::ast::extract(63, 32, node3), src2, "XCHG8B EDX operation");
          auto expr4 = triton::api.createSymbolicExpression(inst, triton::ast::extract(31, 0, node3), src3, "XCHG8B EAX operation");

          /* Spread taint */
          expr1->isTainted = triton::api.isTainted(src1) | triton::api.isTainted(src2) | triton::api.isTainted(src3);
          expr2->isTainted = triton::api.taintAssignment(src1, src2);
          expr2->isTainted = triton::api.taintUnion(src1, src3);
          expr3->isTainted = triton::api.taintAssignment(src2, src1);
          expr4->isTainted = triton::api.taintAssignment(src3, src1);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::zf_s(inst, expr1, src1, true);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cpuid_s(triton::arch::Instruction& inst) {
          auto src  = triton::arch::OperandWrapper(TRITON_X86_REG_AX.getParent());
          auto dst1 = triton::arch::OperandWrapper(TRITON_X86_REG_AX.getParent());
          auto dst2 = triton::arch::OperandWrapper(TRITON_X86_REG_BX.getParent());
          auto dst3 = triton::arch::OperandWrapper(TRITON_X86_REG_CX.getParent());
          auto dst4 = triton::arch::OperandWrapper(TRITON_X86_REG_DX.getParent());

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          triton::ast::AbstractNode* node1 = nullptr;
          triton::ast::AbstractNode* node2 = nullptr;
          triton::ast::AbstractNode* node3 = nullptr;
          triton::ast::AbstractNode* node4 = nullptr;

          /* In this case, we concretize the AX option */
          switch (op1->evaluate().convert_to<triton::uint32>()) {
            case 0:
              node1 = triton::ast::bv(0x0000000d, dst1.getBitSize());
              node2 = triton::ast::bv(0x756e6547, dst2.getBitSize());
              node3 = triton::ast::bv(0x6c65746e, dst3.getBitSize());
              node4 = triton::ast::bv(0x49656e69, dst4.getBitSize());
              break;
            case 1:
              node1 = triton::ast::bv(0x000306a9, dst1.getBitSize());
              node2 = triton::ast::bv(0x02100800, dst2.getBitSize());
              node3 = triton::ast::bv(0x7fbae3ff, dst3.getBitSize());
              node4 = triton::ast::bv(0xbfebfbff, dst4.getBitSize());
              break;
            case 2:
              node1 = triton::ast::bv(0x76035a01, dst1.getBitSize());
              node2 = triton::ast::bv(0x00f0b2ff, dst2.getBitSize());
              node3 = triton::ast::bv(0x00000000, dst3.getBitSize());
              node4 = triton::ast::bv(0x00ca0000, dst4.getBitSize());
              break;
            case 3:
              node1 = triton::ast::bv(0x00000000, dst1.getBitSize());
              node2 = triton::ast::bv(0x00000000, dst2.getBitSize());
              node3 = triton::ast::bv(0x00000000, dst3.getBitSize());
              node4 = triton::ast::bv(0x00000000, dst4.getBitSize());
              break;
            case 4:
              node1 = triton::ast::bv(0x1c004121, dst1.getBitSize());
              node2 = triton::ast::bv(0x01c0003f, dst2.getBitSize());
              node3 = triton::ast::bv(0x0000003f, dst3.getBitSize());
              node4 = triton::ast::bv(0x00000000, dst4.getBitSize());
              break;
            case 5:
              node1 = triton::ast::bv(0x00000040, dst1.getBitSize());
              node2 = triton::ast::bv(0x00000040, dst2.getBitSize());
              node3 = triton::ast::bv(0x00000003, dst3.getBitSize());
              node4 = triton::ast::bv(0x00021120, dst4.getBitSize());
              break;
            case 0x80000000:
              node1 = triton::ast::bv(0x80000008, dst1.getBitSize());
              node2 = triton::ast::bv(0x00000000, dst2.getBitSize());
              node3 = triton::ast::bv(0x00000000, dst3.getBitSize());
              node4 = triton::ast::bv(0x00000000, dst4.getBitSize());
              break;
            case 0x80000001:
              node1 = triton::ast::bv(0x00000000, dst1.getBitSize());
              node2 = triton::ast::bv(0x00000000, dst2.getBitSize());
              node3 = triton::ast::bv(0x00000001, dst3.getBitSize());
              node4 = triton::ast::bv(0x28100800, dst4.getBitSize());
              break;
            case 0x80000002:
              node1 = triton::ast::bv(0x20202020, dst1.getBitSize());
              node2 = triton::ast::bv(0x49202020, dst2.getBitSize());
              node3 = triton::ast::bv(0x6c65746e, dst3.getBitSize());
              node4 = triton::ast::bv(0x20295228, dst4.getBitSize());
              break;
            case 0x80000003:
              node1 = triton::ast::bv(0x65726f43, dst1.getBitSize());
              node2 = triton::ast::bv(0x294d5428, dst2.getBitSize());
              node3 = triton::ast::bv(0x2d376920, dst3.getBitSize());
              node4 = triton::ast::bv(0x30323533, dst4.getBitSize());
              break;
            case 0x80000004:
              node1 = triton::ast::bv(0x5043204d, dst1.getBitSize());
              node2 = triton::ast::bv(0x20402055, dst2.getBitSize());
              node3 = triton::ast::bv(0x30392e32, dst3.getBitSize());
              node4 = triton::ast::bv(0x007a4847, dst4.getBitSize());
              break;
            case 0x80000005:
              node1 = triton::ast::bv(0x00000000, dst1.getBitSize());
              node2 = triton::ast::bv(0x00000000, dst2.getBitSize());
              node3 = triton::ast::bv(0x00000000, dst3.getBitSize());
              node4 = triton::ast::bv(0x00000000, dst4.getBitSize());
              break;
            case 0x80000006:
              node1 = triton::ast::bv(0x00000000, dst1.getBitSize());
              node2 = triton::ast::bv(0x00000000, dst2.getBitSize());
              node3 = triton::ast::bv(0x01006040, dst3.getBitSize());
              node4 = triton::ast::bv(0x00000000, dst4.getBitSize());
              break;
            case 0x80000007:
              node1 = triton::ast::bv(0x00000000, dst1.getBitSize());
              node2 = triton::ast::bv(0x00000000, dst2.getBitSize());
              node3 = triton::ast::bv(0x00000000, dst3.getBitSize());
              node4 = triton::ast::bv(0x00000100, dst4.getBitSize());
              break;
            case 0x80000008:
              node1 = triton::ast::bv(0x00003024, dst1.getBitSize());
              node2 = triton::ast::bv(0x00000000, dst2.getBitSize());
              node3 = triton::ast::bv(0x00000000, dst3.getBitSize());
              node4 = triton::ast::bv(0x00000000, dst4.getBitSize());
              break;
            default:
              node1 = triton::ast::bv(0x00000007, dst1.getBitSize());
              node2 = triton::ast::bv(0x00000340, dst2.getBitSize());
              node3 = triton::ast::bv(0x00000340, dst3.getBitSize());
              node4 = triton::ast::bv(0x00000000, dst4.getBitSize());
              break;
          }

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicExpression(inst, node1, dst1, "CPUID AX operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, dst2, "CPUID BX operation");
          auto expr3 = triton::api.createSymbolicExpression(inst, node3, dst3, "CPUID CX operation");
          auto expr4 = triton::api.createSymbolicExpression(inst, node4, dst4, "CPUID DX operation");

          /* Spread taint */
          expr1->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_AX.getParent(), false);
          expr2->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_BX.getParent(), false);
          expr3->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_CX.getParent(), false);
          expr4->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_DX.getParent(), false);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cqo_s(triton::arch::Instruction& inst) {
          auto dst = triton::arch::OperandWrapper(TRITON_X86_REG_RDX);
          auto src = triton::arch::OperandWrapper(TRITON_X86_REG_RAX);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics - TMP = 128 bitvec (RDX:RAX) */
          auto node1 = triton::ast::sx(QWORD_SIZE_BIT, op1);

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicVolatileExpression(inst, node1, "Temporary variable");

          /* Spread taint */
          expr1->isTainted = triton::api.isRegisterTainted(TRITON_X86_REG_RDX) | triton::api.isRegisterTainted(TRITON_X86_REG_RAX);

          /* Create the semantics - RAX = TMP[63...0] */
          auto node2 = triton::ast::extract(QWORD_SIZE_BIT-1, 0, triton::ast::reference(expr1->getId()));

          /* Create symbolic expression */
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, src, "CQO operation - RAX");

          /* Spread taint */
          expr2->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_RAX, expr1->isTainted);

          /* Create the semantics - RDX = TMP[127...64] */
          auto node3 = triton::ast::extract(DQWORD_SIZE_BIT-1, QWORD_SIZE_BIT, triton::ast::reference(expr1->getId()));

          /* Create symbolic expression */
          auto expr3 = triton::api.createSymbolicExpression(inst, node3, dst, "CQO operation - RDX");

          /* Spread taint */
          expr3->isTainted = triton::api.setTaintRegister(TRITON_X86_REG_RDX, expr1->isTainted);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void cwde_s(triton::arch::Instruction& inst) {
          auto dst = triton::arch::OperandWrapper(TRITON_X86_REG_EAX);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);

          /* Create the semantics */
          auto node = triton::ast::sx(WORD_SIZE_BIT, triton::ast::extract(WORD_SIZE_BIT-1, 0, op1));

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "CWDE operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void dec_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::ast::bv(1, dst.getBitSize());

          /* Create the semantics */
          auto node = triton::ast::bvsub(op1, op2);

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
          auto& src = inst.operands[0];

          /* Create symbolic operands */
          auto divisor = triton::api.buildSymbolicOperand(inst, src);

          /* Create symbolic expression */
          switch (src.getSize()) {

            case BYTE_SIZE: {
              /* AX */
              auto ax = triton::arch::OperandWrapper(TRITON_X86_REG_AX);
              auto dividend = triton::api.buildSymbolicOperand(inst, ax);
              /* res = AX / Source */
              auto result = triton::ast::bvudiv(dividend, triton::ast::zx(BYTE_SIZE_BIT, divisor));
              /* mod = AX % Source */
              auto mod = triton::ast::bvurem(dividend, triton::ast::zx(BYTE_SIZE_BIT, divisor));
              /* AH = mod */
              /* AL = res */
              auto node = triton::ast::concat(
                            triton::ast::extract((BYTE_SIZE_BIT - 1), 0, mod),   /* AH = mod */
                            triton::ast::extract((BYTE_SIZE_BIT - 1), 0, result) /* AL = res */
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
              auto dividend = triton::ast::concat(triton::api.buildSymbolicOperand(inst, dx), triton::api.buildSymbolicOperand(inst, ax));
              /* res = DX:AX / Source */
              auto result = triton::ast::extract((WORD_SIZE_BIT - 1), 0, triton::ast::bvudiv(dividend, triton::ast::zx(WORD_SIZE_BIT, divisor)));
              /* mod = DX:AX % Source */
              auto mod = triton::ast::extract((WORD_SIZE_BIT - 1), 0, triton::ast::bvurem(dividend, triton::ast::zx(WORD_SIZE_BIT, divisor)));
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
              auto dividend = triton::ast::concat(triton::api.buildSymbolicOperand(inst, edx), triton::api.buildSymbolicOperand(inst, eax));
              /* res = EDX:EAX / Source */
              auto result = triton::ast::extract((DWORD_SIZE_BIT - 1), 0, triton::ast::bvudiv(dividend, triton::ast::zx(DWORD_SIZE_BIT, divisor)));
              /* mod = EDX:EAX % Source */
              auto mod = triton::ast::extract((DWORD_SIZE_BIT - 1), 0, triton::ast::bvurem(dividend, triton::ast::zx(DWORD_SIZE_BIT, divisor)));
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
              auto dividend = triton::ast::concat(triton::api.buildSymbolicOperand(inst, rdx), triton::api.buildSymbolicOperand(inst, rax));
              /* res = RDX:RAX / Source */
              auto result = triton::ast::extract((QWORD_SIZE_BIT - 1), 0, triton::ast::bvudiv(dividend, triton::ast::zx(QWORD_SIZE_BIT, divisor)));
              /* mod = RDX:RAX % Source */
              auto mod = triton::ast::extract((QWORD_SIZE_BIT - 1), 0, triton::ast::bvurem(dividend, triton::ast::zx(QWORD_SIZE_BIT, divisor)));
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
          auto& src = inst.operands[0];

          /* Create symbolic operands */
          auto divisor = triton::api.buildSymbolicOperand(inst, src);

          /* Create symbolic expression */
          switch (src.getSize()) {

            case BYTE_SIZE: {
              /* AX */
              auto ax = triton::arch::OperandWrapper(TRITON_X86_REG_AX);
              auto dividend = triton::api.buildSymbolicOperand(inst, ax);
              /* res = AX / Source */
              auto result = triton::ast::bvsdiv(dividend, triton::ast::sx(BYTE_SIZE_BIT, divisor));
              /* mod = AX % Source */
              auto mod = triton::ast::bvsrem(dividend, triton::ast::sx(BYTE_SIZE_BIT, divisor));
              /* AH = mod */
              /* AL = res */
              auto node = triton::ast::concat(
                            triton::ast::extract((BYTE_SIZE_BIT - 1), 0, mod),   /* AH = mod */
                            triton::ast::extract((BYTE_SIZE_BIT - 1), 0, result) /* AL = res */
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
              auto dividend = triton::ast::concat(triton::api.buildSymbolicOperand(inst, dx), triton::api.buildSymbolicOperand(inst, ax));
              /* res = DX:AX / Source */
              auto result = triton::ast::extract((WORD_SIZE_BIT - 1), 0, triton::ast::bvsdiv(dividend, triton::ast::sx(WORD_SIZE_BIT, divisor)));
              /* mod = DX:AX % Source */
              auto mod = triton::ast::extract((WORD_SIZE_BIT - 1), 0, triton::ast::bvsrem(dividend, triton::ast::sx(WORD_SIZE_BIT, divisor)));
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
              auto dividend = triton::ast::concat(triton::api.buildSymbolicOperand(inst, edx), triton::api.buildSymbolicOperand(inst, eax));
              /* res = EDX:EAX / Source */
              auto result = triton::ast::extract((DWORD_SIZE_BIT - 1), 0, triton::ast::bvsdiv(dividend, triton::ast::sx(DWORD_SIZE_BIT, divisor)));
              /* mod = EDX:EAX % Source */
              auto mod = triton::ast::extract((DWORD_SIZE_BIT - 1), 0, triton::ast::bvsrem(dividend, triton::ast::sx(DWORD_SIZE_BIT, divisor)));
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
              auto dividend = triton::ast::concat(triton::api.buildSymbolicOperand(inst, rdx), triton::api.buildSymbolicOperand(inst, rax));
              /* res = RDX:RAX / Source */
              auto result = triton::ast::extract((QWORD_SIZE_BIT - 1), 0, triton::ast::bvsdiv(dividend, triton::ast::sx(QWORD_SIZE_BIT, divisor)));
              /* mod = RDX:RAX % Source */
              auto mod = triton::ast::extract((QWORD_SIZE_BIT - 1), 0, triton::ast::bvsrem(dividend, triton::ast::sx(QWORD_SIZE_BIT, divisor)));
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
              auto& src = inst.operands[0];

              /* size of the Operand */
              switch (src.getSize()) {

                /* dst = AX */
                case BYTE_SIZE: {
                  auto ax   = triton::arch::OperandWrapper(TRITON_X86_REG_AX);
                  auto al   = triton::arch::OperandWrapper(TRITON_X86_REG_AL);
                  auto op1  = triton::api.buildSymbolicOperand(inst, al);
                  auto op2  = triton::api.buildSymbolicOperand(inst, src);
                  auto node = triton::ast::bvmul(triton::ast::sx(BYTE_SIZE_BIT, op1), triton::ast::sx(BYTE_SIZE_BIT, op2));
                  auto expr = triton::api.createSymbolicExpression(inst, node, ax, "IMUL operation");
                  expr->isTainted = triton::api.taintUnion(ax, src);
                  triton::arch::x86::semantics::cfImul_s(inst, expr, al, triton::ast::bvmul(op1, op2), node);
                  triton::arch::x86::semantics::ofImul_s(inst, expr, al, triton::ast::bvmul(op1, op2), node);
                  break;
                }

                /* dst = DX:AX */
                case WORD_SIZE: {
                  auto ax    = triton::arch::OperandWrapper(TRITON_X86_REG_AX);
                  auto dx    = triton::arch::OperandWrapper(TRITON_X86_REG_DX);
                  auto op1   = triton::api.buildSymbolicOperand(inst, ax);
                  auto op2   = triton::api.buildSymbolicOperand(inst, src);
                  auto node  = triton::ast::bvmul(triton::ast::sx(WORD_SIZE_BIT, op1), triton::ast::sx(WORD_SIZE_BIT, op2));
                  auto expr1 = triton::api.createSymbolicExpression(inst, triton::ast::extract(WORD_SIZE_BIT-1, 0, node), ax, "IMUL operation");
                  auto expr2 = triton::api.createSymbolicExpression(inst, triton::ast::extract(DWORD_SIZE_BIT-1, WORD_SIZE_BIT, node), dx, "IMUL operation");
                  expr1->isTainted = triton::api.taintUnion(ax, src);
                  expr2->isTainted = triton::api.taintUnion(dx, ax);
                  triton::arch::x86::semantics::cfImul_s(inst, expr1, ax, triton::ast::bvmul(op1, op2), node);
                  triton::arch::x86::semantics::ofImul_s(inst, expr1, ax, triton::ast::bvmul(op1, op2), node);
                  break;
                }

                /* dst = EDX:EAX */
                case DWORD_SIZE: {
                  auto eax   = triton::arch::OperandWrapper(TRITON_X86_REG_EAX);
                  auto edx   = triton::arch::OperandWrapper(TRITON_X86_REG_EDX);
                  auto op1   = triton::api.buildSymbolicOperand(inst, eax);
                  auto op2   = triton::api.buildSymbolicOperand(inst, src);
                  auto node  = triton::ast::bvmul(triton::ast::sx(DWORD_SIZE_BIT, op1), triton::ast::sx(DWORD_SIZE_BIT, op2));
                  auto expr1 = triton::api.createSymbolicExpression(inst, triton::ast::extract(DWORD_SIZE_BIT-1, 0, node), eax, "IMUL operation");
                  auto expr2 = triton::api.createSymbolicExpression(inst, triton::ast::extract(QWORD_SIZE_BIT-1, DWORD_SIZE_BIT, node), edx, "IMUL operation");
                  expr1->isTainted = triton::api.taintUnion(eax, src);
                  expr2->isTainted = triton::api.taintUnion(edx, eax);
                  triton::arch::x86::semantics::cfImul_s(inst, expr1, eax, triton::ast::bvmul(op1, op2), node);
                  triton::arch::x86::semantics::ofImul_s(inst, expr1, eax, triton::ast::bvmul(op1, op2), node);
                  break;
                }

                /* dst = RDX:RAX */
                case QWORD_SIZE: {
                  auto rax   = triton::arch::OperandWrapper(TRITON_X86_REG_RAX);
                  auto rdx   = triton::arch::OperandWrapper(TRITON_X86_REG_RDX);
                  auto op1   = triton::api.buildSymbolicOperand(inst, rax);
                  auto op2   = triton::api.buildSymbolicOperand(inst, src);
                  auto node  = triton::ast::bvmul(triton::ast::sx(QWORD_SIZE_BIT, op1), triton::ast::sx(QWORD_SIZE_BIT, op2));
                  auto expr1 = triton::api.createSymbolicExpression(inst, triton::ast::extract(QWORD_SIZE_BIT-1, 0, node), rax, "IMUL operation");
                  auto expr2 = triton::api.createSymbolicExpression(inst, triton::ast::extract(DQWORD_SIZE_BIT-1, QWORD_SIZE_BIT, node), rdx, "IMUL operation");
                  expr1->isTainted = triton::api.taintUnion(rax, src);
                  expr2->isTainted = triton::api.taintUnion(rdx, rax);
                  triton::arch::x86::semantics::cfImul_s(inst, expr1, rax, triton::ast::bvmul(op1, op2), node);
                  triton::arch::x86::semantics::ofImul_s(inst, expr1, rax, triton::ast::bvmul(op1, op2), node);
                  break;
                }

              }
              break;
            }

            /* two operands */
            case 2: {
              auto& dst  = inst.operands[0];
              auto& src  = inst.operands[1];
              auto  op1  = triton::api.buildSymbolicOperand(inst, dst);
              auto  op2  = triton::api.buildSymbolicOperand(inst, src);
              auto  node = triton::ast::bvmul(triton::ast::sx(dst.getBitSize(), op1), triton::ast::sx(src.getBitSize(), op2));
              auto  expr = triton::api.createSymbolicExpression(inst, triton::ast::extract(dst.getBitSize()-1, 0, node), dst, "IMUL operation");
              expr->isTainted = triton::api.taintUnion(dst, src);
              triton::arch::x86::semantics::cfImul_s(inst, expr, dst, triton::ast::bvmul(op1, op2), node);
              triton::arch::x86::semantics::ofImul_s(inst, expr, dst, triton::ast::bvmul(op1, op2), node);
              break;
            }

            /* three operands */
            case 3: {
              auto& dst  = inst.operands[0];
              auto& src1 = inst.operands[1];
              auto& src2 = inst.operands[2];
              auto  op2  = triton::api.buildSymbolicOperand(inst, src1);
              auto  op3  = triton::api.buildSymbolicOperand(inst, src2);
              auto  node = triton::ast::bvmul(triton::ast::sx(src1.getBitSize(), op2), triton::ast::sx(src2.getBitSize(), op3));
              auto  expr = triton::api.createSymbolicExpression(inst, triton::ast::extract(dst.getBitSize()-1, 0, node), dst, "IMUL operation");
              expr->isTainted = triton::api.taintUnion(dst, src1);
              expr->isTainted = triton::api.taintUnion(dst, src2);
              triton::arch::x86::semantics::cfImul_s(inst, expr, dst, triton::ast::bvmul(op2, op3), node);
              triton::arch::x86::semantics::ofImul_s(inst, expr, dst, triton::ast::bvmul(op2, op3), node);
              break;
            }

          }

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void inc_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::ast::bv(1, dst.getBitSize());

          /* Create the semantics */
          auto node = triton::ast::bvadd(op1, op2);

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
          auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto  cf      = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
          auto  zf      = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
          auto  srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto& srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, cf);
          auto op2 = triton::api.buildSymbolicOperand(inst, zf);
          auto op3 = triton::api.buildSymbolicOperand(inst, srcImm1);
          auto op4 = triton::api.buildSymbolicOperand(inst, srcImm2);

          /* Create the semantics */
          auto node = triton::ast::ite(
                        triton::ast::equal(
                          triton::ast::bvand(
                            triton::ast::bvnot(op1),
                            triton::ast::bvnot(op2)
                          ),
                          triton::ast::bvtrue()
                        ), op4, op3);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if ((!triton::api.getRegisterValue(TRITON_X86_REG_CF) & !triton::api.getRegisterValue(TRITON_X86_REG_ZF)) == true)
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, cf);
          expr->isTainted = triton::api.taintUnion(pc, zf);

          /* Create the path constraint */
          triton::api.addPathConstraint(expr);
        }


        void jae_s(triton::arch::Instruction& inst) {
          auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto  cf      = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
          auto  srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto& srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, cf);
          auto op2 = triton::api.buildSymbolicOperand(inst, srcImm1);
          auto op3 = triton::api.buildSymbolicOperand(inst, srcImm2);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(op1, triton::ast::bvfalse()), op3, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (!triton::api.getRegisterValue(TRITON_X86_REG_CF))
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, cf);

          /* Create the path constraint */
          triton::api.addPathConstraint(expr);
        }


        void jb_s(triton::arch::Instruction& inst) {
          auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto  cf      = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
          auto  srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto& srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, cf);
          auto op2 = triton::api.buildSymbolicOperand(inst, srcImm1);
          auto op3 = triton::api.buildSymbolicOperand(inst, srcImm2);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(op1, triton::ast::bvtrue()), op3, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_CF))
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, cf);

          /* Create the path constraint */
          triton::api.addPathConstraint(expr);
        }


        void jbe_s(triton::arch::Instruction& inst) {
          auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto  cf      = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
          auto  zf      = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
          auto  srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto& srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, cf);
          auto op2 = triton::api.buildSymbolicOperand(inst, zf);
          auto op3 = triton::api.buildSymbolicOperand(inst, srcImm1);
          auto op4 = triton::api.buildSymbolicOperand(inst, srcImm2);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(triton::ast::bvor(op1, op2), triton::ast::bvtrue()), op4, op3);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_CF) | triton::api.getRegisterValue(TRITON_X86_REG_ZF))
            inst.setConditionTaken(true);


          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, cf);
          expr->isTainted = triton::api.taintUnion(pc, zf);

          /* Create the path constraint */
          triton::api.addPathConstraint(expr);
        }


        void je_s(triton::arch::Instruction& inst) {
          auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto  zf      = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
          auto  srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto& srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, zf);
          auto op2 = triton::api.buildSymbolicOperand(inst, srcImm1);
          auto op3 = triton::api.buildSymbolicOperand(inst, srcImm2);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(op1, triton::ast::bvtrue()), op3, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_ZF))
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, zf);

          /* Create the path constraint */
          triton::api.addPathConstraint(expr);
        }


        void jg_s(triton::arch::Instruction& inst) {
          auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto  sf      = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto  of      = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
          auto  zf      = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
          auto  srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto& srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, sf);
          auto op2 = triton::api.buildSymbolicOperand(inst, of);
          auto op3 = triton::api.buildSymbolicOperand(inst, zf);
          auto op4 = triton::api.buildSymbolicOperand(inst, srcImm1);
          auto op5 = triton::api.buildSymbolicOperand(inst, srcImm2);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(triton::ast::bvor(triton::ast::bvxor(op1, op2), op3), triton::ast::bvfalse()), op5, op4);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (((triton::api.getRegisterValue(TRITON_X86_REG_SF) ^ triton::api.getRegisterValue(TRITON_X86_REG_OF)) | triton::api.getRegisterValue(TRITON_X86_REG_ZF)) == false)
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, sf);
          expr->isTainted = triton::api.taintUnion(pc, of);
          expr->isTainted = triton::api.taintUnion(pc, zf);

          /* Create the path constraint */
          triton::api.addPathConstraint(expr);
        }


        void jge_s(triton::arch::Instruction& inst) {
          auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto  sf      = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto  of      = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
          auto  srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto& srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, sf);
          auto op2 = triton::api.buildSymbolicOperand(inst, of);
          auto op3 = triton::api.buildSymbolicOperand(inst, srcImm1);
          auto op4 = triton::api.buildSymbolicOperand(inst, srcImm2);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(op1, op2), op4, op3);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_SF) == triton::api.getRegisterValue(TRITON_X86_REG_OF))
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, sf);
          expr->isTainted = triton::api.taintUnion(pc, of);

          /* Create the path constraint */
          triton::api.addPathConstraint(expr);
        }


        void jl_s(triton::arch::Instruction& inst) {
          auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto  sf      = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto  of      = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
          auto  srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto& srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, sf);
          auto op2 = triton::api.buildSymbolicOperand(inst, of);
          auto op3 = triton::api.buildSymbolicOperand(inst, srcImm1);
          auto op4 = triton::api.buildSymbolicOperand(inst, srcImm2);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(triton::ast::bvxor(op1, op2), triton::ast::bvtrue()), op4, op3);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_SF) ^ triton::api.getRegisterValue(TRITON_X86_REG_OF))
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, sf);
          expr->isTainted = triton::api.taintUnion(pc, of);

          /* Create the path constraint */
          triton::api.addPathConstraint(expr);
        }


        void jle_s(triton::arch::Instruction& inst) {
          auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto  sf      = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto  of      = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
          auto  zf      = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
          auto  srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto& srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, sf);
          auto op2 = triton::api.buildSymbolicOperand(inst, of);
          auto op3 = triton::api.buildSymbolicOperand(inst, zf);
          auto op4 = triton::api.buildSymbolicOperand(inst, srcImm1);
          auto op5 = triton::api.buildSymbolicOperand(inst, srcImm2);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(triton::ast::bvor(triton::ast::bvxor(op1, op2), op3), triton::ast::bvtrue()), op5, op4);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (((triton::api.getRegisterValue(TRITON_X86_REG_SF) ^ triton::api.getRegisterValue(TRITON_X86_REG_OF)) | triton::api.getRegisterValue(TRITON_X86_REG_ZF)) == true)
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, sf);
          expr->isTainted = triton::api.taintUnion(pc, of);
          expr->isTainted = triton::api.taintUnion(pc, zf);

          /* Create the path constraint */
          triton::api.addPathConstraint(expr);
        }


        void jmp_s(triton::arch::Instruction& inst) {
          auto  pc  = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto& src = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = op1;

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, src);

          /* Create the path constraint */
          triton::api.addPathConstraint(expr);
        }


        void jne_s(triton::arch::Instruction& inst) {
          auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto  zf      = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
          auto  srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto& srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, zf);
          auto op2 = triton::api.buildSymbolicOperand(inst, srcImm1);
          auto op3 = triton::api.buildSymbolicOperand(inst, srcImm2);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(op1, triton::ast::bvfalse()), op3, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (!triton::api.getRegisterValue(TRITON_X86_REG_ZF))
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, zf);

          /* Create the path constraint */
          triton::api.addPathConstraint(expr);
        }


        void jno_s(triton::arch::Instruction& inst) {
          auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto  of      = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
          auto  srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto& srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, of);
          auto op2 = triton::api.buildSymbolicOperand(inst, srcImm1);
          auto op3 = triton::api.buildSymbolicOperand(inst, srcImm2);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(op1, triton::ast::bvfalse()), op3, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (!triton::api.getRegisterValue(TRITON_X86_REG_OF))
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, of);

          /* Create the path constraint */
          triton::api.addPathConstraint(expr);
        }


        void jnp_s(triton::arch::Instruction& inst) {
          auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto  pf      = triton::arch::OperandWrapper(TRITON_X86_REG_PF);
          auto  srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto& srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, pf);
          auto op2 = triton::api.buildSymbolicOperand(inst, srcImm1);
          auto op3 = triton::api.buildSymbolicOperand(inst, srcImm2);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(op1, triton::ast::bvfalse()), op3, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (!triton::api.getRegisterValue(TRITON_X86_REG_PF))
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, pf);

          /* Create the path constraint */
          triton::api.addPathConstraint(expr);
        }


        void jns_s(triton::arch::Instruction& inst) {
          auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto  sf      = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto  srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto& srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, sf);
          auto op2 = triton::api.buildSymbolicOperand(inst, srcImm1);
          auto op3 = triton::api.buildSymbolicOperand(inst, srcImm2);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(op1, triton::ast::bvfalse()), op3, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (!triton::api.getRegisterValue(TRITON_X86_REG_SF))
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, sf);

          /* Create the path constraint */
          triton::api.addPathConstraint(expr);
        }


        void jo_s(triton::arch::Instruction& inst) {
          auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto  of      = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
          auto  srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto& srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, of);
          auto op2 = triton::api.buildSymbolicOperand(inst, srcImm1);
          auto op3 = triton::api.buildSymbolicOperand(inst, srcImm2);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(op1, triton::ast::bvtrue()), op3, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_OF))
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, of);

          /* Create the path constraint */
          triton::api.addPathConstraint(expr);
        }


        void jp_s(triton::arch::Instruction& inst) {
          auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto  pf      = triton::arch::OperandWrapper(TRITON_X86_REG_PF);
          auto  srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto& srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, pf);
          auto op2 = triton::api.buildSymbolicOperand(inst, srcImm1);
          auto op3 = triton::api.buildSymbolicOperand(inst, srcImm2);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(op1, triton::ast::bvtrue()), op3, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_PF))
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, pf);

          /* Create the path constraint */
          triton::api.addPathConstraint(expr);
        }


        void js_s(triton::arch::Instruction& inst) {
          auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto  sf      = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto  srcImm1 = triton::arch::OperandWrapper(ImmediateOperand(inst.getNextAddress(), pc.getSize()));
          auto& srcImm2 = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, sf);
          auto op2 = triton::api.buildSymbolicOperand(inst, srcImm1);
          auto op3 = triton::api.buildSymbolicOperand(inst, srcImm2);

          /* Create the semantics */
          auto node = triton::ast::ite(triton::ast::equal(op1, triton::ast::bvtrue()), op3, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Set condition flag */
          if (triton::api.getRegisterValue(TRITON_X86_REG_SF))
            inst.setConditionTaken(true);

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, sf);

          /* Create the path constraint */
          triton::api.addPathConstraint(expr);
        }


        void lddqu_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create the semantics */
          auto node = triton::api.buildSymbolicOperand(inst, src);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "LDDQU operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void ldmxcsr_s(triton::arch::Instruction& inst) {
          auto  dst = triton::arch::OperandWrapper(TRITON_X86_REG_MXCSR);
          auto& src = inst.operands[0];

          /* Create the semantics */
          auto node = triton::api.buildSymbolicOperand(inst, src);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "LDMXCSR operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void lea_s(triton::arch::Instruction& inst) {
          auto& dst                = inst.operands[0].getRegister();
          auto& srcDisp            = inst.operands[1].getMemory().getDisplacement();
          auto& srcBase            = inst.operands[1].getMemory().getBaseRegister();
          auto& srcIndex           = inst.operands[1].getMemory().getIndexRegister();
          auto& srcScale           = inst.operands[1].getMemory().getScale();
          triton::uint32 leaSize   = 0;

          /* Setup LEA size */
          if (srcBase.isValid())
            leaSize = srcBase.getBitSize();
          else if (srcIndex.isValid())
            leaSize = srcIndex.getBitSize();
          else
            leaSize = srcDisp.getBitSize();

          /* Create symbolic operands */

          /* Displacement */
          auto op2 = triton::api.buildSymbolicImmediateOperand(inst, srcDisp);
          if (leaSize > srcDisp.getBitSize())
            op2 = triton::ast::zx(leaSize - srcDisp.getBitSize(), op2);

          /* Base */
          triton::ast::AbstractNode* op3;
          if (srcBase.isValid())
            op3 = triton::api.buildSymbolicRegisterOperand(inst, srcBase);
          else
            op3 = triton::ast::bv(0, leaSize);

          /* Base with PC */
          if (srcBase.isValid() && (srcBase.getParent().getId() == TRITON_X86_REG_PC.getId()))
            op3 = triton::ast::bvadd(op3, triton::ast::bv(inst.getSize(), leaSize));

          /* Index */
          triton::ast::AbstractNode* op4;
          if (srcIndex.isValid())
            op4 = triton::api.buildSymbolicRegisterOperand(inst, srcIndex);
          else
            op4 = triton::ast::bv(0, leaSize);

          /* Scale */
          auto op5 = triton::api.buildSymbolicImmediateOperand(inst, srcScale);
          if (leaSize > srcScale.getBitSize())
            op5 = triton::ast::zx(leaSize - srcScale.getBitSize(), op5);

          /* Create the semantics */
          /* Effective address = Displacement + BaseReg + IndexReg * Scale */
          auto node = triton::ast::bvadd(op2, triton::ast::bvadd(op3, triton::ast::bvmul(op4, op5)));

          if (dst.getBitSize() > leaSize)
            node = triton::ast::zx(dst.getBitSize() - leaSize, node);

          if (dst.getBitSize() < leaSize)
            node = triton::ast::extract(dst.getAbstractHigh(), dst.getAbstractLow(), node);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicRegisterExpression(inst, node, dst, "LEA operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignmentRegisterRegister(dst, srcBase);
          expr->isTainted = triton::api.taintUnionRegisterRegister(dst, srcIndex);

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
          auto op1 = triton::api.buildSymbolicOperand(inst, bp2);

          /* RSP = RBP */
          auto node1 = op1;

          /* Create the symbolic expression */
          auto expr1 = triton::api.createSymbolicExpression(inst, node1, sp, "Stack Pointer");

          /* Spread taint */
          expr1->isTainted = triton::api.taintAssignment(sp, bp2);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, bp1);

          /* RBP = pop() */
          auto node2 = op2;

          /* Create the symbolic expression */
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, bp2, "Stack Top Pointer");

          /* Spread taint */
          expr2->isTainted = triton::api.taintAssignment(bp2, bp1);

          /* Create the semantics - side effect */
          alignAddStack_s(inst, bp1.getSize());

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void lodsb_s(triton::arch::Instruction& inst) {
          auto& dst    = inst.operands[0];
          auto& src    = inst.operands[1];
          auto  index  = triton::arch::OperandWrapper(TRITON_X86_REG_SI.getParent());
          auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);
          auto op2 = triton::api.buildSymbolicOperand(inst, index);
          auto op3 = triton::api.buildSymbolicOperand(inst, df);

          /* Create the semantics */
          auto node1 = op1;
          auto node2 = triton::ast::ite(
                         triton::ast::equal(op3, triton::ast::bvfalse()),
                         triton::ast::bvadd(op2, triton::ast::bv(BYTE_SIZE, index.getBitSize())),
                         triton::ast::bvsub(op2, triton::ast::bv(BYTE_SIZE, index.getBitSize()))
                       );

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicExpression(inst, node1, dst, "LODSB operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, index, "Index operation");

          /* Spread taint */
          expr1->isTainted = triton::api.taintAssignment(dst, src);
          expr2->isTainted = triton::api.taintUnion(index, index);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void lodsd_s(triton::arch::Instruction& inst) {
          auto& dst    = inst.operands[0];
          auto& src    = inst.operands[1];
          auto  index  = triton::arch::OperandWrapper(TRITON_X86_REG_SI.getParent());
          auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);
          auto op2 = triton::api.buildSymbolicOperand(inst, index);
          auto op3 = triton::api.buildSymbolicOperand(inst, df);

          /* Create the semantics */
          auto node1 = op1;
          auto node2 = triton::ast::ite(
                         triton::ast::equal(op3, triton::ast::bvfalse()),
                         triton::ast::bvadd(op2, triton::ast::bv(DWORD_SIZE, index.getBitSize())),
                         triton::ast::bvsub(op2, triton::ast::bv(DWORD_SIZE, index.getBitSize()))
                       );

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicExpression(inst, node1, dst, "LODSD operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, index, "Index operation");

          /* Spread taint */
          expr1->isTainted = triton::api.taintAssignment(dst, src);
          expr2->isTainted = triton::api.taintUnion(index, index);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void lodsq_s(triton::arch::Instruction& inst) {
          auto& dst    = inst.operands[0];
          auto& src    = inst.operands[1];
          auto  index  = triton::arch::OperandWrapper(TRITON_X86_REG_SI.getParent());
          auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);
          auto op2 = triton::api.buildSymbolicOperand(inst, index);
          auto op3 = triton::api.buildSymbolicOperand(inst, df);

          /* Create the semantics */
          auto node1 = op1;
          auto node2 = triton::ast::ite(
                         triton::ast::equal(op3, triton::ast::bvfalse()),
                         triton::ast::bvadd(op2, triton::ast::bv(QWORD_SIZE, index.getBitSize())),
                         triton::ast::bvsub(op2, triton::ast::bv(QWORD_SIZE, index.getBitSize()))
                       );

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicExpression(inst, node1, dst, "LODSQ operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, index, "Index operation");

          /* Spread taint */
          expr1->isTainted = triton::api.taintAssignment(dst, src);
          expr2->isTainted = triton::api.taintUnion(index, index);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void lodsw_s(triton::arch::Instruction& inst) {
          auto& dst    = inst.operands[0];
          auto& src    = inst.operands[1];
          auto  index  = triton::arch::OperandWrapper(TRITON_X86_REG_SI.getParent());
          auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);
          auto op2 = triton::api.buildSymbolicOperand(inst, index);
          auto op3 = triton::api.buildSymbolicOperand(inst, df);

          /* Create the semantics */
          auto node1 = op1;
          auto node2 = triton::ast::ite(
                         triton::ast::equal(op3, triton::ast::bvfalse()),
                         triton::ast::bvadd(op2, triton::ast::bv(WORD_SIZE, index.getBitSize())),
                         triton::ast::bvsub(op2, triton::ast::bv(WORD_SIZE, index.getBitSize()))
                       );

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicExpression(inst, node1, dst, "LODSW operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, index, "Index operation");

          /* Spread taint */
          expr1->isTainted = triton::api.taintAssignment(dst, src);
          expr2->isTainted = triton::api.taintUnion(index, index);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void mov_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create the semantics */
          auto node = triton::api.buildSymbolicOperand(inst, src);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOV operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movabs_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create the semantics */
          auto node = triton::api.buildSymbolicOperand(inst, src);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVABS operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movapd_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create the semantics */
          auto node = triton::api.buildSymbolicOperand(inst, src);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVAPD operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movaps_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create the semantics */
          auto node = triton::api.buildSymbolicOperand(inst, src);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVAPS operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movd_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          triton::ast::AbstractNode* node = nullptr;

          switch (dst.getBitSize()) {
            /* GPR 32-bits */
            case DWORD_SIZE_BIT:
              node = triton::ast::extract(DWORD_SIZE_BIT-1, 0, op2);
              break;

            /* MMX 64-bits */
            case QWORD_SIZE_BIT:
              node = triton::ast::zx(DWORD_SIZE_BIT, triton::ast::extract(DWORD_SIZE_BIT-1, 0, op2));
              break;

            /* XMM 128-bits */
            case DQWORD_SIZE_BIT:
              node = triton::ast::zx(QWORD_SIZE_BIT + DWORD_SIZE_BIT, triton::ast::extract(DWORD_SIZE_BIT-1, 0, op2));
              break;
          }

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVD operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movddup_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::concat(triton::ast::extract(QWORD_SIZE_BIT-1, 0, op2), triton::ast::extract(QWORD_SIZE_BIT-1, 0, op2));

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVDDUP operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movdq2q_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::extract(QWORD_SIZE_BIT-1, 0, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVDQ2Q operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movdqa_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create the semantics */
          auto node = triton::api.buildSymbolicOperand(inst, src);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVDQA operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movdqu_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create the semantics */
          auto node = triton::api.buildSymbolicOperand(inst, src);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVDQU operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movhlps_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::concat(
                        triton::ast::extract((DQWORD_SIZE_BIT - 1), QWORD_SIZE_BIT, op1), /* Destination[127..64] unchanged */
                        triton::ast::extract((DQWORD_SIZE_BIT - 1), QWORD_SIZE_BIT, op2)  /* Destination[63..0] = Source[127..64]; */
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVHLPS operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movhpd_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::concat(
                        triton::ast::extract((QWORD_SIZE_BIT - 1), 0, op2), /* Destination[127..64] = Source */
                        triton::ast::extract((QWORD_SIZE_BIT - 1), 0, op1)  /* Destination[63..0] unchanged */
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVHPD operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movhps_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::concat(
                        triton::ast::extract((QWORD_SIZE_BIT - 1), 0, op2), /* Destination[127..64] = Source */
                        triton::ast::extract((QWORD_SIZE_BIT - 1), 0, op1)  /* Destination[63..0] unchanged */
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVHPS operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movlhps_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::concat(
                        triton::ast::extract((QWORD_SIZE_BIT - 1), 0, op2), /* Destination[127..64] = Source[63..0] */
                        triton::ast::extract((QWORD_SIZE_BIT - 1), 0, op1)  /* Destination[63..0] unchanged */
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVLHPS operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movlpd_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::concat(
                        triton::ast::extract((DQWORD_SIZE_BIT - 1), QWORD_SIZE_BIT, op1), /* Destination[127..64] unchanged */
                        triton::ast::extract((QWORD_SIZE_BIT - 1), 0, op2)                /* Destination[63..0] = Source */
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVLPD operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movlps_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::concat(
                        triton::ast::extract((DQWORD_SIZE_BIT - 1), QWORD_SIZE_BIT, op1), /* Destination[127..64] unchanged */
                        triton::ast::extract((QWORD_SIZE_BIT - 1), 0, op2)                /* Destination[63..0] = Source */
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVLPS operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movmskpd_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::zx(30,                       /* Destination[2..31] = 0        */
                        triton::ast::concat(
                          triton::ast::extract(127, 127, op2),  /* Destination[1] = Source[127]; */
                          triton::ast::extract(63, 63, op2)     /* Destination[0] = Source[63];  */
                        )
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVMSKPD operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movmskps_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> signs;

          signs.push_back(triton::ast::extract(127, 127, op2)); /* Destination[3] = Source[127]; */
          signs.push_back(triton::ast::extract(95, 95,   op2)); /* Destination[2] = Source[95];  */
          signs.push_back(triton::ast::extract(63, 63,   op2)); /* Destination[1] = Source[63];  */
          signs.push_back(triton::ast::extract(31, 31,   op2)); /* Destination[0] = Source[31];  */

          auto node = triton::ast::zx(28, triton::ast::concat(signs));

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVMSKPS operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movntdq_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create the semantics */
          auto node = triton::api.buildSymbolicOperand(inst, src);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVNTDQ operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movnti_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create the semantics */
          auto node = triton::api.buildSymbolicOperand(inst, src);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVNTI operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movntpd_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create the semantics */
          auto node = triton::api.buildSymbolicOperand(inst, src);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVNTPD operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movntps_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create the semantics */
          auto node = triton::api.buildSymbolicOperand(inst, src);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVNTPS operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movntq_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create the semantics */
          auto node = triton::api.buildSymbolicOperand(inst, src);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVNTQ operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movshdup_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> bytes;

          bytes.push_back(triton::ast::extract(127, 96, op2));
          bytes.push_back(triton::ast::extract(127, 96, op2));
          bytes.push_back(triton::ast::extract(63, 32, op2));
          bytes.push_back(triton::ast::extract(63, 32, op2));

          auto node = triton::ast::concat(bytes);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVSHDUP operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movsldup_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> bytes;

          bytes.push_back(triton::ast::extract(95, 64, op2));
          bytes.push_back(triton::ast::extract(95, 64, op2));
          bytes.push_back(triton::ast::extract(31, 0, op2));
          bytes.push_back(triton::ast::extract(31, 0, op2));

          auto node = triton::ast::concat(bytes);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVSLDUP operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movq_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          triton::ast::AbstractNode* node = nullptr;

          /* when operating on MMX technology registers and memory locations */
          if (dst.getBitSize() == QWORD_SIZE_BIT && src.getBitSize() == QWORD_SIZE_BIT)
            node = op2;

          /* when source and destination operands are XMM registers */
          else if (dst.getBitSize() == DQWORD_SIZE_BIT && src.getBitSize() == DQWORD_SIZE_BIT)
            node = triton::ast::concat(
                    triton::ast::extract(DQWORD_SIZE_BIT-1, QWORD_SIZE_BIT, op1),
                    triton::ast::extract(QWORD_SIZE_BIT-1, 0, op2)
                   );

          /* when source operand is XMM register and destination operand is memory location */
          else if (dst.getBitSize() < src.getBitSize())
            node = triton::ast::extract(QWORD_SIZE_BIT-1, 0, op2);

          /* when source operand is memory location and destination operand is XMM register */
          else if (dst.getBitSize() > src.getBitSize())
            node = triton::ast::zx(QWORD_SIZE_BIT, op2);

          /* Invalid operation */
          else
            throw std::runtime_error("triton::arch::x86::semantics::movq_s(): Invalid operation.");

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVQ operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movq2dq_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::zx(QWORD_SIZE_BIT, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVQ2DQ operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movsb_s(triton::arch::Instruction& inst) {
          auto& dst    = inst.operands[0];
          auto& src    = inst.operands[1];
          auto  index1 = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
          auto  index2 = triton::arch::OperandWrapper(TRITON_X86_REG_SI.getParent());
          auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);
          auto op2 = triton::api.buildSymbolicOperand(inst, index1);
          auto op3 = triton::api.buildSymbolicOperand(inst, index2);
          auto op4 = triton::api.buildSymbolicOperand(inst, df);

          /* Create the semantics */
          auto node1 = op1;
          auto node2 = triton::ast::ite(
                         triton::ast::equal(op4, triton::ast::bvfalse()),
                         triton::ast::bvadd(op2, triton::ast::bv(BYTE_SIZE, index1.getBitSize())),
                         triton::ast::bvsub(op2, triton::ast::bv(BYTE_SIZE, index1.getBitSize()))
                       );
          auto node3 = triton::ast::ite(
                         triton::ast::equal(op4, triton::ast::bvfalse()),
                         triton::ast::bvadd(op3, triton::ast::bv(BYTE_SIZE, index2.getBitSize())),
                         triton::ast::bvsub(op3, triton::ast::bv(BYTE_SIZE, index2.getBitSize()))
                       );

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicExpression(inst, node1, dst, "MOVSB operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, index1, "Index (DI) operation");
          auto expr3 = triton::api.createSymbolicExpression(inst, node3, index2, "Index (SI) operation");

          /* Spread taint */
          expr1->isTainted = triton::api.taintAssignment(dst, src);
          expr2->isTainted = triton::api.taintUnion(index1, index1);
          expr3->isTainted = triton::api.taintUnion(index2, index2);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movsd_s(triton::arch::Instruction& inst) {
          auto& dst    = inst.operands[0];
          auto& src    = inst.operands[1];
          auto  index1 = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
          auto  index2 = triton::arch::OperandWrapper(TRITON_X86_REG_SI.getParent());
          auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);
          auto op2 = triton::api.buildSymbolicOperand(inst, index1);
          auto op3 = triton::api.buildSymbolicOperand(inst, index2);
          auto op4 = triton::api.buildSymbolicOperand(inst, df);

          /* Create the semantics */
          auto node1 = op1;
          auto node2 = triton::ast::ite(
                         triton::ast::equal(op4, triton::ast::bvfalse()),
                         triton::ast::bvadd(op2, triton::ast::bv(DWORD_SIZE, index1.getBitSize())),
                         triton::ast::bvsub(op2, triton::ast::bv(DWORD_SIZE, index1.getBitSize()))
                       );
          auto node3 = triton::ast::ite(
                         triton::ast::equal(op4, triton::ast::bvfalse()),
                         triton::ast::bvadd(op3, triton::ast::bv(DWORD_SIZE, index2.getBitSize())),
                         triton::ast::bvsub(op3, triton::ast::bv(DWORD_SIZE, index2.getBitSize()))
                       );

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicExpression(inst, node1, dst, "MOVSD operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, index1, "Index (DI) operation");
          auto expr3 = triton::api.createSymbolicExpression(inst, node3, index2, "Index (SI) operation");

          /* Spread taint */
          expr1->isTainted = triton::api.taintAssignment(dst, src);
          expr2->isTainted = triton::api.taintUnion(index1, index1);
          expr3->isTainted = triton::api.taintUnion(index2, index2);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movupd_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create the semantics */
          auto node = triton::api.buildSymbolicOperand(inst, src);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVUPD operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movups_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create the semantics */
          auto node = triton::api.buildSymbolicOperand(inst, src);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVUPS operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movsq_s(triton::arch::Instruction& inst) {
          auto& dst    = inst.operands[0];
          auto& src    = inst.operands[1];
          auto  index1 = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
          auto  index2 = triton::arch::OperandWrapper(TRITON_X86_REG_SI.getParent());
          auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);
          auto op2 = triton::api.buildSymbolicOperand(inst, index1);
          auto op3 = triton::api.buildSymbolicOperand(inst, index2);
          auto op4 = triton::api.buildSymbolicOperand(inst, df);

          /* Create the semantics */
          auto node1 = op1;
          auto node2 = triton::ast::ite(
                         triton::ast::equal(op4, triton::ast::bvfalse()),
                         triton::ast::bvadd(op2, triton::ast::bv(QWORD_SIZE, index1.getBitSize())),
                         triton::ast::bvsub(op2, triton::ast::bv(QWORD_SIZE, index1.getBitSize()))
                       );
          auto node3 = triton::ast::ite(
                         triton::ast::equal(op4, triton::ast::bvfalse()),
                         triton::ast::bvadd(op3, triton::ast::bv(QWORD_SIZE, index2.getBitSize())),
                         triton::ast::bvsub(op3, triton::ast::bv(QWORD_SIZE, index2.getBitSize()))
                       );

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicExpression(inst, node1, dst, "MOVSQ operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, index1, "Index (DI) operation");
          auto expr3 = triton::api.createSymbolicExpression(inst, node3, index2, "Index (SI) operation");

          /* Spread taint */
          expr1->isTainted = triton::api.taintAssignment(dst, src);
          expr2->isTainted = triton::api.taintUnion(index1, index1);
          expr3->isTainted = triton::api.taintUnion(index2, index2);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movsw_s(triton::arch::Instruction& inst) {
          auto& dst    = inst.operands[0];
          auto& src    = inst.operands[1];
          auto  index1 = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
          auto  index2 = triton::arch::OperandWrapper(TRITON_X86_REG_SI.getParent());
          auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);
          auto op2 = triton::api.buildSymbolicOperand(inst, index1);
          auto op3 = triton::api.buildSymbolicOperand(inst, index2);
          auto op4 = triton::api.buildSymbolicOperand(inst, df);

          /* Create the semantics */
          auto node1 = op1;
          auto node2 = triton::ast::ite(
                         triton::ast::equal(op4, triton::ast::bvfalse()),
                         triton::ast::bvadd(op2, triton::ast::bv(WORD_SIZE, index1.getBitSize())),
                         triton::ast::bvsub(op2, triton::ast::bv(WORD_SIZE, index1.getBitSize()))
                       );
          auto node3 = triton::ast::ite(
                         triton::ast::equal(op4, triton::ast::bvfalse()),
                         triton::ast::bvadd(op3, triton::ast::bv(WORD_SIZE, index2.getBitSize())),
                         triton::ast::bvsub(op3, triton::ast::bv(WORD_SIZE, index2.getBitSize()))
                       );

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicExpression(inst, node1, dst, "MOVSW operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, index1, "Index (DI) operation");
          auto expr3 = triton::api.createSymbolicExpression(inst, node3, index2, "Index (SI) operation");

          /* Spread taint */
          expr1->isTainted = triton::api.taintAssignment(dst, src);
          expr2->isTainted = triton::api.taintUnion(index1, index1);
          expr3->isTainted = triton::api.taintUnion(index2, index2);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movsx_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::sx(dst.getBitSize() - src.getBitSize(), op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVSX operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movsxd_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::sx(dst.getBitSize() - src.getBitSize(), op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVSXD operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void movzx_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::zx(dst.getBitSize() - src.getBitSize(), op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MOVZX operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void mul_s(triton::arch::Instruction& inst) {
          auto& src2 = inst.operands[0];

          switch (src2.getSize()) {

            /* AX = AL * r/m8 */
            case BYTE_SIZE: {
              auto dst  = triton::arch::OperandWrapper(TRITON_X86_REG_AX);
              auto src1 = triton::arch::OperandWrapper(TRITON_X86_REG_AL);
              /* Create symbolic operands */
              auto op1 = triton::api.buildSymbolicOperand(inst, src1);
              auto op2 = triton::api.buildSymbolicOperand(inst, src2);
              /* Create the semantics */
              auto node = triton::ast::bvmul(triton::ast::zx(BYTE_SIZE_BIT, op1), triton::ast::zx(BYTE_SIZE_BIT, op2));
              /* Create symbolic expression */
              auto expr = triton::api.createSymbolicExpression(inst, node, dst, "MUL operation");
              /* Apply the taint */
              expr->isTainted = triton::api.taintUnion(dst, src2);
              /* Upate symbolic flags */
              auto ah = triton::ast::extract((WORD_SIZE_BIT - 1), BYTE_SIZE_BIT, node);
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
              auto op1 = triton::api.buildSymbolicOperand(inst, src1);
              auto op2 = triton::api.buildSymbolicOperand(inst, src2);
              /* Create the semantics */
              auto node = triton::ast::bvmul(triton::ast::zx(WORD_SIZE_BIT, op1), triton::ast::zx(WORD_SIZE_BIT, op2));
              /* Create symbolic expression for ax */
              auto ax = triton::ast::extract((WORD_SIZE_BIT - 1), 0, node);
              auto expr1 = triton::api.createSymbolicExpression(inst, ax, dst1, "MUL operation");
              /* Apply the taint */
              expr1->isTainted = triton::api.taintUnion(dst1, src2);
              /* Create symbolic expression for dx */
              auto dx = triton::ast::extract((DWORD_SIZE_BIT - 1), WORD_SIZE_BIT, node);
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
              auto op1 = triton::api.buildSymbolicOperand(inst, src1);
              auto op2 = triton::api.buildSymbolicOperand(inst, src2);
              /* Create the semantics */
              auto node = triton::ast::bvmul(triton::ast::zx(DWORD_SIZE_BIT, op1), triton::ast::zx(DWORD_SIZE_BIT, op2));
              /* Create symbolic expression for eax */
              auto eax = triton::ast::extract((DWORD_SIZE_BIT - 1), 0, node);
              auto expr1 = triton::api.createSymbolicExpression(inst, eax, dst1, "MUL operation");
              /* Apply the taint */
              expr1->isTainted = triton::api.taintUnion(dst1, src2);
              /* Create symbolic expression for edx */
              auto edx = triton::ast::extract((QWORD_SIZE_BIT - 1), DWORD_SIZE_BIT, node);
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
              auto op1 = triton::api.buildSymbolicOperand(inst, src1);
              auto op2 = triton::api.buildSymbolicOperand(inst, src2);
              /* Create the semantics */
              auto node = triton::ast::bvmul(triton::ast::zx(QWORD_SIZE_BIT, op1), triton::ast::zx(QWORD_SIZE_BIT, op2));
              /* Create symbolic expression for eax */
              auto rax = triton::ast::extract((QWORD_SIZE_BIT - 1), 0, node);
              auto expr1 = triton::api.createSymbolicExpression(inst, rax, dst1, "MUL operation");
              /* Apply the taint */
              expr1->isTainted = triton::api.taintUnion(dst1, src2);
              /* Create symbolic expression for rdx */
              auto rdx = triton::ast::extract((DQWORD_SIZE_BIT - 1), QWORD_SIZE_BIT, node);
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
          auto& src = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::bvneg(op1);

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
          auto& src = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::bvnot(op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, src, "NOT operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(src, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void or_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::bvor(op1, op2);

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
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::bvor(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "ORPD operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void orps_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::bvor(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "ORPS operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void paddb_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> packed;

          switch (dst.getBitSize()) {

            /* XMM */
            case DQWORD_SIZE_BIT:
              packed.push_back(triton::ast::bvadd(triton::ast::extract(127, 120, op1), triton::ast::extract(127, 120, op2)));
              packed.push_back(triton::ast::bvadd(triton::ast::extract(119, 112, op1), triton::ast::extract(119, 112, op2)));
              packed.push_back(triton::ast::bvadd(triton::ast::extract(111, 104, op1), triton::ast::extract(111, 104, op2)));
              packed.push_back(triton::ast::bvadd(triton::ast::extract(103, 96,  op1), triton::ast::extract(103, 96,  op2)));
              packed.push_back(triton::ast::bvadd(triton::ast::extract(95,  88,  op1), triton::ast::extract(95,  88,  op2)));
              packed.push_back(triton::ast::bvadd(triton::ast::extract(87,  80,  op1), triton::ast::extract(87,  80,  op2)));
              packed.push_back(triton::ast::bvadd(triton::ast::extract(79,  72,  op1), triton::ast::extract(79,  72,  op2)));
              packed.push_back(triton::ast::bvadd(triton::ast::extract(71,  64,  op1), triton::ast::extract(71,  64,  op2)));

            /* MMX */
            case QWORD_SIZE_BIT:
              packed.push_back(triton::ast::bvadd(triton::ast::extract(63,  56,  op1), triton::ast::extract(63,  56,  op2)));
              packed.push_back(triton::ast::bvadd(triton::ast::extract(55,  48,  op1), triton::ast::extract(55,  48,  op2)));
              packed.push_back(triton::ast::bvadd(triton::ast::extract(47,  40,  op1), triton::ast::extract(47,  40,  op2)));
              packed.push_back(triton::ast::bvadd(triton::ast::extract(39,  32,  op1), triton::ast::extract(39,  32,  op2)));
              packed.push_back(triton::ast::bvadd(triton::ast::extract(31,  24,  op1), triton::ast::extract(31,  24,  op2)));
              packed.push_back(triton::ast::bvadd(triton::ast::extract(23,  16,  op1), triton::ast::extract(23,  16,  op2)));
              packed.push_back(triton::ast::bvadd(triton::ast::extract(15,  8,   op1), triton::ast::extract(15,  8,   op2)));
              packed.push_back(triton::ast::bvadd(triton::ast::extract(7,   0,   op1), triton::ast::extract(7,   0,   op2)));
              break;

            default:
              throw std::runtime_error("triton::arch::x86::semantics::paddb_s(): Invalid operand size.");

          }

          auto node = triton::ast::concat(packed);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PADDB operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void paddd_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> packed;

          switch (dst.getBitSize()) {

            /* XMM */
            case DQWORD_SIZE_BIT:
              packed.push_back(triton::ast::bvadd(triton::ast::extract(127, 96, op1), triton::ast::extract(127, 96, op2)));
              packed.push_back(triton::ast::bvadd(triton::ast::extract(95,  64, op1), triton::ast::extract(95,  64, op2)));

            /* MMX */
            case QWORD_SIZE_BIT:
              packed.push_back(triton::ast::bvadd(triton::ast::extract(63,  32, op1), triton::ast::extract(63,  32, op2)));
              packed.push_back(triton::ast::bvadd(triton::ast::extract(31,  0,  op1), triton::ast::extract(31,  0,  op2)));
              break;

            default:
              throw std::runtime_error("triton::arch::x86::semantics::paddd_s(): Invalid operand size.");

          }

          auto node = triton::ast::concat(packed);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PADDD operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void paddq_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> packed;

          switch (dst.getBitSize()) {

            /* XMM */
            case DQWORD_SIZE_BIT:
              packed.push_back(triton::ast::bvadd(triton::ast::extract(127, 64, op1), triton::ast::extract(127, 64, op2)));

            /* MMX */
            case QWORD_SIZE_BIT:
              packed.push_back(triton::ast::bvadd(triton::ast::extract(63,  0,  op1), triton::ast::extract(63,  0,  op2)));
              break;

            default:
              throw std::runtime_error("triton::arch::x86::semantics::paddq_s(): Invalid operand size.");

          }

          auto node = triton::ast::concat(packed);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PADDQ operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void paddw_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> packed;

          switch (dst.getBitSize()) {

            /* XMM */
            case DQWORD_SIZE_BIT:
              packed.push_back(triton::ast::bvadd(triton::ast::extract(127, 112, op1), triton::ast::extract(127, 112, op2)));
              packed.push_back(triton::ast::bvadd(triton::ast::extract(111, 96,  op1), triton::ast::extract(111, 96,  op2)));
              packed.push_back(triton::ast::bvadd(triton::ast::extract(95,  80,  op1), triton::ast::extract(95,  80,  op2)));
              packed.push_back(triton::ast::bvadd(triton::ast::extract(79,  64,  op1), triton::ast::extract(79,  64,  op2)));

            /* MMX */
            case QWORD_SIZE_BIT:
              packed.push_back(triton::ast::bvadd(triton::ast::extract(63,  48,  op1), triton::ast::extract(63,  48,  op2)));
              packed.push_back(triton::ast::bvadd(triton::ast::extract(47,  32,  op1), triton::ast::extract(47,  32,  op2)));
              packed.push_back(triton::ast::bvadd(triton::ast::extract(31,  16,  op1), triton::ast::extract(31,  16,  op2)));
              packed.push_back(triton::ast::bvadd(triton::ast::extract(15,  0,   op1), triton::ast::extract(15,  0,   op2)));
              break;

            default:
              throw std::runtime_error("triton::arch::x86::semantics::paddw_s(): Invalid operand size.");

          }

          auto node = triton::ast::concat(packed);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PADDW operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pand_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::bvand(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PAND operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pandn_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::bvand(triton::ast::bvnot(op1), op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PANDN operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pcmpeqb_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode *> pck;
          for (triton::uint32 index = 0; index < dst.getSize(); index++) {
            uint32 high = (dst.getBitSize() - 1) - (index * BYTE_SIZE_BIT);
            uint32 low  = (dst.getBitSize() - BYTE_SIZE_BIT) - (index * BYTE_SIZE_BIT);
            pck.push_back(triton::ast::ite(
                            triton::ast::equal(
                              triton::ast::extract(high, low, op1),
                              triton::ast::extract(high, low, op2)),
                            triton::ast::bv(0xff, BYTE_SIZE_BIT),
                            triton::ast::bv(0x00, BYTE_SIZE_BIT))
                         );
          }

          auto node = triton::ast::concat(pck);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PCMPEQB operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pcmpeqd_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode *> pck;
          for (triton::uint32 index = 0; index < dst.getSize() / DWORD_SIZE; index++) {
            uint32 high = (dst.getBitSize() - 1) - (index * DWORD_SIZE_BIT);
            uint32 low  = (dst.getBitSize() - DWORD_SIZE_BIT) - (index * DWORD_SIZE_BIT);
            pck.push_back(triton::ast::ite(
                            triton::ast::equal(
                              triton::ast::extract(high, low, op1),
                              triton::ast::extract(high, low, op2)),
                            triton::ast::bv(0xffffffff, DWORD_SIZE_BIT),
                            triton::ast::bv(0x00000000, DWORD_SIZE_BIT))
                         );
          }

          auto node = triton::ast::concat(pck);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PCMPEQD operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pcmpeqw_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode *> pck;
          for (triton::uint32 index = 0; index < dst.getSize() / WORD_SIZE; index++) {
            uint32 high = (dst.getBitSize() - 1) - (index * WORD_SIZE_BIT);
            uint32 low  = (dst.getBitSize() - WORD_SIZE_BIT) - (index * WORD_SIZE_BIT);
            pck.push_back(triton::ast::ite(
                            triton::ast::equal(
                              triton::ast::extract(high, low, op1),
                              triton::ast::extract(high, low, op2)),
                            triton::ast::bv(0xffff, WORD_SIZE_BIT),
                            triton::ast::bv(0x0000, WORD_SIZE_BIT))
                         );
          }

          auto node = triton::ast::concat(pck);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PCMPEQW operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pcmpgtb_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode *> pck;
          for (triton::uint32 index = 0; index < dst.getSize(); index++) {
            uint32 high = (dst.getBitSize() - 1) - (index * BYTE_SIZE_BIT);
            uint32 low  = (dst.getBitSize() - BYTE_SIZE_BIT) - (index * BYTE_SIZE_BIT);
            pck.push_back(triton::ast::ite(
                            triton::ast::bvsgt(
                              triton::ast::extract(high, low, op1),
                              triton::ast::extract(high, low, op2)),
                            triton::ast::bv(0xff, BYTE_SIZE_BIT),
                            triton::ast::bv(0x00, BYTE_SIZE_BIT))
                         );
          }

          auto node = triton::ast::concat(pck);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PCMPGTB operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pcmpgtd_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode *> pck;
          for (triton::uint32 index = 0; index < dst.getSize() / DWORD_SIZE; index++) {
            uint32 high = (dst.getBitSize() - 1) - (index * DWORD_SIZE_BIT);
            uint32 low  = (dst.getBitSize() - DWORD_SIZE_BIT) - (index * DWORD_SIZE_BIT);
            pck.push_back(triton::ast::ite(
                            triton::ast::bvsgt(
                              triton::ast::extract(high, low, op1),
                              triton::ast::extract(high, low, op2)),
                            triton::ast::bv(0xffffffff, DWORD_SIZE_BIT),
                            triton::ast::bv(0x00000000, DWORD_SIZE_BIT))
                         );
          }

          auto node = triton::ast::concat(pck);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PCMPGTD operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pcmpgtw_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode *> pck;
          for (triton::uint32 index = 0; index < dst.getSize() / WORD_SIZE; index++) {
            uint32 high = (dst.getBitSize() - 1) - (index * WORD_SIZE_BIT);
            uint32 low  = (dst.getBitSize() - WORD_SIZE_BIT) - (index * WORD_SIZE_BIT);
            pck.push_back(triton::ast::ite(
                            triton::ast::bvsgt(
                              triton::ast::extract(high, low, op1),
                              triton::ast::extract(high, low, op2)),
                            triton::ast::bv(0xffff, WORD_SIZE_BIT),
                            triton::ast::bv(0x0000, WORD_SIZE_BIT))
                         );
          }

          auto node = triton::ast::concat(pck);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PCMPGTW operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pmaxsb_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode *> pck;
          for (triton::uint32 index = 0; index < dst.getSize(); index++) {
            uint32 high = (dst.getBitSize() - 1) - (index * BYTE_SIZE_BIT);
            uint32 low  = (dst.getBitSize() - BYTE_SIZE_BIT) - (index * BYTE_SIZE_BIT);
            pck.push_back(triton::ast::ite(
                            triton::ast::bvsle(
                              triton::ast::extract(high, low, op1),
                              triton::ast::extract(high, low, op2)),
                            triton::ast::extract(high, low, op2),
                            triton::ast::extract(high, low, op1))
                         );
          }

          auto node = triton::ast::concat(pck);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PMAXSB operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pmaxsd_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode *> pck;
          for (triton::uint32 index = 0; index < dst.getSize() / DWORD_SIZE; index++) {
            uint32 high = (dst.getBitSize() - 1) - (index * DWORD_SIZE_BIT);
            uint32 low  = (dst.getBitSize() - DWORD_SIZE_BIT) - (index * DWORD_SIZE_BIT);
            pck.push_back(triton::ast::ite(
                            triton::ast::bvsle(
                              triton::ast::extract(high, low, op1),
                              triton::ast::extract(high, low, op2)),
                            triton::ast::extract(high, low, op2),
                            triton::ast::extract(high, low, op1))
                         );
          }

          auto node = triton::ast::concat(pck);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PMAXSD operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pmaxsw_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode *> pck;
          for (triton::uint32 index = 0; index < dst.getSize() / WORD_SIZE; index++) {
            uint32 high = (dst.getBitSize() - 1) - (index * WORD_SIZE_BIT);
            uint32 low  = (dst.getBitSize() - WORD_SIZE_BIT) - (index * WORD_SIZE_BIT);
            pck.push_back(triton::ast::ite(
                            triton::ast::bvsle(
                              triton::ast::extract(high, low, op1),
                              triton::ast::extract(high, low, op2)),
                            triton::ast::extract(high, low, op2),
                            triton::ast::extract(high, low, op1))
                         );
          }

          auto node = triton::ast::concat(pck);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PMAXSW operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pmaxub_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode *> pck;
          for (triton::uint32 index = 0; index < dst.getSize(); index++) {
            uint32 high = (dst.getBitSize() - 1) - (index * BYTE_SIZE_BIT);
            uint32 low  = (dst.getBitSize() - BYTE_SIZE_BIT) - (index * BYTE_SIZE_BIT);
            pck.push_back(triton::ast::ite(
                            triton::ast::bvule(
                              triton::ast::extract(high, low, op1),
                              triton::ast::extract(high, low, op2)),
                            triton::ast::extract(high, low, op2),
                            triton::ast::extract(high, low, op1))
                         );
          }

          auto node = triton::ast::concat(pck);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PMAXUB operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pmaxud_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode *> pck;
          for (triton::uint32 index = 0; index < dst.getSize() / DWORD_SIZE; index++) {
            uint32 high = (dst.getBitSize() - 1) - (index * DWORD_SIZE_BIT);
            uint32 low  = (dst.getBitSize() - DWORD_SIZE_BIT) - (index * DWORD_SIZE_BIT);
            pck.push_back(triton::ast::ite(
                            triton::ast::bvule(
                              triton::ast::extract(high, low, op1),
                              triton::ast::extract(high, low, op2)),
                            triton::ast::extract(high, low, op2),
                            triton::ast::extract(high, low, op1))
                         );
          }

          auto node = triton::ast::concat(pck);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PMAXUD operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pmaxuw_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode *> pck;
          for (triton::uint32 index = 0; index < dst.getSize() / WORD_SIZE; index++) {
            uint32 high = (dst.getBitSize() - 1) - (index * WORD_SIZE_BIT);
            uint32 low  = (dst.getBitSize() - WORD_SIZE_BIT) - (index * WORD_SIZE_BIT);
            pck.push_back(triton::ast::ite(
                            triton::ast::bvule(
                              triton::ast::extract(high, low, op1),
                              triton::ast::extract(high, low, op2)),
                            triton::ast::extract(high, low, op2),
                            triton::ast::extract(high, low, op1))
                         );
          }

          auto node = triton::ast::concat(pck);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PMAXUW operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pminsb_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode *> pck;
          for (triton::uint32 index = 0; index < dst.getSize(); index++) {
            uint32 high = (dst.getBitSize() - 1) - (index * BYTE_SIZE_BIT);
            uint32 low  = (dst.getBitSize() - BYTE_SIZE_BIT) - (index * BYTE_SIZE_BIT);
            pck.push_back(triton::ast::ite(
                            triton::ast::bvsge(
                              triton::ast::extract(high, low, op1),
                              triton::ast::extract(high, low, op2)),
                            triton::ast::extract(high, low, op2),
                            triton::ast::extract(high, low, op1))
                         );
          }

          auto node = triton::ast::concat(pck);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PMINSB operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pminsd_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode *> pck;
          for (triton::uint32 index = 0; index < dst.getSize() / DWORD_SIZE; index++) {
            uint32 high = (dst.getBitSize() - 1) - (index * DWORD_SIZE_BIT);
            uint32 low  = (dst.getBitSize() - DWORD_SIZE_BIT) - (index * DWORD_SIZE_BIT);
            pck.push_back(triton::ast::ite(
                            triton::ast::bvsge(
                              triton::ast::extract(high, low, op1),
                              triton::ast::extract(high, low, op2)),
                            triton::ast::extract(high, low, op2),
                            triton::ast::extract(high, low, op1))
                         );
          }

          auto node = triton::ast::concat(pck);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PMINSD operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pminsw_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode *> pck;
          for (triton::uint32 index = 0; index < dst.getSize() / WORD_SIZE; index++) {
            uint32 high = (dst.getBitSize() - 1) - (index * WORD_SIZE_BIT);
            uint32 low  = (dst.getBitSize() - WORD_SIZE_BIT) - (index * WORD_SIZE_BIT);
            pck.push_back(triton::ast::ite(
                            triton::ast::bvsge(
                              triton::ast::extract(high, low, op1),
                              triton::ast::extract(high, low, op2)),
                            triton::ast::extract(high, low, op2),
                            triton::ast::extract(high, low, op1))
                         );
          }

          auto node = triton::ast::concat(pck);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PMINSW operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pminub_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode *> pck;
          for (triton::uint32 index = 0; index < dst.getSize(); index++) {
            uint32 high = (dst.getBitSize() - 1) - (index * BYTE_SIZE_BIT);
            uint32 low  = (dst.getBitSize() - BYTE_SIZE_BIT) - (index * BYTE_SIZE_BIT);
            pck.push_back(triton::ast::ite(
                            triton::ast::bvuge(
                              triton::ast::extract(high, low, op1),
                              triton::ast::extract(high, low, op2)),
                            triton::ast::extract(high, low, op2),
                            triton::ast::extract(high, low, op1))
                         );
          }

          auto node = triton::ast::concat(pck);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PMINUB operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pminud_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode *> pck;
          for (triton::uint32 index = 0; index < dst.getSize() / DWORD_SIZE; index++) {
            uint32 high = (dst.getBitSize() - 1) - (index * DWORD_SIZE_BIT);
            uint32 low  = (dst.getBitSize() - DWORD_SIZE_BIT) - (index * DWORD_SIZE_BIT);
            pck.push_back(triton::ast::ite(
                            triton::ast::bvuge(
                              triton::ast::extract(high, low, op1),
                              triton::ast::extract(high, low, op2)),
                            triton::ast::extract(high, low, op2),
                            triton::ast::extract(high, low, op1))
                         );
          }

          auto node = triton::ast::concat(pck);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PMINUD operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pminuw_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode *> pck;
          for (triton::uint32 index = 0; index < dst.getSize() / WORD_SIZE; index++) {
            uint32 high = (dst.getBitSize() - 1) - (index * WORD_SIZE_BIT);
            uint32 low  = (dst.getBitSize() - WORD_SIZE_BIT) - (index * WORD_SIZE_BIT);
            pck.push_back(triton::ast::ite(
                            triton::ast::bvuge(
                              triton::ast::extract(high, low, op1),
                              triton::ast::extract(high, low, op2)),
                            triton::ast::extract(high, low, op2),
                            triton::ast::extract(high, low, op1))
                         );
          }

          auto node = triton::ast::concat(pck);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PMINUW operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pmovmskb_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode *> mskb;
          switch (src.getSize()) {
            case DQWORD_SIZE:
              mskb.push_back(triton::ast::extract(127, 127, op2));
              mskb.push_back(triton::ast::extract(119, 119, op2));
              mskb.push_back(triton::ast::extract(111, 111, op2));
              mskb.push_back(triton::ast::extract(103, 103, op2));
              mskb.push_back(triton::ast::extract(95,  95,  op2));
              mskb.push_back(triton::ast::extract(87,  87,  op2));
              mskb.push_back(triton::ast::extract(79,  79,  op2));
              mskb.push_back(triton::ast::extract(71,  71,  op2));

            case QWORD_SIZE:
              mskb.push_back(triton::ast::extract(63,  63,  op2));
              mskb.push_back(triton::ast::extract(55,  55,  op2));
              mskb.push_back(triton::ast::extract(47,  47,  op2));
              mskb.push_back(triton::ast::extract(39,  39,  op2));
              mskb.push_back(triton::ast::extract(31,  31,  op2));
              mskb.push_back(triton::ast::extract(23,  23,  op2));
              mskb.push_back(triton::ast::extract(15,  15,  op2));
              mskb.push_back(triton::ast::extract(7,   7,   op2));
          }

          auto node = triton::ast::zx(dst.getBitSize() - mskb.size(), triton::ast::concat(mskb));

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PMOVMSKB operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pop_s(triton::arch::Instruction& inst) {
          auto  stack      = TRITON_X86_REG_SP.getParent();
          auto  stackValue = triton::api.getRegisterValue(stack).convert_to<triton::__uint>();
          auto& dst        = inst.operands[0];
          auto  src        = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue, stack.getSize()));

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = op1;

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "POP operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Create the semantics - side effect */
          alignAddStack_s(inst, src.getSize());

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void popal_s(triton::arch::Instruction& inst) {
          auto stack      = TRITON_X86_REG_SP.getParent();
          auto stackValue = triton::api.getRegisterValue(stack).convert_to<triton::__uint>();
          auto dst1       = triton::arch::OperandWrapper(TRITON_X86_REG_EDI);
          auto dst2       = triton::arch::OperandWrapper(TRITON_X86_REG_ESI);
          auto dst3       = triton::arch::OperandWrapper(TRITON_X86_REG_EBP);
          auto dst4       = triton::arch::OperandWrapper(TRITON_X86_REG_ESP);
          auto dst5       = triton::arch::OperandWrapper(TRITON_X86_REG_EBX);
          auto dst6       = triton::arch::OperandWrapper(TRITON_X86_REG_EDX);
          auto dst7       = triton::arch::OperandWrapper(TRITON_X86_REG_ECX);
          auto dst8       = triton::arch::OperandWrapper(TRITON_X86_REG_EAX);
          auto src1       = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue+(stack.getSize() * 0), stack.getSize()));
          auto src2       = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue+(stack.getSize() * 1), stack.getSize()));
          auto src3       = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue+(stack.getSize() * 2), stack.getSize()));
          auto src4       = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue+(stack.getSize() * 3), stack.getSize()));
          auto src5       = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue+(stack.getSize() * 4), stack.getSize()));
          auto src6       = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue+(stack.getSize() * 5), stack.getSize()));
          auto src7       = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue+(stack.getSize() * 6), stack.getSize()));
          auto src8       = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue+(stack.getSize() * 7), stack.getSize()));

          /* Create symbolic operands and semantics */
          auto node1 = triton::api.buildSymbolicOperand(inst, src1);
          auto node2 = triton::api.buildSymbolicOperand(inst, src2);
          auto node3 = triton::api.buildSymbolicOperand(inst, src3);
          auto node4 = triton::api.buildSymbolicOperand(inst, src4);
          auto node5 = triton::api.buildSymbolicOperand(inst, src5);
          auto node6 = triton::api.buildSymbolicOperand(inst, src6);
          auto node7 = triton::api.buildSymbolicOperand(inst, src7);
          auto node8 = triton::api.buildSymbolicOperand(inst, src8);

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicExpression(inst, node1, dst1, "POPAL EDI operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, dst2, "POPAL ESI operation");
          auto expr3 = triton::api.createSymbolicExpression(inst, node3, dst3, "POPAL EBP operation");
          auto expr4 = triton::api.createSymbolicExpression(inst, node4, dst4, "POPAL ESP operation");
          auto expr5 = triton::api.createSymbolicExpression(inst, node5, dst5, "POPAL EBX operation");
          auto expr6 = triton::api.createSymbolicExpression(inst, node6, dst6, "POPAL EDX operation");
          auto expr7 = triton::api.createSymbolicExpression(inst, node7, dst7, "POPAL ECX operation");
          auto expr8 = triton::api.createSymbolicExpression(inst, node8, dst8, "POPAL EAX operation");

          /* Spread taint */
          expr1->isTainted = triton::api.taintAssignment(dst1, src1);
          expr2->isTainted = triton::api.taintAssignment(dst2, src2);
          expr3->isTainted = triton::api.taintAssignment(dst3, src3);
          expr4->isTainted = triton::api.taintAssignment(dst4, src4);
          expr5->isTainted = triton::api.taintAssignment(dst5, src5);
          expr6->isTainted = triton::api.taintAssignment(dst6, src6);
          expr7->isTainted = triton::api.taintAssignment(dst7, src7);
          expr8->isTainted = triton::api.taintAssignment(dst8, src8);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void popfd_s(triton::arch::Instruction& inst) {
          auto  stack      = TRITON_X86_REG_SP.getParent();
          auto  stackValue = triton::api.getRegisterValue(stack).convert_to<triton::__uint>();
          auto  dst1       = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
          auto  dst2       = triton::arch::OperandWrapper(TRITON_X86_REG_PF);
          auto  dst3       = triton::arch::OperandWrapper(TRITON_X86_REG_AF);
          auto  dst4       = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
          auto  dst5       = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto  dst6       = triton::arch::OperandWrapper(TRITON_X86_REG_TF);
          auto  dst7       = triton::arch::OperandWrapper(TRITON_X86_REG_IF);
          auto  dst8       = triton::arch::OperandWrapper(TRITON_X86_REG_DF);
          auto  dst9       = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
          auto  src        = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue, stack.getSize()));

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node1 = triton::ast::extract(0,  0,  op1);
          auto node2 = triton::ast::extract(2,  2,  op1);
          auto node3 = triton::ast::extract(4,  4,  op1);
          auto node4 = triton::ast::extract(6,  6,  op1);
          auto node5 = triton::ast::extract(7,  7,  op1);
          auto node6 = triton::ast::extract(8,  8,  op1);
          auto node7 = triton::ast::bvtrue(); /* TODO IF and IOPL */
          auto node8 = triton::ast::extract(10, 10, op1);
          auto node9 = triton::ast::extract(11, 11, op1);

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicFlagExpression(inst, node1, dst1.getRegister(), "POPFD CF operation");
          auto expr2 = triton::api.createSymbolicFlagExpression(inst, node2, dst2.getRegister(), "POPFD PF operation");
          auto expr3 = triton::api.createSymbolicFlagExpression(inst, node3, dst3.getRegister(), "POPFD AF operation");
          auto expr4 = triton::api.createSymbolicFlagExpression(inst, node4, dst4.getRegister(), "POPFD ZF operation");
          auto expr5 = triton::api.createSymbolicFlagExpression(inst, node5, dst5.getRegister(), "POPFD SF operation");
          auto expr6 = triton::api.createSymbolicFlagExpression(inst, node6, dst6.getRegister(), "POPFD TF operation");
          auto expr7 = triton::api.createSymbolicFlagExpression(inst, node7, dst7.getRegister(), "POPFD IF operation");
          auto expr8 = triton::api.createSymbolicFlagExpression(inst, node8, dst8.getRegister(), "POPFD DF operation");
          auto expr9 = triton::api.createSymbolicFlagExpression(inst, node9, dst9.getRegister(), "POPFD OF operation");

          /* Spread taint */
          expr1->isTainted = triton::api.taintAssignment(dst1, src);
          expr2->isTainted = triton::api.taintAssignment(dst2, src);
          expr3->isTainted = triton::api.taintAssignment(dst3, src);
          expr4->isTainted = triton::api.taintAssignment(dst4, src);
          expr5->isTainted = triton::api.taintAssignment(dst5, src);
          expr6->isTainted = triton::api.taintAssignment(dst6, src);
          expr7->isTainted = triton::api.taintAssignment(dst7, src);
          expr8->isTainted = triton::api.taintAssignment(dst8, src);
          expr9->isTainted = triton::api.taintAssignment(dst9, src);

          /* Create the semantics - side effect */
          alignAddStack_s(inst, src.getSize());

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void popfq_s(triton::arch::Instruction& inst) {
          auto  stack      = TRITON_X86_REG_SP.getParent();
          auto  stackValue = triton::api.getRegisterValue(stack).convert_to<triton::__uint>();
          auto  dst1       = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
          auto  dst2       = triton::arch::OperandWrapper(TRITON_X86_REG_PF);
          auto  dst3       = triton::arch::OperandWrapper(TRITON_X86_REG_AF);
          auto  dst4       = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
          auto  dst5       = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto  dst6       = triton::arch::OperandWrapper(TRITON_X86_REG_TF);
          auto  dst7       = triton::arch::OperandWrapper(TRITON_X86_REG_IF);
          auto  dst8       = triton::arch::OperandWrapper(TRITON_X86_REG_DF);
          auto  dst9       = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
          auto  src        = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue, stack.getSize()));

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node1 = triton::ast::extract(0,  0,  op1);
          auto node2 = triton::ast::extract(2,  2,  op1);
          auto node3 = triton::ast::extract(4,  4,  op1);
          auto node4 = triton::ast::extract(6,  6,  op1);
          auto node5 = triton::ast::extract(7,  7,  op1);
          auto node6 = triton::ast::extract(8,  8,  op1);
          auto node7 = triton::ast::bvtrue(); /* TODO IF and IOPL */
          auto node8 = triton::ast::extract(10, 10, op1);
          auto node9 = triton::ast::extract(11, 11, op1);

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicFlagExpression(inst, node1, dst1.getRegister(), "POPFQ CF operation");
          auto expr2 = triton::api.createSymbolicFlagExpression(inst, node2, dst2.getRegister(), "POPFQ PF operation");
          auto expr3 = triton::api.createSymbolicFlagExpression(inst, node3, dst3.getRegister(), "POPFQ AF operation");
          auto expr4 = triton::api.createSymbolicFlagExpression(inst, node4, dst4.getRegister(), "POPFQ ZF operation");
          auto expr5 = triton::api.createSymbolicFlagExpression(inst, node5, dst5.getRegister(), "POPFQ SF operation");
          auto expr6 = triton::api.createSymbolicFlagExpression(inst, node6, dst6.getRegister(), "POPFQ TF operation");
          auto expr7 = triton::api.createSymbolicFlagExpression(inst, node7, dst7.getRegister(), "POPFQ IF operation");
          auto expr8 = triton::api.createSymbolicFlagExpression(inst, node8, dst8.getRegister(), "POPFQ DF operation");
          auto expr9 = triton::api.createSymbolicFlagExpression(inst, node9, dst9.getRegister(), "POPFQ OF operation");

          /* Spread taint */
          expr1->isTainted = triton::api.taintAssignment(dst1, src);
          expr2->isTainted = triton::api.taintAssignment(dst2, src);
          expr3->isTainted = triton::api.taintAssignment(dst3, src);
          expr4->isTainted = triton::api.taintAssignment(dst4, src);
          expr5->isTainted = triton::api.taintAssignment(dst5, src);
          expr6->isTainted = triton::api.taintAssignment(dst6, src);
          expr7->isTainted = triton::api.taintAssignment(dst7, src);
          expr8->isTainted = triton::api.taintAssignment(dst8, src);
          expr9->isTainted = triton::api.taintAssignment(dst9, src);

          /* Create the semantics - side effect */
          alignAddStack_s(inst, src.getSize());

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void por_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::bvor(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "POR operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void prefetchx_s(triton::arch::Instruction& inst) {
          auto& src = inst.operands[0];

          /* Only specify that the instruction performs an implicit memory read */
          triton::api.buildSymbolicOperand(inst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pshufd_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];
          auto& ord = inst.operands[2];

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, ord);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> pack;
          pack.push_back(
            triton::ast::extract(31, 0,
              triton::ast::bvlshr(
                op2,
                triton::ast::bvmul(
                  triton::ast::zx(DQWORD_SIZE_BIT-2, triton::ast::extract(7, 6, op3)),
                  triton::ast::bv(32, DQWORD_SIZE_BIT)
                )
              )
            )
          );
          pack.push_back(
            triton::ast::extract(31, 0,
              triton::ast::bvlshr(
                op2,
                triton::ast::bvmul(
                  triton::ast::zx(DQWORD_SIZE_BIT-2, triton::ast::extract(5, 4, op3)),
                  triton::ast::bv(32, DQWORD_SIZE_BIT)
                )
              )
            )
          );
          pack.push_back(
            triton::ast::extract(31, 0,
              triton::ast::bvlshr(
                op2,
                triton::ast::bvmul(
                  triton::ast::zx(DQWORD_SIZE_BIT-2, triton::ast::extract(3, 2, op3)),
                  triton::ast::bv(32, DQWORD_SIZE_BIT)
                )
              )
            )
          );
          pack.push_back(
            triton::ast::extract(31, 0,
              triton::ast::bvlshr(
                op2,
                triton::ast::bvmul(
                  triton::ast::zx(DQWORD_SIZE_BIT-2, triton::ast::extract(1, 0, op3)),
                  triton::ast::bv(32, DQWORD_SIZE_BIT)
                )
              )
            )
          );

          auto node = triton::ast::concat(pack);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PSHUFD operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pshufhw_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];
          auto& ord = inst.operands[2];

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, ord);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> pack;
          pack.push_back(
            triton::ast::extract(79, 64,
              triton::ast::bvlshr(
                op2,
                triton::ast::bvmul(
                  triton::ast::zx(DQWORD_SIZE_BIT-2, triton::ast::extract(7, 6, op3)),
                  triton::ast::bv(16, DQWORD_SIZE_BIT)
                )
              )
            )
          );
          pack.push_back(
            triton::ast::extract(79, 64,
              triton::ast::bvlshr(
                op2,
                triton::ast::bvmul(
                  triton::ast::zx(DQWORD_SIZE_BIT-2, triton::ast::extract(5, 4, op3)),
                  triton::ast::bv(16, DQWORD_SIZE_BIT)
                )
              )
            )
          );
          pack.push_back(
            triton::ast::extract(79, 64,
              triton::ast::bvlshr(
                op2,
                triton::ast::bvmul(
                  triton::ast::zx(DQWORD_SIZE_BIT-2, triton::ast::extract(3, 2, op3)),
                  triton::ast::bv(16, DQWORD_SIZE_BIT)
                )
              )
            )
          );
          pack.push_back(
            triton::ast::extract(79, 64,
              triton::ast::bvlshr(
                op2,
                triton::ast::bvmul(
                  triton::ast::zx(DQWORD_SIZE_BIT-2, triton::ast::extract(1, 0, op3)),
                  triton::ast::bv(16, DQWORD_SIZE_BIT)
                )
              )
            )
          );
          pack.push_back(
            triton::ast::extract(63, 0, op2)
          );

          auto node = triton::ast::concat(pack);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PSHUFHW operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pshuflw_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];
          auto& ord = inst.operands[2];

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, ord);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> pack;
          pack.push_back(
            triton::ast::extract(127, 64, op2)
          );
          pack.push_back(
            triton::ast::extract(15, 0,
              triton::ast::bvlshr(
                op2,
                triton::ast::bvmul(
                  triton::ast::zx(DQWORD_SIZE_BIT-2, triton::ast::extract(7, 6, op3)),
                  triton::ast::bv(16, DQWORD_SIZE_BIT)
                )
              )
            )
          );
          pack.push_back(
            triton::ast::extract(15, 0,
              triton::ast::bvlshr(
                op2,
                triton::ast::bvmul(
                  triton::ast::zx(DQWORD_SIZE_BIT-2, triton::ast::extract(5, 4, op3)),
                  triton::ast::bv(16, DQWORD_SIZE_BIT)
                )
              )
            )
          );
          pack.push_back(
            triton::ast::extract(15, 0,
              triton::ast::bvlshr(
                op2,
                triton::ast::bvmul(
                  triton::ast::zx(DQWORD_SIZE_BIT-2, triton::ast::extract(3, 2, op3)),
                  triton::ast::bv(16, DQWORD_SIZE_BIT)
                )
              )
            )
          );
          pack.push_back(
            triton::ast::extract(15, 0,
              triton::ast::bvlshr(
                op2,
                triton::ast::bvmul(
                  triton::ast::zx(DQWORD_SIZE_BIT-2, triton::ast::extract(1, 0, op3)),
                  triton::ast::bv(16, DQWORD_SIZE_BIT)
                )
              )
            )
          );

          auto node = triton::ast::concat(pack);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PSHUFLW operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pshufw_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];
          auto& ord = inst.operands[2];

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, ord);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> pack;
          pack.push_back(
            triton::ast::extract(15, 0,
              triton::ast::bvlshr(
                op2,
                triton::ast::bvmul(
                  triton::ast::zx(QWORD_SIZE_BIT-2, triton::ast::extract(7, 6, op3)),
                  triton::ast::bv(16, QWORD_SIZE_BIT)
                )
              )
            )
          );
          pack.push_back(
            triton::ast::extract(15, 0,
              triton::ast::bvlshr(
                op2,
                triton::ast::bvmul(
                  triton::ast::zx(QWORD_SIZE_BIT-2, triton::ast::extract(5, 4, op3)),
                  triton::ast::bv(16, QWORD_SIZE_BIT)
                )
              )
            )
          );
          pack.push_back(
            triton::ast::extract(15, 0,
              triton::ast::bvlshr(
                op2,
                triton::ast::bvmul(
                  triton::ast::zx(QWORD_SIZE_BIT-2, triton::ast::extract(3, 2, op3)),
                  triton::ast::bv(16, QWORD_SIZE_BIT)
                )
              )
            )
          );
          pack.push_back(
            triton::ast::extract(15, 0,
              triton::ast::bvlshr(
                op2,
                triton::ast::bvmul(
                  triton::ast::zx(QWORD_SIZE_BIT-2, triton::ast::extract(1, 0, op3)),
                  triton::ast::bv(16, QWORD_SIZE_BIT)
                )
              )
            )
          );

          auto node = triton::ast::concat(pack);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PSHUFW operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pslldq_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::ast::zx(dst.getBitSize() - src.getBitSize(), triton::api.buildSymbolicOperand(inst, src));

          /* Create the semantics */
          auto node = triton::ast::bvshl(
                        op1,
                        triton::ast::bvmul(
                          triton::ast::ite(
                            triton::ast::bvuge(op2, triton::ast::bv(WORD_SIZE_BIT, dst.getBitSize())),
                            triton::ast::bv(WORD_SIZE_BIT, dst.getBitSize()),
                            op2
                          ),
                          triton::ast::bv(QWORD_SIZE, dst.getBitSize())
                        )
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PSLLDQ operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void psrldq_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::ast::zx(dst.getBitSize() - src.getBitSize(), triton::api.buildSymbolicOperand(inst, src));

          /* Create the semantics */
          auto node = triton::ast::bvlshr(
                        op1,
                        triton::ast::bvmul(
                          triton::ast::ite(
                            triton::ast::bvuge(op2, triton::ast::bv(WORD_SIZE_BIT, dst.getBitSize())),
                            triton::ast::bv(WORD_SIZE_BIT, dst.getBitSize()),
                            op2
                          ),
                          triton::ast::bv(QWORD_SIZE, dst.getBitSize())
                        )
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PSRLDQ operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void psubb_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> packed;

          switch (dst.getBitSize()) {

            /* XMM */
            case DQWORD_SIZE_BIT:
              packed.push_back(triton::ast::bvsub(triton::ast::extract(127, 120, op1), triton::ast::extract(127, 120, op2)));
              packed.push_back(triton::ast::bvsub(triton::ast::extract(119, 112, op1), triton::ast::extract(119, 112, op2)));
              packed.push_back(triton::ast::bvsub(triton::ast::extract(111, 104, op1), triton::ast::extract(111, 104, op2)));
              packed.push_back(triton::ast::bvsub(triton::ast::extract(103, 96,  op1), triton::ast::extract(103, 96,  op2)));
              packed.push_back(triton::ast::bvsub(triton::ast::extract(95,  88,  op1), triton::ast::extract(95,  88,  op2)));
              packed.push_back(triton::ast::bvsub(triton::ast::extract(87,  80,  op1), triton::ast::extract(87,  80,  op2)));
              packed.push_back(triton::ast::bvsub(triton::ast::extract(79,  72,  op1), triton::ast::extract(79,  72,  op2)));
              packed.push_back(triton::ast::bvsub(triton::ast::extract(71,  64,  op1), triton::ast::extract(71,  64,  op2)));

            /* MMX */
            case QWORD_SIZE_BIT:
              packed.push_back(triton::ast::bvsub(triton::ast::extract(63,  56,  op1), triton::ast::extract(63,  56,  op2)));
              packed.push_back(triton::ast::bvsub(triton::ast::extract(55,  48,  op1), triton::ast::extract(55,  48,  op2)));
              packed.push_back(triton::ast::bvsub(triton::ast::extract(47,  40,  op1), triton::ast::extract(47,  40,  op2)));
              packed.push_back(triton::ast::bvsub(triton::ast::extract(39,  32,  op1), triton::ast::extract(39,  32,  op2)));
              packed.push_back(triton::ast::bvsub(triton::ast::extract(31,  24,  op1), triton::ast::extract(31,  24,  op2)));
              packed.push_back(triton::ast::bvsub(triton::ast::extract(23,  16,  op1), triton::ast::extract(23,  16,  op2)));
              packed.push_back(triton::ast::bvsub(triton::ast::extract(15,  8,   op1), triton::ast::extract(15,  8,   op2)));
              packed.push_back(triton::ast::bvsub(triton::ast::extract(7,   0,   op1), triton::ast::extract(7,   0,   op2)));
              break;

            default:
              throw std::runtime_error("triton::arch::x86::semantics::psubb_s(): Invalid operand size.");

          }

          auto node = triton::ast::concat(packed);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PSUBB operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void psubd_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> packed;

          switch (dst.getBitSize()) {

            /* XMM */
            case DQWORD_SIZE_BIT:
              packed.push_back(triton::ast::bvsub(triton::ast::extract(127, 96, op1), triton::ast::extract(127, 96, op2)));
              packed.push_back(triton::ast::bvsub(triton::ast::extract(95,  64, op1), triton::ast::extract(95,  64, op2)));

            /* MMX */
            case QWORD_SIZE_BIT:
              packed.push_back(triton::ast::bvsub(triton::ast::extract(63,  32, op1), triton::ast::extract(63,  32, op2)));
              packed.push_back(triton::ast::bvsub(triton::ast::extract(31,  0,  op1), triton::ast::extract(31,  0,  op2)));
              break;

            default:
              throw std::runtime_error("triton::arch::x86::semantics::psubd_s(): Invalid operand size.");

          }

          auto node = triton::ast::concat(packed);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PSUBD operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void psubq_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> packed;

          switch (dst.getBitSize()) {

            /* XMM */
            case DQWORD_SIZE_BIT:
              packed.push_back(triton::ast::bvsub(triton::ast::extract(127, 64, op1), triton::ast::extract(127, 64, op2)));

            /* MMX */
            case QWORD_SIZE_BIT:
              packed.push_back(triton::ast::bvsub(triton::ast::extract(63,  0,  op1), triton::ast::extract(63,  0,  op2)));
              break;

            default:
              throw std::runtime_error("triton::arch::x86::semantics::psubq_s(): Invalid operand size.");

          }

          auto node = triton::ast::concat(packed);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PSUBQ operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void psubw_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> packed;

          switch (dst.getBitSize()) {

            /* XMM */
            case DQWORD_SIZE_BIT:
              packed.push_back(triton::ast::bvsub(triton::ast::extract(127, 112, op1), triton::ast::extract(127, 112, op2)));
              packed.push_back(triton::ast::bvsub(triton::ast::extract(111, 96,  op1), triton::ast::extract(111, 96,  op2)));
              packed.push_back(triton::ast::bvsub(triton::ast::extract(95,  80,  op1), triton::ast::extract(95,  80,  op2)));
              packed.push_back(triton::ast::bvsub(triton::ast::extract(79,  64,  op1), triton::ast::extract(79,  64,  op2)));

            /* MMX */
            case QWORD_SIZE_BIT:
              packed.push_back(triton::ast::bvsub(triton::ast::extract(63,  48,  op1), triton::ast::extract(63,  48,  op2)));
              packed.push_back(triton::ast::bvsub(triton::ast::extract(47,  32,  op1), triton::ast::extract(47,  32,  op2)));
              packed.push_back(triton::ast::bvsub(triton::ast::extract(31,  16,  op1), triton::ast::extract(31,  16,  op2)));
              packed.push_back(triton::ast::bvsub(triton::ast::extract(15,  0,   op1), triton::ast::extract(15,  0,   op2)));
              break;

            default:
              throw std::runtime_error("triton::arch::x86::semantics::psubw_s(): Invalid operand size.");

          }

          auto node = triton::ast::concat(packed);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PSUBW operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void ptest_s(triton::arch::Instruction& inst) {
          auto& src1 = inst.operands[0];
          auto& src2 = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src1);
          auto op2 = triton::api.buildSymbolicOperand(inst, src2);

          /* Create the semantics */
          auto node1 = triton::ast::bvand(op1, op2);
          auto node2 = triton::ast::bvand(op1, triton::ast::bvnot(op2));

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicVolatileExpression(inst, node1, "PTEST operation");
          auto expr2 = triton::api.createSymbolicVolatileExpression(inst, node2, "PTEST operation");

          /* Spread taint */
          expr1->isTainted = triton::api.isTainted(src1) | triton::api.isTainted(src2);
          expr2->isTainted = triton::api.isTainted(src1) | triton::api.isTainted(src2);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::clearFlag_s(inst, TRITON_X86_REG_AF, "Clears adjust flag");
          triton::arch::x86::semantics::cfPtest_s(inst, expr2, src1, true);
          triton::arch::x86::semantics::clearFlag_s(inst, TRITON_X86_REG_OF, "Clears overflow flag");
          triton::arch::x86::semantics::clearFlag_s(inst, TRITON_X86_REG_PF, "Clears parity flag");
          triton::arch::x86::semantics::clearFlag_s(inst, TRITON_X86_REG_SF, "Clears sign flag");
          triton::arch::x86::semantics::zf_s(inst, expr1, src1, true);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void punpckhbw_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> unpack;

          switch (dst.getBitSize()) {

            /* MMX */
            case QWORD_SIZE_BIT:
              unpack.push_back(triton::ast::extract(63, 56, op2));
              unpack.push_back(triton::ast::extract(63, 56, op1));
              unpack.push_back(triton::ast::extract(55, 48, op2));
              unpack.push_back(triton::ast::extract(55, 48, op1));
              unpack.push_back(triton::ast::extract(47, 40, op2));
              unpack.push_back(triton::ast::extract(55, 40, op1));
              unpack.push_back(triton::ast::extract(39, 32, op2));
              unpack.push_back(triton::ast::extract(39, 32, op1));
              break;

            /* XMM */
            case DQWORD_SIZE_BIT:
              unpack.push_back(triton::ast::extract(127, 120, op2));
              unpack.push_back(triton::ast::extract(127, 120, op1));
              unpack.push_back(triton::ast::extract(119, 112, op2));
              unpack.push_back(triton::ast::extract(119, 112, op1));
              unpack.push_back(triton::ast::extract(111, 104, op2));
              unpack.push_back(triton::ast::extract(111, 104, op1));
              unpack.push_back(triton::ast::extract(103, 96,  op2));
              unpack.push_back(triton::ast::extract(103, 96,  op1));
              unpack.push_back(triton::ast::extract(95,  88,  op2));
              unpack.push_back(triton::ast::extract(95,  88,  op1));
              unpack.push_back(triton::ast::extract(87,  80,  op2));
              unpack.push_back(triton::ast::extract(87,  80,  op1));
              unpack.push_back(triton::ast::extract(79,  72,  op2));
              unpack.push_back(triton::ast::extract(79,  72,  op1));
              unpack.push_back(triton::ast::extract(71,  64,  op2));
              unpack.push_back(triton::ast::extract(71,  64,  op1));
              break;

            default:
              throw std::runtime_error("triton::arch::x86::semantics::punpckhbw_s(): Invalid operand size.");
          }

          auto node = triton::ast::concat(unpack);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PUNPCKHBW operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void punpckhdq_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> unpack;

          switch (dst.getBitSize()) {

            /* MMX */
            case QWORD_SIZE_BIT:
              unpack.push_back(triton::ast::extract(63, 32, op2));
              unpack.push_back(triton::ast::extract(63, 32, op1));
              break;

            /* XMM */
            case DQWORD_SIZE_BIT:
              unpack.push_back(triton::ast::extract(127, 96, op2));
              unpack.push_back(triton::ast::extract(127, 96, op1));
              unpack.push_back(triton::ast::extract(95,  64, op2));
              unpack.push_back(triton::ast::extract(95,  64, op1));
              break;

            default:
              throw std::runtime_error("triton::arch::x86::semantics::punpckhdq_s(): Invalid operand size.");
          }

          auto node = triton::ast::concat(unpack);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PUNPCKHDQ operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void punpckhqdq_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> unpack;

          switch (dst.getBitSize()) {

            /* XMM */
            case DQWORD_SIZE_BIT:
              unpack.push_back(triton::ast::extract(127, 64, op2));
              unpack.push_back(triton::ast::extract(127, 64, op1));
              break;

            default:
              throw std::runtime_error("triton::arch::x86::semantics::punpckhqdq_s(): Invalid operand size.");
          }

          auto node = triton::ast::concat(unpack);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PUNPCKHQDQ operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void punpckhwd_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> unpack;

          switch (dst.getBitSize()) {

            /* MMX */
            case QWORD_SIZE_BIT:
              unpack.push_back(triton::ast::extract(63, 48, op2));
              unpack.push_back(triton::ast::extract(63, 48, op1));
              unpack.push_back(triton::ast::extract(47, 32, op2));
              unpack.push_back(triton::ast::extract(47, 32, op1));
              break;

            /* XMM */
            case DQWORD_SIZE_BIT:
              unpack.push_back(triton::ast::extract(127, 112, op2));
              unpack.push_back(triton::ast::extract(127, 112, op1));
              unpack.push_back(triton::ast::extract(111, 96,  op2));
              unpack.push_back(triton::ast::extract(111, 96,  op1));
              unpack.push_back(triton::ast::extract(95,  80,  op2));
              unpack.push_back(triton::ast::extract(95,  80,  op1));
              unpack.push_back(triton::ast::extract(79,  64,  op2));
              unpack.push_back(triton::ast::extract(79,  64,  op1));
              break;

            default:
              throw std::runtime_error("triton::arch::x86::semantics::punpckhwd_s(): Invalid operand size.");
          }

          auto node = triton::ast::concat(unpack);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PUNPCKHWD operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void punpcklbw_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> unpack;

          switch (dst.getBitSize()) {

            /* MMX */
            case QWORD_SIZE_BIT:
              unpack.push_back(triton::ast::extract(31, 24, op2));
              unpack.push_back(triton::ast::extract(31, 24, op1));
              unpack.push_back(triton::ast::extract(23, 16, op2));
              unpack.push_back(triton::ast::extract(23, 16, op1));
              unpack.push_back(triton::ast::extract(15, 8,  op2));
              unpack.push_back(triton::ast::extract(15, 8,  op1));
              unpack.push_back(triton::ast::extract(7,  0,  op2));
              unpack.push_back(triton::ast::extract(7,  0,  op1));
              break;

            /* XMM */
            case DQWORD_SIZE_BIT:
              unpack.push_back(triton::ast::extract(63, 56, op2));
              unpack.push_back(triton::ast::extract(63, 56, op1));
              unpack.push_back(triton::ast::extract(55, 48, op2));
              unpack.push_back(triton::ast::extract(55, 48, op1));
              unpack.push_back(triton::ast::extract(47, 40, op2));
              unpack.push_back(triton::ast::extract(47, 40, op1));
              unpack.push_back(triton::ast::extract(39, 32, op2));
              unpack.push_back(triton::ast::extract(39, 32, op1));
              unpack.push_back(triton::ast::extract(31, 24, op2));
              unpack.push_back(triton::ast::extract(31, 24, op1));
              unpack.push_back(triton::ast::extract(23, 16, op2));
              unpack.push_back(triton::ast::extract(23, 16, op1));
              unpack.push_back(triton::ast::extract(15, 8,  op2));
              unpack.push_back(triton::ast::extract(15, 8,  op1));
              unpack.push_back(triton::ast::extract(7,  0,  op2));
              unpack.push_back(triton::ast::extract(7,  0,  op1));
              break;

            default:
              throw std::runtime_error("triton::arch::x86::semantics::punpcklbw_s(): Invalid operand size.");
          }

          auto node = triton::ast::concat(unpack);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PUNPCKLBW operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void punpckldq_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> unpack;

          switch (dst.getBitSize()) {

            /* MMX */
            case QWORD_SIZE_BIT:
              unpack.push_back(triton::ast::extract(31, 0, op2));
              unpack.push_back(triton::ast::extract(31, 0, op1));
              break;

            /* XMM */
            case DQWORD_SIZE_BIT:
              unpack.push_back(triton::ast::extract(63, 32, op2));
              unpack.push_back(triton::ast::extract(63, 32, op1));
              unpack.push_back(triton::ast::extract(31, 0,  op2));
              unpack.push_back(triton::ast::extract(31, 0,  op1));
              break;

            default:
              throw std::runtime_error("triton::arch::x86::semantics::punpckldq_s(): Invalid operand size.");
          }

          auto node = triton::ast::concat(unpack);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PUNPCKLDQ operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void punpcklqdq_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> unpack;

          switch (dst.getBitSize()) {

            /* XMM */
            case DQWORD_SIZE_BIT:
              unpack.push_back(triton::ast::extract(63, 0, op2));
              unpack.push_back(triton::ast::extract(63, 0, op1));
              break;

            default:
              throw std::runtime_error("triton::arch::x86::semantics::punpcklqdq_s(): Invalid operand size.");
          }

          auto node = triton::ast::concat(unpack);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PUNPCKLQDQ operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void punpcklwd_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> unpack;

          switch (dst.getBitSize()) {

            /* MMX */
            case QWORD_SIZE_BIT:
              unpack.push_back(triton::ast::extract(31, 16, op2));
              unpack.push_back(triton::ast::extract(31, 16, op1));
              unpack.push_back(triton::ast::extract(15, 0,  op2));
              unpack.push_back(triton::ast::extract(15, 0,  op1));
              break;

            /* XMM */
            case DQWORD_SIZE_BIT:
              unpack.push_back(triton::ast::extract(63, 48, op2));
              unpack.push_back(triton::ast::extract(63, 48, op1));
              unpack.push_back(triton::ast::extract(47, 32, op2));
              unpack.push_back(triton::ast::extract(47, 32, op1));
              unpack.push_back(triton::ast::extract(31, 16, op2));
              unpack.push_back(triton::ast::extract(31, 16, op1));
              unpack.push_back(triton::ast::extract(15, 0,  op2));
              unpack.push_back(triton::ast::extract(15, 0,  op1));
              break;

            default:
              throw std::runtime_error("triton::arch::x86::semantics::punpcklwd_s(): Invalid operand size.");
          }

          auto node = triton::ast::concat(unpack);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PUNPCKLWD operation");

          /* Apply the taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void push_s(triton::arch::Instruction& inst) {
          auto stack = TRITON_X86_REG_SP.getParent();

          /* Create the semantics - side effect */
          alignSubStack_s(inst, stack.getSize());

          auto  stackValue = triton::api.getRegisterValue(stack).convert_to<triton::__uint>();
          auto  dst        = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue, stack.getSize()));
          auto& src        = inst.operands[0];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::zx(dst.getBitSize() - src.getBitSize(), op1);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PUSH operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pushal_s(triton::arch::Instruction& inst) {
          auto stack      = TRITON_X86_REG_SP.getParent();
          auto stackValue = triton::api.getRegisterValue(stack).convert_to<triton::__uint>();
          auto dst1       = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue-(stack.getSize() * 1), stack.getSize()));
          auto dst2       = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue-(stack.getSize() * 2), stack.getSize()));
          auto dst3       = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue-(stack.getSize() * 3), stack.getSize()));
          auto dst4       = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue-(stack.getSize() * 4), stack.getSize()));
          auto dst5       = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue-(stack.getSize() * 5), stack.getSize()));
          auto dst6       = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue-(stack.getSize() * 6), stack.getSize()));
          auto dst7       = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue-(stack.getSize() * 7), stack.getSize()));
          auto dst8       = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue-(stack.getSize() * 8), stack.getSize()));
          auto src1       = triton::arch::OperandWrapper(TRITON_X86_REG_EAX);
          auto src2       = triton::arch::OperandWrapper(TRITON_X86_REG_ECX);
          auto src3       = triton::arch::OperandWrapper(TRITON_X86_REG_EDX);
          auto src4       = triton::arch::OperandWrapper(TRITON_X86_REG_EBX);
          auto src5       = triton::arch::OperandWrapper(TRITON_X86_REG_ESP);
          auto src6       = triton::arch::OperandWrapper(TRITON_X86_REG_EBP);
          auto src7       = triton::arch::OperandWrapper(TRITON_X86_REG_ESI);
          auto src8       = triton::arch::OperandWrapper(TRITON_X86_REG_EDI);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src1);
          auto op2 = triton::api.buildSymbolicOperand(inst, src2);
          auto op3 = triton::api.buildSymbolicOperand(inst, src3);
          auto op4 = triton::api.buildSymbolicOperand(inst, src4);
          auto op5 = triton::api.buildSymbolicOperand(inst, src5);
          auto op6 = triton::api.buildSymbolicOperand(inst, src6);
          auto op7 = triton::api.buildSymbolicOperand(inst, src7);
          auto op8 = triton::api.buildSymbolicOperand(inst, src8);

          /* Create the semantics */
          auto node1 = triton::ast::zx(dst1.getBitSize() - src1.getBitSize(), op1);
          auto node2 = triton::ast::zx(dst2.getBitSize() - src2.getBitSize(), op2);
          auto node3 = triton::ast::zx(dst3.getBitSize() - src3.getBitSize(), op3);
          auto node4 = triton::ast::zx(dst4.getBitSize() - src4.getBitSize(), op4);
          auto node5 = triton::ast::zx(dst5.getBitSize() - src5.getBitSize(), op5);
          auto node6 = triton::ast::zx(dst6.getBitSize() - src6.getBitSize(), op6);
          auto node7 = triton::ast::zx(dst7.getBitSize() - src7.getBitSize(), op7);
          auto node8 = triton::ast::zx(dst8.getBitSize() - src8.getBitSize(), op8);

          /* Create symbolic expression */
          alignSubStack_s(inst, 32);
          auto expr1 = triton::api.createSymbolicExpression(inst, node1, dst1, "PUSHAL EAX operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, dst2, "PUSHAL ECX operation");
          auto expr3 = triton::api.createSymbolicExpression(inst, node3, dst3, "PUSHAL EDX operation");
          auto expr4 = triton::api.createSymbolicExpression(inst, node4, dst4, "PUSHAL EBX operation");
          auto expr5 = triton::api.createSymbolicExpression(inst, node5, dst5, "PUSHAL ESP operation");
          auto expr6 = triton::api.createSymbolicExpression(inst, node6, dst6, "PUSHAL EBP operation");
          auto expr7 = triton::api.createSymbolicExpression(inst, node7, dst7, "PUSHAL ESI operation");
          auto expr8 = triton::api.createSymbolicExpression(inst, node8, dst8, "PUSHAL EDI operation");

          /* Spread taint */
          expr1->isTainted = triton::api.taintAssignment(dst1, src1);
          expr2->isTainted = triton::api.taintAssignment(dst2, src2);
          expr3->isTainted = triton::api.taintAssignment(dst3, src3);
          expr4->isTainted = triton::api.taintAssignment(dst4, src4);
          expr5->isTainted = triton::api.taintAssignment(dst5, src5);
          expr6->isTainted = triton::api.taintAssignment(dst6, src6);
          expr7->isTainted = triton::api.taintAssignment(dst7, src7);
          expr8->isTainted = triton::api.taintAssignment(dst8, src8);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pushfd_s(triton::arch::Instruction& inst) {
          auto stack = TRITON_X86_REG_SP.getParent();

          /* Create the semantics - side effect */
          alignSubStack_s(inst, stack.getSize());

          auto stackValue = triton::api.getRegisterValue(stack).convert_to<triton::__uint>();
          auto dst        = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue, stack.getSize()));
          auto src1       = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
          auto src2       = triton::arch::OperandWrapper(TRITON_X86_REG_PF);
          auto src3       = triton::arch::OperandWrapper(TRITON_X86_REG_AF);
          auto src4       = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
          auto src5       = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto src6       = triton::arch::OperandWrapper(TRITON_X86_REG_TF);
          auto src7       = triton::arch::OperandWrapper(TRITON_X86_REG_IF);
          auto src8       = triton::arch::OperandWrapper(TRITON_X86_REG_DF);
          auto src9       = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src1);
          auto op2 = triton::api.buildSymbolicOperand(inst, src2);
          auto op3 = triton::api.buildSymbolicOperand(inst, src3);
          auto op4 = triton::api.buildSymbolicOperand(inst, src4);
          auto op5 = triton::api.buildSymbolicOperand(inst, src5);
          auto op6 = triton::api.buildSymbolicOperand(inst, src6);
          auto op7 = triton::api.buildSymbolicOperand(inst, src7);
          auto op8 = triton::api.buildSymbolicOperand(inst, src8);
          auto op9 = triton::api.buildSymbolicOperand(inst, src9);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> eflags;
          eflags.push_back(op9);
          eflags.push_back(op8);
          eflags.push_back(op7);
          eflags.push_back(op6);
          eflags.push_back(op5);
          eflags.push_back(op4);
          eflags.push_back(triton::ast::bvfalse()); /* Reserved */
          eflags.push_back(op3);
          eflags.push_back(triton::ast::bvfalse()); /* Reserved */
          eflags.push_back(op2);
          eflags.push_back(triton::ast::bvfalse()); /* Reserved */
          eflags.push_back(op1);

          auto node = triton::ast::zx(dst.getBitSize() - eflags.size(), triton::ast::concat(eflags));

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PUSHFD operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src1);
          expr->isTainted = triton::api.taintUnion(dst, src2);
          expr->isTainted = triton::api.taintUnion(dst, src3);
          expr->isTainted = triton::api.taintUnion(dst, src4);
          expr->isTainted = triton::api.taintUnion(dst, src5);
          expr->isTainted = triton::api.taintUnion(dst, src6);
          expr->isTainted = triton::api.taintUnion(dst, src7);
          expr->isTainted = triton::api.taintUnion(dst, src8);
          expr->isTainted = triton::api.taintUnion(dst, src9);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pushfq_s(triton::arch::Instruction& inst) {
          auto stack = TRITON_X86_REG_SP.getParent();

          /* Create the semantics - side effect */
          alignSubStack_s(inst, stack.getSize());

          auto stackValue = triton::api.getRegisterValue(stack).convert_to<triton::__uint>();
          auto dst        = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue, stack.getSize()));
          auto src1       = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
          auto src2       = triton::arch::OperandWrapper(TRITON_X86_REG_PF);
          auto src3       = triton::arch::OperandWrapper(TRITON_X86_REG_AF);
          auto src4       = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
          auto src5       = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto src6       = triton::arch::OperandWrapper(TRITON_X86_REG_TF);
          auto src7       = triton::arch::OperandWrapper(TRITON_X86_REG_IF);
          auto src8       = triton::arch::OperandWrapper(TRITON_X86_REG_DF);
          auto src9       = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src1);
          auto op2 = triton::api.buildSymbolicOperand(inst, src2);
          auto op3 = triton::api.buildSymbolicOperand(inst, src3);
          auto op4 = triton::api.buildSymbolicOperand(inst, src4);
          auto op5 = triton::api.buildSymbolicOperand(inst, src5);
          auto op6 = triton::api.buildSymbolicOperand(inst, src6);
          auto op7 = triton::api.buildSymbolicOperand(inst, src7);
          auto op8 = triton::api.buildSymbolicOperand(inst, src8);
          auto op9 = triton::api.buildSymbolicOperand(inst, src9);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> eflags;
          eflags.push_back(op9);
          eflags.push_back(op8);
          eflags.push_back(op7);
          eflags.push_back(op6);
          eflags.push_back(op5);
          eflags.push_back(op4);
          eflags.push_back(triton::ast::bvfalse()); /* Reserved */
          eflags.push_back(op3);
          eflags.push_back(triton::ast::bvfalse()); /* Reserved */
          eflags.push_back(op2);
          eflags.push_back(triton::ast::bvfalse()); /* Reserved */
          eflags.push_back(op1);

          auto node = triton::ast::zx(dst.getBitSize() - eflags.size(), triton::ast::concat(eflags));

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PUSHFQ operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src1);
          expr->isTainted = triton::api.taintUnion(dst, src2);
          expr->isTainted = triton::api.taintUnion(dst, src3);
          expr->isTainted = triton::api.taintUnion(dst, src4);
          expr->isTainted = triton::api.taintUnion(dst, src5);
          expr->isTainted = triton::api.taintUnion(dst, src6);
          expr->isTainted = triton::api.taintUnion(dst, src7);
          expr->isTainted = triton::api.taintUnion(dst, src8);
          expr->isTainted = triton::api.taintUnion(dst, src9);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void pxor_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::bvxor(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "PXOR operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void rcl_s(triton::arch::Instruction& inst) {
          auto& dst   = inst.operands[0];
          auto& src   = inst.operands[1];
          auto  srcCf = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          /*
           * Note that the SMT2-LIB doesn't support expression as rotate value.
           * The op2 must be the value of the concretization.
           */
          auto op2 = triton::ast::decimal(triton::api.buildSymbolicOperand(inst, src)->evaluate());
          auto op3 = triton::api.buildSymbolicOperand(inst, srcCf);

          /* Create the semantics */
          auto node1 = triton::ast::bvrol(op2, triton::ast::concat(op3, op1));

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicVolatileExpression(inst, node1, "RCL tempory operation");

          /* Spread taint */
          expr1->isTainted = triton::api.isTainted(dst) | triton::api.isTainted(src);

          /* Create the semantics */
          auto node2 = triton::ast::extract(dst.getBitSize()-1, 0, node1);

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
          auto& dst   = inst.operands[0];
          auto& src   = inst.operands[1];
          auto  srcCf = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          /*
           * Note that the SMT2-LIB doesn't support expression as rotate value.
           * The op2 must be the value of the concretization.
           */
          auto op2 = triton::ast::decimal(triton::api.buildSymbolicOperand(inst, src)->evaluate());
          auto op3 = triton::api.buildSymbolicOperand(inst, srcCf);

          /* Create the semantics */
          auto node1 = triton::ast::bvror(op2, triton::ast::concat(op3, op1));

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicVolatileExpression(inst, node1, "RCR tempory operation");

          /* Spread taint */
          expr1->isTainted = triton::api.isTainted(dst) | triton::api.isTainted(src);

          /* Create the semantics */
          auto node2 = triton::ast::extract(dst.getBitSize()-1, 0, node1);

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


        void rdtsc_s(triton::arch::Instruction& inst) {
          auto dst1 = triton::arch::OperandWrapper(TRITON_X86_REG_EDX);
          auto dst2 = triton::arch::OperandWrapper(TRITON_X86_REG_EAX);

          /* Create symbolic operands */
          auto op1 = triton::ast::bv(0, dst1.getBitSize());
          auto op2 = triton::ast::bv(triton::api.getSymbolicExpressions().size(), dst2.getBitSize());

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicExpression(inst, op1, dst1, "RDTSC EDX operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, op2, dst2, "RDTSC EAX operation");

          /* Spread taint */
          expr1->isTainted = triton::api.setTaint(dst1, triton::engines::taint::UNTAINTED);
          expr2->isTainted = triton::api.setTaint(dst2, triton::engines::taint::UNTAINTED);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void ret_s(triton::arch::Instruction& inst) {
          auto stack      = TRITON_X86_REG_SP.getParent();
          auto stackValue = triton::api.getRegisterValue(stack).convert_to<triton::__uint>();
          auto pc         = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
          auto sp         = triton::arch::OperandWrapper(inst.popMemoryAccess(stackValue, stack.getSize()));

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, sp);

          /* Create the semantics */
          auto node = op1;

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, pc, "Program Counter");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(pc, sp);

          /* Create the semantics - side effect */
          alignAddStack_s(inst, sp.getSize());

          /* Create the semantics - side effect */
          if (inst.operands.size() > 0) {
            auto offset = inst.operands[0].getImmediate();
            triton::api.buildSymbolicImmediateOperand(inst, offset);
            alignAddStack_s(inst, offset.getValue());
          }

          /* Create the path constraint */
          triton::api.addPathConstraint(expr);
        }


        void rol_s(triton::arch::Instruction& inst) {
          auto& dst   = inst.operands[0];
          auto& src   = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          /*
           * Note that the SMT2-LIB doesn't support expression as rotate value.
           * The op2 must be the value of the concretization.
           */
          auto op2 = triton::ast::decimal(triton::api.buildSymbolicOperand(inst, src)->evaluate());

          /* Create the semantics */
          auto node = triton::ast::bvrol(op2, op1);

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
          auto& dst   = inst.operands[0];
          auto& src   = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          /*
           * Note that the SMT2-LIB doesn't support expression as rotate value.
           * The op2 must be the value of the concretization.
           */
          auto op2 = triton::ast::decimal(triton::api.buildSymbolicOperand(inst, src)->evaluate());

          /* Create the semantics */
          auto node = triton::ast::bvror(op2, op1);

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
          auto& dst   = inst.operands[0];
          auto& src   = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::ast::zx(dst.getBitSize() - src.getBitSize(), triton::api.buildSymbolicOperand(inst, src));

          if (dst.getBitSize() >= DWORD_SIZE_BIT)
            op2 = triton::ast::bvand(op2, triton::ast::bv(dst.getBitSize() - 1, dst.getBitSize()));

          /* Create the semantics */
          auto node = triton::ast::bvashr(op1, op2);

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
          auto& dst   = inst.operands[0];
          auto& src   = inst.operands[1];
          auto  srcCf = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::ast::zx(src.getBitSize()-1, triton::api.buildSymbolicOperand(inst, srcCf));

          /* Create the semantics */
          auto node = triton::ast::bvsub(op1, triton::ast::bvadd(op2, op3));

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


        void scasb_s(triton::arch::Instruction& inst) {
          auto& dst    = inst.operands[0];
          auto& src    = inst.operands[1];
          auto  index  = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
          auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

          /* If the REP prefix is defined, convert REP into REPE */
          if (inst.getPrefix() == triton::arch::x86::ID_PREFIX_REP)
            inst.setPrefix(triton::arch::x86::ID_PREFIX_REPE);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, index);
          auto op4 = triton::api.buildSymbolicOperand(inst, df);

          /* Create the semantics */
          auto node1 = triton::ast::bvsub(op1, op2);
          auto node2 = triton::ast::ite(
                         triton::ast::equal(op4, triton::ast::bvfalse()),
                         triton::ast::bvadd(op3, triton::ast::bv(BYTE_SIZE, index.getBitSize())),
                         triton::ast::bvsub(op3, triton::ast::bv(BYTE_SIZE, index.getBitSize()))
                       );

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicVolatileExpression(inst, node1, "SCASB operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, index, "Index operation");

          /* Spread taint */
          expr1->isTainted = triton::api.isTainted(dst) | triton::api.isTainted(src);
          expr2->isTainted = triton::api.taintUnion(index, index);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::af_s(inst, expr1, dst, op1, op2, true);
          triton::arch::x86::semantics::cfSub_s(inst, expr1, dst, op1, op2, true);
          triton::arch::x86::semantics::ofSub_s(inst, expr1, dst, op1, op2, true);
          triton::arch::x86::semantics::pf_s(inst, expr1, dst, true);
          triton::arch::x86::semantics::sf_s(inst, expr1, dst, true);
          triton::arch::x86::semantics::zf_s(inst, expr1, dst, true);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void scasd_s(triton::arch::Instruction& inst) {
          auto& dst    = inst.operands[0];
          auto& src    = inst.operands[1];
          auto  index  = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
          auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

          /* If the REP prefix is defined, convert REP into REPE */
          if (inst.getPrefix() == triton::arch::x86::ID_PREFIX_REP)
            inst.setPrefix(triton::arch::x86::ID_PREFIX_REPE);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, index);
          auto op4 = triton::api.buildSymbolicOperand(inst, df);

          /* Create the semantics */
          auto node1 = triton::ast::bvsub(op1, op2);
          auto node2 = triton::ast::ite(
                         triton::ast::equal(op4, triton::ast::bvfalse()),
                         triton::ast::bvadd(op3, triton::ast::bv(DWORD_SIZE, index.getBitSize())),
                         triton::ast::bvsub(op3, triton::ast::bv(DWORD_SIZE, index.getBitSize()))
                       );

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicVolatileExpression(inst, node1, "SCASD operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, index, "Index operation");

          /* Spread taint */
          expr1->isTainted = triton::api.isTainted(dst) | triton::api.isTainted(src);
          expr2->isTainted = triton::api.taintUnion(index, index);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::af_s(inst, expr1, dst, op1, op2, true);
          triton::arch::x86::semantics::cfSub_s(inst, expr1, dst, op1, op2, true);
          triton::arch::x86::semantics::ofSub_s(inst, expr1, dst, op1, op2, true);
          triton::arch::x86::semantics::pf_s(inst, expr1, dst, true);
          triton::arch::x86::semantics::sf_s(inst, expr1, dst, true);
          triton::arch::x86::semantics::zf_s(inst, expr1, dst, true);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void scasq_s(triton::arch::Instruction& inst) {
          auto& dst    = inst.operands[0];
          auto& src    = inst.operands[1];
          auto  index  = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
          auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

          /* If the REP prefix is defined, convert REP into REPE */
          if (inst.getPrefix() == triton::arch::x86::ID_PREFIX_REP)
            inst.setPrefix(triton::arch::x86::ID_PREFIX_REPE);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, index);
          auto op4 = triton::api.buildSymbolicOperand(inst, df);

          /* Create the semantics */
          auto node1 = triton::ast::bvsub(op1, op2);
          auto node2 = triton::ast::ite(
                         triton::ast::equal(op4, triton::ast::bvfalse()),
                         triton::ast::bvadd(op3, triton::ast::bv(QWORD_SIZE, index.getBitSize())),
                         triton::ast::bvsub(op3, triton::ast::bv(QWORD_SIZE, index.getBitSize()))
                       );

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicVolatileExpression(inst, node1, "SCASQ operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, index, "Index operation");

          /* Spread taint */
          expr1->isTainted = triton::api.isTainted(dst) | triton::api.isTainted(src);
          expr2->isTainted = triton::api.taintUnion(index, index);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::af_s(inst, expr1, dst, op1, op2, true);
          triton::arch::x86::semantics::cfSub_s(inst, expr1, dst, op1, op2, true);
          triton::arch::x86::semantics::ofSub_s(inst, expr1, dst, op1, op2, true);
          triton::arch::x86::semantics::pf_s(inst, expr1, dst, true);
          triton::arch::x86::semantics::sf_s(inst, expr1, dst, true);
          triton::arch::x86::semantics::zf_s(inst, expr1, dst, true);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void scasw_s(triton::arch::Instruction& inst) {
          auto& dst    = inst.operands[0];
          auto& src    = inst.operands[1];
          auto  index  = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
          auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

          /* If the REP prefix is defined, convert REP into REPE */
          if (inst.getPrefix() == triton::arch::x86::ID_PREFIX_REP)
            inst.setPrefix(triton::arch::x86::ID_PREFIX_REPE);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);
          auto op3 = triton::api.buildSymbolicOperand(inst, index);
          auto op4 = triton::api.buildSymbolicOperand(inst, df);

          /* Create the semantics */
          auto node1 = triton::ast::bvsub(op1, op2);
          auto node2 = triton::ast::ite(
                         triton::ast::equal(op4, triton::ast::bvfalse()),
                         triton::ast::bvadd(op3, triton::ast::bv(WORD_SIZE, index.getBitSize())),
                         triton::ast::bvsub(op3, triton::ast::bv(WORD_SIZE, index.getBitSize()))
                       );

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicVolatileExpression(inst, node1, "SCASW operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, index, "Index operation");

          /* Spread taint */
          expr1->isTainted = triton::api.isTainted(dst) | triton::api.isTainted(src);
          expr2->isTainted = triton::api.taintUnion(index, index);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::af_s(inst, expr1, dst, op1, op2, true);
          triton::arch::x86::semantics::cfSub_s(inst, expr1, dst, op1, op2, true);
          triton::arch::x86::semantics::ofSub_s(inst, expr1, dst, op1, op2, true);
          triton::arch::x86::semantics::pf_s(inst, expr1, dst, true);
          triton::arch::x86::semantics::sf_s(inst, expr1, dst, true);
          triton::arch::x86::semantics::zf_s(inst, expr1, dst, true);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void seta_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto  cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
          auto  zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, cf);
          auto op3 = triton::api.buildSymbolicOperand(inst, zf);

          /* Create the semantics */
          auto node = triton::ast::ite(
                        triton::ast::equal(
                          triton::ast::bvand(
                            triton::ast::bvnot(op2),
                            triton::ast::bvnot(op3)
                          ),
                          triton::ast::bvtrue()
                        ),
                        triton::ast::bv(1, dst.getBitSize()),
                        triton::ast::bv(0, dst.getBitSize())
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
          auto& dst = inst.operands[0];
          auto  cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, cf);

          /* Create the semantics */
          auto node = triton::ast::ite(
                        triton::ast::equal(op2, triton::ast::bvfalse()),
                        triton::ast::bv(1, dst.getBitSize()),
                        triton::ast::bv(0, dst.getBitSize())
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
          auto& dst = inst.operands[0];
          auto  cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, cf);

          /* Create the semantics */
          auto node = triton::ast::ite(
                        triton::ast::equal(op2, triton::ast::bvtrue()),
                        triton::ast::bv(1, dst.getBitSize()),
                        triton::ast::bv(0, dst.getBitSize())
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
          auto& dst = inst.operands[0];
          auto  cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
          auto  zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, cf);
          auto op3 = triton::api.buildSymbolicOperand(inst, zf);

          /* Create the semantics */
          auto node = triton::ast::ite(
                        triton::ast::equal(triton::ast::bvor(op2, op3), triton::ast::bvtrue()),
                        triton::ast::bv(1, dst.getBitSize()),
                        triton::ast::bv(0, dst.getBitSize())
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
          auto& dst = inst.operands[0];
          auto  zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, zf);

          /* Create the semantics */
          auto node = triton::ast::ite(
                        triton::ast::equal(op2, triton::ast::bvtrue()),
                        triton::ast::bv(1, dst.getBitSize()),
                        triton::ast::bv(0, dst.getBitSize())
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
          auto& dst = inst.operands[0];
          auto  sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto  of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
          auto  zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, sf);
          auto op3 = triton::api.buildSymbolicOperand(inst, of);
          auto op4 = triton::api.buildSymbolicOperand(inst, zf);

          /* Create the semantics */
          auto node = triton::ast::ite(
                        triton::ast::equal(triton::ast::bvor(triton::ast::bvxor(op2, op3), op4), triton::ast::bvfalse()),
                        triton::ast::bv(1, dst.getBitSize()),
                        triton::ast::bv(0, dst.getBitSize())
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
          auto& dst = inst.operands[0];
          auto  sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto  of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, sf);
          auto op3 = triton::api.buildSymbolicOperand(inst, of);

          /* Create the semantics */
          auto node = triton::ast::ite(
                        triton::ast::equal(op2, op3),
                        triton::ast::bv(1, dst.getBitSize()),
                        triton::ast::bv(0, dst.getBitSize())
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
          auto& dst = inst.operands[0];
          auto  sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto  of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, sf);
          auto op3 = triton::api.buildSymbolicOperand(inst, of);

          /* Create the semantics */
          auto node = triton::ast::ite(
                        triton::ast::equal(triton::ast::bvxor(op2, op3), triton::ast::bvtrue()),
                        triton::ast::bv(1, dst.getBitSize()),
                        triton::ast::bv(0, dst.getBitSize())
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
          auto& dst = inst.operands[0];
          auto  sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
          auto  of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
          auto  zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, sf);
          auto op3 = triton::api.buildSymbolicOperand(inst, of);
          auto op4 = triton::api.buildSymbolicOperand(inst, zf);

          /* Create the semantics */
          auto node = triton::ast::ite(
                        triton::ast::equal(triton::ast::bvor(triton::ast::bvxor(op2, op3), op4), triton::ast::bvtrue()),
                        triton::ast::bv(1, dst.getBitSize()),
                        triton::ast::bv(0, dst.getBitSize())
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
          auto& dst = inst.operands[0];
          auto  zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, zf);

          /* Create the semantics */
          auto node = triton::ast::ite(
                        triton::ast::equal(op2, triton::ast::bvfalse()),
                        triton::ast::bv(1, dst.getBitSize()),
                        triton::ast::bv(0, dst.getBitSize())
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
          auto& dst = inst.operands[0];
          auto  of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, of);

          /* Create the semantics */
          auto node = triton::ast::ite(
                        triton::ast::equal(op2, triton::ast::bvfalse()),
                        triton::ast::bv(1, dst.getBitSize()),
                        triton::ast::bv(0, dst.getBitSize())
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
          auto& dst = inst.operands[0];
          auto  pf  = triton::arch::OperandWrapper(TRITON_X86_REG_PF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, pf);

          /* Create the semantics */
          auto node = triton::ast::ite(
                        triton::ast::equal(op2, triton::ast::bvfalse()),
                        triton::ast::bv(1, dst.getBitSize()),
                        triton::ast::bv(0, dst.getBitSize())
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
          auto& dst = inst.operands[0];
          auto  sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, sf);

          /* Create the semantics */
          auto node = triton::ast::ite(
                        triton::ast::equal(op2, triton::ast::bvfalse()),
                        triton::ast::bv(1, dst.getBitSize()),
                        triton::ast::bv(0, dst.getBitSize())
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
          auto& dst = inst.operands[0];
          auto  of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, of);

          /* Create the semantics */
          auto node = triton::ast::ite(
                        triton::ast::equal(op2, triton::ast::bvtrue()),
                        triton::ast::bv(1, dst.getBitSize()),
                        triton::ast::bv(0, dst.getBitSize())
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
          auto& dst = inst.operands[0];
          auto  pf  = triton::arch::OperandWrapper(TRITON_X86_REG_PF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, pf);

          /* Create the semantics */
          auto node = triton::ast::ite(
                        triton::ast::equal(op2, triton::ast::bvtrue()),
                        triton::ast::bv(1, dst.getBitSize()),
                        triton::ast::bv(0, dst.getBitSize())
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
          auto& dst = inst.operands[0];
          auto  sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, sf);

          /* Create the semantics */
          auto node = triton::ast::ite(
                        triton::ast::equal(op2, triton::ast::bvtrue()),
                        triton::ast::bv(1, dst.getBitSize()),
                        triton::ast::bv(0, dst.getBitSize())
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
          auto& dst   = inst.operands[0];
          auto& src   = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::ast::zx(dst.getBitSize() - src.getBitSize(), triton::api.buildSymbolicOperand(inst, src));

          if (dst.getBitSize() >= DWORD_SIZE_BIT)
            op2 = triton::ast::bvand(op2, triton::ast::bv(dst.getBitSize() - 1, dst.getBitSize()));

          /* Create the semantics */
          auto node = triton::ast::bvshl(op1, op2);

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
          auto& dst   = inst.operands[0];
          auto& src   = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::ast::zx(dst.getBitSize() - src.getBitSize(), triton::api.buildSymbolicOperand(inst, src));

          if (dst.getBitSize() >= DWORD_SIZE_BIT)
            op2 = triton::ast::bvand(op2, triton::ast::bv(dst.getBitSize() - 1, dst.getBitSize()));

          /* Create the semantics */
          auto node = triton::ast::bvlshr(op1, op2);

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


        void stmxcsr_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto  src = triton::arch::OperandWrapper(TRITON_X86_REG_MXCSR);

          /* Create symbolic operands */
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::extract(DWORD_SIZE_BIT-1, 0, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "STMXCSR operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void stosb_s(triton::arch::Instruction& inst) {
          auto& dst    = inst.operands[0];
          auto& src    = inst.operands[1];
          auto  index  = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
          auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);
          auto op2 = triton::api.buildSymbolicOperand(inst, index);
          auto op3 = triton::api.buildSymbolicOperand(inst, df);

          /* Create the semantics */
          auto node1 = op1;
          auto node2 = triton::ast::ite(
                         triton::ast::equal(op3, triton::ast::bvfalse()),
                         triton::ast::bvadd(op2, triton::ast::bv(BYTE_SIZE, index.getBitSize())),
                         triton::ast::bvsub(op2, triton::ast::bv(BYTE_SIZE, index.getBitSize()))
                       );

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicExpression(inst, node1, dst, "STOSB operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, index, "Index operation");

          /* Spread taint */
          expr1->isTainted = triton::api.taintAssignment(dst, src);
          expr2->isTainted = triton::api.taintUnion(index, index);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void stosd_s(triton::arch::Instruction& inst) {
          auto& dst    = inst.operands[0];
          auto& src    = inst.operands[1];
          auto  index  = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
          auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);
          auto op2 = triton::api.buildSymbolicOperand(inst, index);
          auto op3 = triton::api.buildSymbolicOperand(inst, df);

          /* Create the semantics */
          auto node1 = op1;
          auto node2 = triton::ast::ite(
                         triton::ast::equal(op3, triton::ast::bvfalse()),
                         triton::ast::bvadd(op2, triton::ast::bv(DWORD_SIZE, index.getBitSize())),
                         triton::ast::bvsub(op2, triton::ast::bv(DWORD_SIZE, index.getBitSize()))
                       );

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicExpression(inst, node1, dst, "STOSD operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, index, "Index operation");

          /* Spread taint */
          expr1->isTainted = triton::api.taintAssignment(dst, src);
          expr2->isTainted = triton::api.taintUnion(index, index);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void stosq_s(triton::arch::Instruction& inst) {
          auto& dst    = inst.operands[0];
          auto& src    = inst.operands[1];
          auto  index  = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
          auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);
          auto op2 = triton::api.buildSymbolicOperand(inst, index);
          auto op3 = triton::api.buildSymbolicOperand(inst, df);

          /* Create the semantics */
          auto node1 = op1;
          auto node2 = triton::ast::ite(
                         triton::ast::equal(op3, triton::ast::bvfalse()),
                         triton::ast::bvadd(op2, triton::ast::bv(QWORD_SIZE, index.getBitSize())),
                         triton::ast::bvsub(op2, triton::ast::bv(QWORD_SIZE, index.getBitSize()))
                       );

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicExpression(inst, node1, dst, "STOSQ operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, index, "Index operation");

          /* Spread taint */
          expr1->isTainted = triton::api.taintAssignment(dst, src);
          expr2->isTainted = triton::api.taintUnion(index, index);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void stosw_s(triton::arch::Instruction& inst) {
          auto& dst    = inst.operands[0];
          auto& src    = inst.operands[1];
          auto  index  = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
          auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src);
          auto op2 = triton::api.buildSymbolicOperand(inst, index);
          auto op3 = triton::api.buildSymbolicOperand(inst, df);

          /* Create the semantics */
          auto node1 = op1;
          auto node2 = triton::ast::ite(
                         triton::ast::equal(op3, triton::ast::bvfalse()),
                         triton::ast::bvadd(op2, triton::ast::bv(WORD_SIZE, index.getBitSize())),
                         triton::ast::bvsub(op2, triton::ast::bv(WORD_SIZE, index.getBitSize()))
                       );

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicExpression(inst, node1, dst, "STOSW operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, index, "Index operation");

          /* Spread taint */
          expr1->isTainted = triton::api.taintAssignment(dst, src);
          expr2->isTainted = triton::api.taintUnion(index, index);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void sub_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::bvsub(op1, op2);

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
          auto& src1 = inst.operands[0];
          auto& src2 = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src1);
          auto op2 = triton::api.buildSymbolicOperand(inst, src2);

          /* Create the semantics */
          auto node = triton::ast::bvand(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicVolatileExpression(inst, node, "TEST operation");

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


        void unpckhpd_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::concat(
                        triton::ast::extract(127, 64, op2),
                        triton::ast::extract(127, 64, op1)
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "UNPCKHPD operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void unpckhps_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> unpack;

          unpack.push_back(triton::ast::extract(127, 96, op2));
          unpack.push_back(triton::ast::extract(127, 96, op1));
          unpack.push_back(triton::ast::extract(95, 64, op2));
          unpack.push_back(triton::ast::extract(95, 64, op1));

          auto node = triton::ast::concat(unpack);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "UNPCKHPS operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void unpcklpd_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::concat(
                        triton::ast::extract(63, 0, op2),
                        triton::ast::extract(63, 0, op1)
                      );

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "UNPCKLPD operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void unpcklps_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          std::list<triton::ast::AbstractNode*> unpack;

          unpack.push_back(triton::ast::extract(63, 32, op2));
          unpack.push_back(triton::ast::extract(63, 32, op1));
          unpack.push_back(triton::ast::extract(31, 0, op2));
          unpack.push_back(triton::ast::extract(31, 0, op1));

          auto node = triton::ast::concat(unpack);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "UNPCKLPS operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void vmovdqa_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create the semantics */
          auto node = triton::api.buildSymbolicOperand(inst, src);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "VMOVDQA operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintAssignment(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void vptest_s(triton::arch::Instruction& inst) {
          auto& src1 = inst.operands[0];
          auto& src2 = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, src1);
          auto op2 = triton::api.buildSymbolicOperand(inst, src2);

          /* Create the semantics */
          auto node1 = triton::ast::bvand(op1, op2);
          auto node2 = triton::ast::bvand(op1, triton::ast::bvnot(op2));

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicVolatileExpression(inst, node1, "VPTEST operation");
          auto expr2 = triton::api.createSymbolicVolatileExpression(inst, node2, "VPTEST operation");

          /* Spread taint */
          expr1->isTainted = triton::api.isTainted(src1) | triton::api.isTainted(src2);
          expr2->isTainted = triton::api.isTainted(src1) | triton::api.isTainted(src2);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::clearFlag_s(inst, TRITON_X86_REG_AF, "Clears adjust flag");
          triton::arch::x86::semantics::cfPtest_s(inst, expr2, src1, true);
          triton::arch::x86::semantics::clearFlag_s(inst, TRITON_X86_REG_OF, "Clears overflow flag");
          triton::arch::x86::semantics::clearFlag_s(inst, TRITON_X86_REG_PF, "Clears parity flag");
          triton::arch::x86::semantics::clearFlag_s(inst, TRITON_X86_REG_SF, "Clears sign flag");
          triton::arch::x86::semantics::zf_s(inst, expr1, src1, true);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void xadd_s(triton::arch::Instruction& inst) {
          auto& dst  = inst.operands[0];
          auto& src  = inst.operands[1];
          bool  dstT = triton::api.isTainted(dst);
          bool  srcT = triton::api.isTainted(src);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node1 = op2;
          auto node2 = op1;

          /* Create symbolic expression */
          auto expr1 = triton::api.createSymbolicExpression(inst, node1, dst, "XCHG operation");
          auto expr2 = triton::api.createSymbolicExpression(inst, node2, src, "XCHG operation");

          /* Spread taint */
          expr1->isTainted = triton::api.setTaint(dst, srcT);
          expr2->isTainted = triton::api.setTaint(src, dstT);

          /* Create symbolic operands */
          op1 = triton::api.buildSymbolicOperand(inst, dst);
          op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node3 = triton::ast::bvadd(op1, op2);

          /* Create symbolic expression */
          auto expr3 = triton::api.createSymbolicExpression(inst, node3, dst, "ADD operation");

          /* Spread taint */
          expr3->isTainted = triton::api.taintUnion(dst, src);

          /* Upate symbolic flags */
          triton::arch::x86::semantics::af_s(inst, expr3, dst, op1, op2);
          triton::arch::x86::semantics::cfAdd_s(inst, expr3, dst, op1, op2);
          triton::arch::x86::semantics::ofAdd_s(inst, expr3, dst, op1, op2);
          triton::arch::x86::semantics::pf_s(inst, expr3, dst);
          triton::arch::x86::semantics::sf_s(inst, expr3, dst);
          triton::arch::x86::semantics::zf_s(inst, expr3, dst);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void xchg_s(triton::arch::Instruction& inst) {
          auto& dst  = inst.operands[0];
          auto& src  = inst.operands[1];
          bool  dstT = triton::api.isTainted(dst);
          bool  srcT = triton::api.isTainted(src);

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
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
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::bvxor(op1, op2);

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
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::bvxor(op1, op2);

          /* Create symbolic expression */
          auto expr = triton::api.createSymbolicExpression(inst, node, dst, "XORPD operation");

          /* Spread taint */
          expr->isTainted = triton::api.taintUnion(dst, src);

          /* Upate the symbolic control flow */
          triton::arch::x86::semantics::controlFlow_s(inst);
        }


        void xorps_s(triton::arch::Instruction& inst) {
          auto& dst = inst.operands[0];
          auto& src = inst.operands[1];

          /* Create symbolic operands */
          auto op1 = triton::api.buildSymbolicOperand(inst, dst);
          auto op2 = triton::api.buildSymbolicOperand(inst, src);

          /* Create the semantics */
          auto node = triton::ast::bvxor(op1, op2);

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

