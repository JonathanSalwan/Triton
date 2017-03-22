//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/cpuSize.hpp>
#include <triton/exceptions.hpp>
#include <triton/x86Semantics.hpp>
#include <triton/x86Specifications.hpp>



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
AAD                          |            | ASCII Adjust AX Before Division
ADC                          |            | Add with Carry
ADCX                         | adx        | Unsigned Integer Addition of Two Operands with Carry Flag
ADD                          |            | Add
AND                          |            | Logical AND
ANDN                         | bmi1       | Logical AND NOT
ANDNPD                       | sse2       | Bitwise Logical AND NOT of Packed Double-Precision Floating-Point Values
ANDNPS                       | sse1       | Bitwise Logical AND NOT of Packed Single-Precision Floating-Point Values
ANDPD                        | sse2       | Bitwise Logical AND of Packed Double-Precision Floating-Point Values
ANDPS                        | sse1       | Bitwise Logical AND of Packed Single-Precision Floating-Point Values
BEXTR                        | bmi1/tbm   | Bit Field Extract
BLSI                         | bmi1       | Extract Lowest Set Isolated Bit
BLSMSK                       | bmi1       | Get Mask Up to Lowest Set Bit
BLSR                         | bmi1       | Reset Lowest Set Bit
BSF                          |            | Bit Scan Forward
BSR                          |            | Bit Scan Reverse
BSWAP                        |            | Byte Swap
BT                           |            | Bit Test
BTC                          |            | Bit Test and Complement
BTR                          |            | Bit Test and Reset
BTS                          |            | Bit Test and Set
CALL                         |            | Call Procedure
CBW                          |            | Convert byte (al) to word (ax)
CDQ                          |            | Convert dword (eax) to qword (edx:eax)
CDQE                         |            | Convert dword (eax) to qword (rax)
CLC                          |            | Clear Carry Flag
CLD                          |            | Clear Direction Flag
CLFLUSH                      | sse2       | Flush Cache Line
CLI                          |            | Clear Interrupt Flag
CLTS                         |            | Clear Task-Switched Flag in CR0
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
CWD                          |            | Convert word (ax) to dword (dx:ax)
CWDE                         |            | Convert word (ax) to dword (eax)
DEC                          |            | Decrement by 1
DIV                          |            | Unsigned Divide
EXTRACTPS                    | sse4.1     | Extract Packed Single Precision Floating-Point Value
IDIV                         |            | Signed Divide
IMUL                         |            | Signed Multiply
INC                          |            | Increment by 1
INVD                         |            | Invalidate Internal Caches
INVLPG                       |            | Invalidate TLB Entry
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
LAHF                         |            | Load Status Flags into AH Register
LDDQU                        | sse3       | Load Unaligned Integer 128 Bits
LDMXCSR                      | sse1       | Load MXCSR Register
LEA                          |            | Load Effective Address
LEAVE                        |            | High Level Procedure Exit
LFENCE                       | sse2       | Load Fence
LODSB                        |            | Load byte at address
LODSD                        |            | Load doubleword at address
LODSQ                        |            | Load quadword at address
LODSW                        |            | Load word at address
MFENCE                       | sse2       | Memory Fence
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
MULX                         | bmi2       | Unsigned Multiply Without Affecting Flags
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
PAUSE                        | sse2       | Spin Loop Hint
PAVGB                        | sse1       | Average Packed Unsigned Byte Integers
PAVGW                        | sse1       | Average Packed Unsigned Word Integers
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
PMOVSXBD                     | sse4.1     | Sign Extend 4 Packed Signed 8-bit Integers
PMOVSXBQ                     | sse4.1     | Sign Extend 2 Packed Signed 8-bit Integers
PMOVSXBW                     | sse4.1     | Sign Extend 8 Packed Signed 8-bit Integers
PMOVSXDQ                     | sse4.1     | Sign Extend 2 Packed Signed 32-bit Integers
PMOVSXWD                     | sse4.1     | Sign Extend 4 Packed Signed 16-bit Integers
PMOVSXWQ                     | sse4.1     | Sign Extend 2 Packed Signed 16-bit Integers
PMOVZXBD                     | sse4.1     | Zero Extend 4 Packed Signed 8-bit Integers
PMOVZXBQ                     | sse4.1     | Zero Extend 2 Packed Signed 8-bit Integers
PMOVZXBW                     | sse4.1     | Zero Extend 8 Packed Signed 8-bit Integers
PMOVZXDQ                     | sse4.1     | Zero Extend 2 Packed Signed 32-bit Integers
PMOVZXWD                     | sse4.1     | Zero Extend 4 Packed Signed 16-bit Integers
PMOVZXWQ                     | sse4.1     | Zero Extend 2 Packed Signed 16-bit Integers
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
RORX                         | bmi2       | Rotate Right Logical Without Affecting Flags
SAHF                         |            | Store AH into Flags
SAL                          |            | Shift Left
SAR                          |            | Shift Right Signed
SARX                         | bmi2       | Shift arithmetic right without affecting flags
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
SFENCE                       | sse1       | Store Fence
SHL                          |            | Shift Left
SHLD                         |            | Double-precision Shift Left
SHLX                         | bmi2       | Shift Logical Left Without Affecting Flags
SHR                          |            | Shift Right Unsigned
SHRD                         |            | Double Precision Shift Right
SHRX                         | bmi2       | Shift Logical Right Without Affecting Flags
STC                          |            | Set Carry Flag
STD                          |            | Set Direction Flag
STI                          |            | Set Interrupt Flag
STMXCSR                      | sse1       | Store MXCSR Register State
STOSB                        |            | Store byte at address
STOSD                        |            | Store doubleword at address
STOSQ                        |            | Store quadword at address
STOSW                        |            | Store word at address
SUB                          |            | Subtract
SYSCALL                      |            | Fast System Call
TEST                         |            | Logical Compare
TZCNT                        | bmi1       | Count the Number of Trailing Zero Bits
UNPCKHPD                     | sse2       | Unpack and Interleave High Packed Double- Precision Floating-Point Values
UNPCKHPS                     | sse1       | Unpack and Interleave High Packed Single-Precision Floating-Point Values
UNPCKLPD                     | sse2       | Unpack and Interleave Low Packed Double-Precision Floating-Point Values
UNPCKLPS                     | sse1       | Unpack and Interleave Low Packed Single-Precision Floating-Point Values
VMOVDQA                      | avx        | VEX Move aligned packed integer values
VMOVDQU                      | avx        | VEX Move unaligned packed integer values
VPAND                        | avx/avx2   | VEX Logical AND
VPANDN                       | avx/avx2   | VEX Logical AND NOT
VPOR                         | avx/avx2   | VEX Logical OR
VPSHUFD                      | avx/avx2   | VEX Shuffle Packed Doublewords
VPTEST                       | avx        | VEX Logical Compare
VPXOR                        | avx/avx2   | VEX Logical XOR
WBINVD                       |            | Write Back and Invalidate Cache
XADD                         |            | Exchange and Add
XCHG                         |            | Exchange Register/Memory with Register
XOR                          |            | Logical Exclusive OR
XORPD                        | sse2       | Bitwise Logical XOR for Double-Precision Floating-Point Values
XORPS                        | sse1       | Bitwise Logical XOR for Single-Precision Floating-Point Values

*/



namespace triton {
  namespace arch {
    namespace x86 {

      x86Semantics::x86Semantics(triton::arch::Architecture* architecture,
                                 triton::engines::symbolic::SymbolicEngine* symbolicEngine,
                                 triton::engines::taint::TaintEngine* taintEngine) {

        this->architecture    = architecture;
        this->symbolicEngine  = symbolicEngine;
        this->taintEngine     = taintEngine;

        if (this->architecture == nullptr)
          throw triton::exceptions::Semantics("x86Semantics::x86Semantics(): The architecture API must be defined.");

        if (this->symbolicEngine == nullptr)
          throw triton::exceptions::Semantics("x86Semantics::x86Semantics(): The symbolic engine API must be defined.");

        if (this->taintEngine == nullptr)
          throw triton::exceptions::Semantics("x86Semantics::x86Semantics(): The taint engines API must be defined.");
      }


      x86Semantics::~x86Semantics() {
      }


      bool x86Semantics::buildSemantics(triton::arch::Instruction& inst) {
        switch (inst.getType()) {
          case ID_INS_AAD:            this->aad_s(inst);          break;
          case ID_INS_ADC:            this->adc_s(inst);          break;
          case ID_INS_ADCX:           this->adcx_s(inst);         break;
          case ID_INS_ADD:            this->add_s(inst);          break;
          case ID_INS_AND:            this->and_s(inst);          break;
          case ID_INS_ANDN:           this->andn_s(inst);         break;
          case ID_INS_ANDNPD:         this->andnpd_s(inst);       break;
          case ID_INS_ANDNPS:         this->andnps_s(inst);       break;
          case ID_INS_ANDPD:          this->andpd_s(inst);        break;
          case ID_INS_ANDPS:          this->andps_s(inst);        break;
          case ID_INS_BEXTR:          this->bextr_s(inst);        break;
          case ID_INS_BLSI:           this->blsi_s(inst);         break;
          case ID_INS_BLSMSK:         this->blsmsk_s(inst);       break;
          case ID_INS_BLSR:           this->blsr_s(inst);         break;
          case ID_INS_BSF:            this->bsf_s(inst);          break;
          case ID_INS_BSR:            this->bsr_s(inst);          break;
          case ID_INS_BSWAP:          this->bswap_s(inst);        break;
          case ID_INS_BT:             this->bt_s(inst);           break;
          case ID_INS_BTC:            this->btc_s(inst);          break;
          case ID_INS_BTR:            this->btr_s(inst);          break;
          case ID_INS_BTS:            this->bts_s(inst);          break;
          case ID_INS_CALL:           this->call_s(inst);         break;
          case ID_INS_CBW:            this->cbw_s(inst);          break;
          case ID_INS_CDQ:            this->cdq_s(inst);          break;
          case ID_INS_CDQE:           this->cdqe_s(inst);         break;
          case ID_INS_CLC:            this->clc_s(inst);          break;
          case ID_INS_CLD:            this->cld_s(inst);          break;
          case ID_INS_CLFLUSH:        this->clflush_s(inst);      break;
          case ID_INS_CLTS:           this->clts_s(inst);         break;
          case ID_INS_CLI:            this->cli_s(inst);          break;
          case ID_INS_CMC:            this->cmc_s(inst);          break;
          case ID_INS_CMOVA:          this->cmova_s(inst);        break;
          case ID_INS_CMOVAE:         this->cmovae_s(inst);       break;
          case ID_INS_CMOVB:          this->cmovb_s(inst);        break;
          case ID_INS_CMOVBE:         this->cmovbe_s(inst);       break;
          case ID_INS_CMOVE:          this->cmove_s(inst);        break;
          case ID_INS_CMOVG:          this->cmovg_s(inst);        break;
          case ID_INS_CMOVGE:         this->cmovge_s(inst);       break;
          case ID_INS_CMOVL:          this->cmovl_s(inst);        break;
          case ID_INS_CMOVLE:         this->cmovle_s(inst);       break;
          case ID_INS_CMOVNE:         this->cmovne_s(inst);       break;
          case ID_INS_CMOVNO:         this->cmovno_s(inst);       break;
          case ID_INS_CMOVNP:         this->cmovnp_s(inst);       break;
          case ID_INS_CMOVNS:         this->cmovns_s(inst);       break;
          case ID_INS_CMOVO:          this->cmovo_s(inst);        break;
          case ID_INS_CMOVP:          this->cmovp_s(inst);        break;
          case ID_INS_CMOVS:          this->cmovs_s(inst);        break;
          case ID_INS_CMP:            this->cmp_s(inst);          break;
          case ID_INS_CMPSB:          this->cmpsb_s(inst);        break;
          case ID_INS_CMPSD:          this->cmpsd_s(inst);        break;
          case ID_INS_CMPSQ:          this->cmpsq_s(inst);        break;
          case ID_INS_CMPSW:          this->cmpsw_s(inst);        break;
          case ID_INS_CMPXCHG:        this->cmpxchg_s(inst);      break;
          case ID_INS_CMPXCHG16B:     this->cmpxchg16b_s(inst);   break;
          case ID_INS_CMPXCHG8B:      this->cmpxchg8b_s(inst);    break;
          case ID_INS_CPUID:          this->cpuid_s(inst);        break;
          case ID_INS_CQO:            this->cqo_s(inst);          break;
          case ID_INS_CWD:            this->cwd_s(inst);          break;
          case ID_INS_CWDE:           this->cwde_s(inst);         break;
          case ID_INS_DEC:            this->dec_s(inst);          break;
          case ID_INS_DIV:            this->div_s(inst);          break;
          case ID_INS_EXTRACTPS:      this->extractps_s(inst);    break;
          case ID_INS_IDIV:           this->idiv_s(inst);         break;
          case ID_INS_IMUL:           this->imul_s(inst);         break;
          case ID_INS_INC:            this->inc_s(inst);          break;
          case ID_INS_INVD:           this->invd_s(inst);         break;
          case ID_INS_INVLPG:         this->invlpg_s(inst);       break;
          case ID_INS_JA:             this->ja_s(inst);           break;
          case ID_INS_JAE:            this->jae_s(inst);          break;
          case ID_INS_JB:             this->jb_s(inst);           break;
          case ID_INS_JBE:            this->jbe_s(inst);          break;
          case ID_INS_JE:             this->je_s(inst);           break;
          case ID_INS_JG:             this->jg_s(inst);           break;
          case ID_INS_JGE:            this->jge_s(inst);          break;
          case ID_INS_JL:             this->jl_s(inst);           break;
          case ID_INS_JLE:            this->jle_s(inst);          break;
          case ID_INS_JMP:            this->jmp_s(inst);          break;
          case ID_INS_JNE:            this->jne_s(inst);          break;
          case ID_INS_JNO:            this->jno_s(inst);          break;
          case ID_INS_JNP:            this->jnp_s(inst);          break;
          case ID_INS_JNS:            this->jns_s(inst);          break;
          case ID_INS_JO:             this->jo_s(inst);           break;
          case ID_INS_JP:             this->jp_s(inst);           break;
          case ID_INS_JS:             this->js_s(inst);           break;
          case ID_INS_LAHF:           this->lahf_s(inst);         break;
          case ID_INS_LDDQU:          this->lddqu_s(inst);        break;
          case ID_INS_LDMXCSR:        this->ldmxcsr_s(inst);      break;
          case ID_INS_LEA:            this->lea_s(inst);          break;
          case ID_INS_LEAVE:          this->leave_s(inst);        break;
          case ID_INS_LFENCE:         this->lfence_s(inst);       break;
          case ID_INS_LODSB:          this->lodsb_s(inst);        break;
          case ID_INS_LODSD:          this->lodsd_s(inst);        break;
          case ID_INS_LODSQ:          this->lodsq_s(inst);        break;
          case ID_INS_LODSW:          this->lodsw_s(inst);        break;
          case ID_INS_MFENCE:         this->mfence_s(inst);       break;
          case ID_INS_MOV:            this->mov_s(inst);          break;
          case ID_INS_MOVABS:         this->movabs_s(inst);       break;
          case ID_INS_MOVAPD:         this->movapd_s(inst);       break;
          case ID_INS_MOVAPS:         this->movaps_s(inst);       break;
          case ID_INS_MOVD:           this->movd_s(inst);         break;
          case ID_INS_MOVDDUP:        this->movddup_s(inst);      break;
          case ID_INS_MOVDQ2Q:        this->movdq2q_s(inst);      break;
          case ID_INS_MOVDQA:         this->movdqa_s(inst);       break;
          case ID_INS_MOVDQU:         this->movdqu_s(inst);       break;
          case ID_INS_MOVHLPS:        this->movhlps_s(inst);      break;
          case ID_INS_MOVHPD:         this->movhpd_s(inst);       break;
          case ID_INS_MOVHPS:         this->movhps_s(inst);       break;
          case ID_INS_MOVLHPS:        this->movlhps_s(inst);      break;
          case ID_INS_MOVLPD:         this->movlpd_s(inst);       break;
          case ID_INS_MOVLPS:         this->movlps_s(inst);       break;
          case ID_INS_MOVMSKPD:       this->movmskpd_s(inst);     break;
          case ID_INS_MOVMSKPS:       this->movmskps_s(inst);     break;
          case ID_INS_MOVNTDQ:        this->movntdq_s(inst);      break;
          case ID_INS_MOVNTI:         this->movnti_s(inst);       break;
          case ID_INS_MOVNTPD:        this->movntpd_s(inst);      break;
          case ID_INS_MOVNTPS:        this->movntps_s(inst);      break;
          case ID_INS_MOVNTQ:         this->movntq_s(inst);       break;
          case ID_INS_MOVQ2DQ:        this->movq2dq_s(inst);      break;
          case ID_INS_MOVQ:           this->movq_s(inst);         break;
          case ID_INS_MOVSB:          this->movsb_s(inst);        break;
          case ID_INS_MOVSD:          this->movsd_s(inst);        break;
          case ID_INS_MOVSHDUP:       this->movshdup_s(inst);     break;
          case ID_INS_MOVSLDUP:       this->movsldup_s(inst);     break;
          case ID_INS_MOVSQ:          this->movsq_s(inst);        break;
          case ID_INS_MOVSW:          this->movsw_s(inst);        break;
          case ID_INS_MOVSX:          this->movsx_s(inst);        break;
          case ID_INS_MOVSXD:         this->movsxd_s(inst);       break;
          case ID_INS_MOVUPD:         this->movupd_s(inst);       break;
          case ID_INS_MOVUPS:         this->movups_s(inst);       break;
          case ID_INS_MOVZX:          this->movzx_s(inst);        break;
          case ID_INS_MUL:            this->mul_s(inst);          break;
          case ID_INS_MULX:           this->mulx_s(inst);         break;
          case ID_INS_NEG:            this->neg_s(inst);          break;
          case ID_INS_NOP:            this->nop_s(inst);          break;
          case ID_INS_NOT:            this->not_s(inst);          break;
          case ID_INS_OR:             this->or_s(inst);           break;
          case ID_INS_ORPD:           this->orpd_s(inst);         break;
          case ID_INS_ORPS:           this->orps_s(inst);         break;
          case ID_INS_PADDB:          this->paddb_s(inst);        break;
          case ID_INS_PADDD:          this->paddd_s(inst);        break;
          case ID_INS_PADDQ:          this->paddq_s(inst);        break;
          case ID_INS_PADDW:          this->paddw_s(inst);        break;
          case ID_INS_PAND:           this->pand_s(inst);         break;
          case ID_INS_PANDN:          this->pandn_s(inst);        break;
          case ID_INS_PAUSE:          this->pause_s(inst);        break;
          case ID_INS_PAVGB:          this->pavgb_s(inst);        break;
          case ID_INS_PAVGW:          this->pavgw_s(inst);        break;
          case ID_INS_PCMPEQB:        this->pcmpeqb_s(inst);      break;
          case ID_INS_PCMPEQD:        this->pcmpeqd_s(inst);      break;
          case ID_INS_PCMPEQW:        this->pcmpeqw_s(inst);      break;
          case ID_INS_PCMPGTB:        this->pcmpgtb_s(inst);      break;
          case ID_INS_PCMPGTD:        this->pcmpgtd_s(inst);      break;
          case ID_INS_PCMPGTW:        this->pcmpgtw_s(inst);      break;
          case ID_INS_PMAXSB:         this->pmaxsb_s(inst);       break;
          case ID_INS_PMAXSD:         this->pmaxsd_s(inst);       break;
          case ID_INS_PMAXSW:         this->pmaxsw_s(inst);       break;
          case ID_INS_PMAXUB:         this->pmaxub_s(inst);       break;
          case ID_INS_PMAXUD:         this->pmaxud_s(inst);       break;
          case ID_INS_PMAXUW:         this->pmaxuw_s(inst);       break;
          case ID_INS_PMINSB:         this->pminsb_s(inst);       break;
          case ID_INS_PMINSD:         this->pminsd_s(inst);       break;
          case ID_INS_PMINSW:         this->pminsw_s(inst);       break;
          case ID_INS_PMINUB:         this->pminub_s(inst);       break;
          case ID_INS_PMINUD:         this->pminud_s(inst);       break;
          case ID_INS_PMINUW:         this->pminuw_s(inst);       break;
          case ID_INS_PMOVMSKB:       this->pmovmskb_s(inst);     break;
          case ID_INS_PMOVSXBD:       this->pmovsxbd_s(inst);     break;
          case ID_INS_PMOVSXBQ:       this->pmovsxbq_s(inst);     break;
          case ID_INS_PMOVSXBW:       this->pmovsxbw_s(inst);     break;
          case ID_INS_PMOVSXDQ:       this->pmovsxdq_s(inst);     break;
          case ID_INS_PMOVSXWD:       this->pmovsxwd_s(inst);     break;
          case ID_INS_PMOVSXWQ:       this->pmovsxwq_s(inst);     break;
          case ID_INS_PMOVZXBD:       this->pmovzxbd_s(inst);     break;
          case ID_INS_PMOVZXBQ:       this->pmovzxbq_s(inst);     break;
          case ID_INS_PMOVZXBW:       this->pmovzxbw_s(inst);     break;
          case ID_INS_PMOVZXDQ:       this->pmovzxdq_s(inst);     break;
          case ID_INS_PMOVZXWD:       this->pmovzxwd_s(inst);     break;
          case ID_INS_PMOVZXWQ:       this->pmovzxwq_s(inst);     break;
          case ID_INS_POP:            this->pop_s(inst);          break;
          case ID_INS_POPAL:          this->popal_s(inst);        break;
          case ID_INS_POPFD:          this->popfd_s(inst);        break;
          case ID_INS_POPFQ:          this->popfq_s(inst);        break;
          case ID_INS_POR:            this->por_s(inst);          break;
          case ID_INS_PREFETCH:       this->prefetchx_s(inst);    break;
          case ID_INS_PREFETCHNTA:    this->prefetchx_s(inst);    break;
          case ID_INS_PREFETCHT0:     this->prefetchx_s(inst);    break;
          case ID_INS_PREFETCHT1:     this->prefetchx_s(inst);    break;
          case ID_INS_PREFETCHT2:     this->prefetchx_s(inst);    break;
          case ID_INS_PREFETCHW:      this->prefetchx_s(inst);    break;
          case ID_INS_PSHUFD:         this->pshufd_s(inst);       break;
          case ID_INS_PSHUFHW:        this->pshufhw_s(inst);      break;
          case ID_INS_PSHUFLW:        this->pshuflw_s(inst);      break;
          case ID_INS_PSHUFW:         this->pshufw_s(inst);       break;
          case ID_INS_PSLLDQ:         this->pslldq_s(inst);       break;
          case ID_INS_PSRLDQ:         this->psrldq_s(inst);       break;
          case ID_INS_PSUBB:          this->psubb_s(inst);        break;
          case ID_INS_PSUBD:          this->psubd_s(inst);        break;
          case ID_INS_PSUBQ:          this->psubq_s(inst);        break;
          case ID_INS_PSUBW:          this->psubw_s(inst);        break;
          case ID_INS_PTEST:          this->ptest_s(inst);        break;
          case ID_INS_PUNPCKHBW:      this->punpckhbw_s(inst);    break;
          case ID_INS_PUNPCKHDQ:      this->punpckhdq_s(inst);    break;
          case ID_INS_PUNPCKHQDQ:     this->punpckhqdq_s(inst);   break;
          case ID_INS_PUNPCKHWD:      this->punpckhwd_s(inst);    break;
          case ID_INS_PUNPCKLBW:      this->punpcklbw_s(inst);    break;
          case ID_INS_PUNPCKLDQ:      this->punpckldq_s(inst);    break;
          case ID_INS_PUNPCKLQDQ:     this->punpcklqdq_s(inst);   break;
          case ID_INS_PUNPCKLWD:      this->punpcklwd_s(inst);    break;
          case ID_INS_PUSH:           this->push_s(inst);         break;
          case ID_INS_PUSHAL:         this->pushal_s(inst);       break;
          case ID_INS_PUSHFD:         this->pushfd_s(inst);       break;
          case ID_INS_PUSHFQ:         this->pushfq_s(inst);       break;
          case ID_INS_PXOR:           this->pxor_s(inst);         break;
          case ID_INS_RCL:            this->rcl_s(inst);          break;
          case ID_INS_RCR:            this->rcr_s(inst);          break;
          case ID_INS_RDTSC:          this->rdtsc_s(inst);        break;
          case ID_INS_RET:            this->ret_s(inst);          break;
          case ID_INS_ROL:            this->rol_s(inst);          break;
          case ID_INS_ROR:            this->ror_s(inst);          break;
          case ID_INS_RORX:           this->rorx_s(inst);         break;
          case ID_INS_SAHF:           this->sahf_s(inst);         break;
          case ID_INS_SAL:            this->shl_s(inst);          break;
          case ID_INS_SAR:            this->sar_s(inst);          break;
          case ID_INS_SARX:           this->sarx_s(inst);         break;
          case ID_INS_SBB:            this->sbb_s(inst);          break;
          case ID_INS_SCASB:          this->scasb_s(inst);        break;
          case ID_INS_SCASD:          this->scasd_s(inst);        break;
          case ID_INS_SCASQ:          this->scasq_s(inst);        break;
          case ID_INS_SCASW:          this->scasw_s(inst);        break;
          case ID_INS_SETA:           this->seta_s(inst);         break;
          case ID_INS_SETAE:          this->setae_s(inst);        break;
          case ID_INS_SETB:           this->setb_s(inst);         break;
          case ID_INS_SETBE:          this->setbe_s(inst);        break;
          case ID_INS_SETE:           this->sete_s(inst);         break;
          case ID_INS_SETG:           this->setg_s(inst);         break;
          case ID_INS_SETGE:          this->setge_s(inst);        break;
          case ID_INS_SETL:           this->setl_s(inst);         break;
          case ID_INS_SETLE:          this->setle_s(inst);        break;
          case ID_INS_SETNE:          this->setne_s(inst);        break;
          case ID_INS_SETNO:          this->setno_s(inst);        break;
          case ID_INS_SETNP:          this->setnp_s(inst);        break;
          case ID_INS_SETNS:          this->setns_s(inst);        break;
          case ID_INS_SETO:           this->seto_s(inst);         break;
          case ID_INS_SETP:           this->setp_s(inst);         break;
          case ID_INS_SETS:           this->sets_s(inst);         break;
          case ID_INS_SFENCE:         this->sfence_s(inst);       break;
          case ID_INS_SHL:            this->shl_s(inst);          break;
          case ID_INS_SHLD:           this->shld_s(inst);         break;
          case ID_INS_SHLX:           this->shlx_s(inst);         break;
          case ID_INS_SHR:            this->shr_s(inst);          break;
          case ID_INS_SHRD:           this->shrd_s(inst);         break;
          case ID_INS_SHRX:           this->shrx_s(inst);         break;
          case ID_INS_STC:            this->stc_s(inst);          break;
          case ID_INS_STD:            this->std_s(inst);          break;
          case ID_INS_STI:            this->sti_s(inst);          break;
          case ID_INS_STMXCSR:        this->stmxcsr_s(inst);      break;
          case ID_INS_STOSB:          this->stosb_s(inst);        break;
          case ID_INS_STOSD:          this->stosd_s(inst);        break;
          case ID_INS_STOSQ:          this->stosq_s(inst);        break;
          case ID_INS_STOSW:          this->stosw_s(inst);        break;
          case ID_INS_SUB:            this->sub_s(inst);          break;
          case ID_INS_SYSCALL:        this->syscall_s(inst);      break;
          case ID_INS_TEST:           this->test_s(inst);         break;
          case ID_INS_TZCNT:          this->tzcnt_s(inst);        break;
          case ID_INS_UNPCKHPD:       this->unpckhpd_s(inst);     break;
          case ID_INS_UNPCKHPS:       this->unpckhps_s(inst);     break;
          case ID_INS_UNPCKLPD:       this->unpcklpd_s(inst);     break;
          case ID_INS_UNPCKLPS:       this->unpcklps_s(inst);     break;
          case ID_INS_VMOVDQA:        this->vmovdqa_s(inst);      break;
          case ID_INS_VMOVDQU:        this->vmovdqu_s(inst);      break;
          case ID_INS_VPAND:          this->vpand_s(inst);        break;
          case ID_INS_VPANDN:         this->vpandn_s(inst);       break;
          case ID_INS_VPOR:           this->vpor_s(inst);         break;
          case ID_INS_VPTEST:         this->vptest_s(inst);       break;
          case ID_INS_VPSHUFD:        this->vpshufd_s(inst);      break;
          case ID_INS_VPXOR:          this->vpxor_s(inst);        break;
          case ID_INS_WBINVD:         this->wbinvd_s(inst);       break;
          case ID_INS_XADD:           this->xadd_s(inst);         break;
          case ID_INS_XCHG:           this->xchg_s(inst);         break;
          case ID_INS_XOR:            this->xor_s(inst);          break;
          case ID_INS_XORPD:          this->xorpd_s(inst);        break;
          case ID_INS_XORPS:          this->xorps_s(inst);        break;
          default:
            return false;
        }
        return true;
      }


      triton::uint64 x86Semantics::alignAddStack_s(triton::arch::Instruction& inst, triton::uint32 delta) {
        auto dst = triton::arch::OperandWrapper(TRITON_X86_REG_SP.getParent());

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = triton::ast::bv(delta, dst.getBitSize());

        /* Create the semantics */
        auto node = triton::ast::bvadd(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "Stack alignment");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Return the new stack value */
        return node->evaluate().convert_to<triton::uint64>();
      }


      triton::uint64 x86Semantics::alignSubStack_s(triton::arch::Instruction& inst, triton::uint32 delta) {
        auto dst = triton::arch::OperandWrapper(TRITON_X86_REG_SP.getParent());

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = triton::ast::bv(delta, dst.getBitSize());

        /* Create the semantics */
        auto node = triton::ast::bvsub(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "Stack alignment");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Return the new stack value */
        return node->evaluate().convert_to<triton::uint64>();
      }


      void x86Semantics::clearFlag_s(triton::arch::Instruction& inst, triton::arch::Register& flag, std::string comment) {
        /* Create the semantics */
        auto node = triton::ast::bv(0, 1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, flag, comment);

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaintRegister(flag, triton::engines::taint::UNTAINTED);
      }


      void x86Semantics::setFlag_s(triton::arch::Instruction& inst, triton::arch::Register& flag, std::string comment) {
        /* Create the semantics */
        auto node = triton::ast::bv(1, 1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, flag, comment);

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaintRegister(flag, triton::engines::taint::UNTAINTED);
      }


      void x86Semantics::controlFlow_s(triton::arch::Instruction& inst) {
        auto pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC.getParent());
        auto counter = triton::arch::OperandWrapper(TRITON_X86_REG_CX.getParent());
        auto zf      = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

        /* Update instruction address if undefined */
        if (!inst.getAddress())
          inst.setAddress(this->architecture->getConcreteRegisterValue(pc.getConstRegister()).convert_to<triton::uint64>());

        switch (inst.getPrefix()) {

          case triton::arch::x86::ID_PREFIX_REP: {
            /* Create symbolic operands */
            auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, counter);

            /* Create the semantics for Counter */
            auto node1 = triton::ast::bvsub(op1, triton::ast::bv(1, counter.getBitSize()));

            /* Create the semantics for PC */
            auto node2 = triton::ast::ite(
                     triton::ast::equal(node1, triton::ast::bv(0, counter.getBitSize())),
                     triton::ast::bv(inst.getNextAddress(), pc.getBitSize()),
                     triton::ast::bv(inst.getAddress(), pc.getBitSize())
                   );

            /* Create symbolic expression */
            auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, counter, "Counter operation");
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, pc, "Program Counter");

            /* Spread taint for PC */
            expr1->isTainted = this->taintEngine->taintUnion(counter, counter);
            expr2->isTainted = this->taintEngine->taintAssignment(pc, counter);
            break;
          }

          case triton::arch::x86::ID_PREFIX_REPE: {
            /* Create symbolic operands */
            auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, counter);
            auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, zf);

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
            auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, counter, "Counter operation");
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, pc, "Program Counter");

            /* Spread taint */
            expr1->isTainted = this->taintEngine->taintUnion(counter, counter);
            expr2->isTainted = this->taintEngine->taintAssignment(pc, counter);
            break;
          }

          case triton::arch::x86::ID_PREFIX_REPNE: {
            /* Create symbolic operands */
            auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, counter);
            auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, zf);

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
            auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, counter, "Counter operation");
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, pc, "Program Counter");

            /* Spread taint */
            expr1->isTainted = this->taintEngine->taintUnion(counter, counter);
            expr2->isTainted = this->taintEngine->taintAssignment(pc, counter);
            break;
          }

          default: {
            /* Create the semantics */
            auto node = triton::ast::bv(inst.getNextAddress(), pc.getBitSize());

            /* Create symbolic expression */
            auto expr = this->symbolicEngine->createSymbolicRegisterExpression(inst, node, TRITON_X86_REG_PC, "Program Counter");

            /* Spread taint */
            expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_PC, triton::engines::taint::UNTAINTED);
            break;
          }
        }
      }


      void x86Semantics::af_s(triton::arch::Instruction& inst,
                              triton::engines::symbolic::SymbolicExpression* parent,
                              triton::arch::OperandWrapper& dst,
                              triton::ast::AbstractNode* op1,
                              triton::ast::AbstractNode* op2,
                              bool vol) {

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
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_AF, "Adjust flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_AF, parent->isTainted);
      }


      void x86Semantics::afNeg_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::arch::OperandWrapper& dst,
                                 triton::ast::AbstractNode* op1,
                                 bool vol) {

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
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_AF, "Adjust flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_AF, parent->isTainted);
      }


      void x86Semantics::cfAdd_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::arch::OperandWrapper& dst,
                                 triton::ast::AbstractNode* op1,
                                 triton::ast::AbstractNode* op2,
                                 bool vol) {

        auto bvSize = dst.getBitSize();
        auto low    = vol ? 0 : dst.getAbstractLow();
        auto high   = vol ? bvSize-1 : dst.getAbstractHigh();

        /*
         * Create the semantic.
         * cf = MSB((op1 & op2) ^ ((op1 ^ op2 ^ parent) & (op1 ^ op2)));
         */
        auto node = triton::ast::extract(bvSize-1, bvSize-1,
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
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
      }


      void x86Semantics::cfBlsi_s(triton::arch::Instruction& inst,
                                  triton::engines::symbolic::SymbolicExpression* parent,
                                  triton::arch::OperandWrapper& dst,
                                  triton::ast::AbstractNode* op1,
                                  bool vol) {

        /*
         * Create the semantic.
         * cf = 0 if op1 == 0 else 1
         */
        auto node = triton::ast::ite(
                      triton::ast::equal(
                        op1,
                        triton::ast::bv(0, dst.getBitSize())
                      ),
                      triton::ast::bv(0, 1),
                      triton::ast::bv(1, 1)
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
      }


      void x86Semantics::cfBlsmsk_s(triton::arch::Instruction& inst,
                                    triton::engines::symbolic::SymbolicExpression* parent,
                                    triton::arch::OperandWrapper& dst,
                                    triton::ast::AbstractNode* op1,
                                    bool vol) {

        /*
         * Create the semantic.
         * cf = 1 if op1 == 0 else 0
         */
        auto node = triton::ast::ite(
                      triton::ast::equal(
                        op1,
                        triton::ast::bv(0, dst.getBitSize())
                      ),
                      triton::ast::bv(1, 1),
                      triton::ast::bv(0, 1)
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
      }


      void x86Semantics::cfBlsr_s(triton::arch::Instruction& inst,
                                  triton::engines::symbolic::SymbolicExpression* parent,
                                  triton::arch::OperandWrapper& dst,
                                  triton::ast::AbstractNode* op1,
                                  bool vol) {

        /*
         * Create the semantic.
         * cf = 1 if op1 == 0 else 0
         */
        auto node = triton::ast::ite(
                      triton::ast::equal(
                        op1,
                        triton::ast::bv(0, dst.getBitSize())
                      ),
                      triton::ast::bv(1, 1),
                      triton::ast::bv(0, 1)
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
      }


      void x86Semantics::cfImul_s(triton::arch::Instruction& inst,
                                  triton::engines::symbolic::SymbolicExpression* parent,
                                  triton::arch::OperandWrapper& dst,
                                  triton::ast::AbstractNode* op1,
                                  triton::ast::AbstractNode* res,
                                  bool vol) {

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
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
      }


      void x86Semantics::cfMul_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::arch::OperandWrapper& dst,
                                 triton::ast::AbstractNode* op1,
                                 bool vol) {

        /*
         * Create the semantic.
         * cf = 0 if op1 == 0 else 1
         */
        auto node = triton::ast::ite(
                      triton::ast::equal(
                        op1,
                        triton::ast::bv(0, dst.getBitSize())
                      ),
                      triton::ast::bv(0, 1),
                      triton::ast::bv(1, 1)
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
      }


      void x86Semantics::cfNeg_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::arch::OperandWrapper& dst,
                                 triton::ast::AbstractNode* op1,
                                 bool vol) {

        /*
         * Create the semantic.
         * cf = 0 if op1 == 0 else 1
         */
        auto node = triton::ast::ite(
                      triton::ast::equal(
                        op1,
                        triton::ast::bv(0, dst.getBitSize())
                      ),
                      triton::ast::bv(0, 1),
                      triton::ast::bv(1, 1)
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
      }


      void x86Semantics::cfPtest_s(triton::arch::Instruction& inst,
                                   triton::engines::symbolic::SymbolicExpression* parent,
                                   triton::arch::OperandWrapper& dst,
                                   bool vol) {

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
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
      }


      void x86Semantics::cfRcl_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::ast::AbstractNode* result,
                                 triton::ast::AbstractNode* op2,
                                 bool vol) {

        auto bvSize = op2->getBitvectorSize();
        auto high   = result->getBitvectorSize() - 1;
        auto cf     = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

        auto node = triton::ast::ite(
                      triton::ast::equal(op2, triton::ast::bv(0, bvSize)),
                      this->symbolicEngine->buildSymbolicOperand(inst, cf),
                      triton::ast::extract(high, high, result)
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
      }


      void x86Semantics::cfRcr_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::arch::OperandWrapper& dst,
                                 triton::ast::AbstractNode* result,
                                 triton::ast::AbstractNode* op2,
                                 bool vol) {

        auto bvSize = op2->getBitvectorSize();
        auto high   = result->getBitvectorSize() - 1;
        auto cf     = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

        auto node = triton::ast::ite(
                      triton::ast::equal(op2, triton::ast::bv(0, bvSize)),
                      this->symbolicEngine->buildSymbolicOperand(inst, cf),
                      triton::ast::extract(high, high, result) /* yes it's should be LSB, but here it's a trick :-) */
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
      }


      void x86Semantics::cfRol_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::arch::OperandWrapper& dst,
                                 triton::ast::AbstractNode* op2,
                                 bool vol) {

        auto bvSize = op2->getBitvectorSize();
        auto low    = vol ? 0 : dst.getAbstractLow();
        auto cf     = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

        auto node = triton::ast::ite(
                      triton::ast::equal(op2, triton::ast::bv(0, bvSize)),
                      this->symbolicEngine->buildSymbolicOperand(inst, cf),
                      triton::ast::extract(low, low, triton::ast::reference(parent->getId()))
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
      }


      void x86Semantics::cfRor_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::arch::OperandWrapper& dst,
                                 triton::ast::AbstractNode* op2,
                                 bool vol) {

        auto bvSize = op2->getBitvectorSize();
        auto high   = vol ? bvSize-1 : dst.getAbstractHigh();
        auto cf     = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

        auto node = triton::ast::ite(
                      triton::ast::equal(op2, triton::ast::bv(0, bvSize)),
                      this->symbolicEngine->buildSymbolicOperand(inst, cf),
                      triton::ast::extract(high, high, triton::ast::reference(parent->getId()))
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
      }


      void x86Semantics::cfSar_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::arch::OperandWrapper& dst,
                                 triton::ast::AbstractNode* op1,
                                 triton::ast::AbstractNode* op2,
                                 bool vol) {

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
                      this->symbolicEngine->buildSymbolicOperand(inst, cf),
                      triton::ast::ite(
                        triton::ast::bvugt(op2, triton::ast::bv(bvSize, bvSize)),
                        triton::ast::extract(0, 0, triton::ast::bvlshr(op1, triton::ast::bvsub(triton::ast::bv(bvSize, bvSize), triton::ast::bv(1, bvSize)))),
                        triton::ast::extract(0, 0, triton::ast::bvlshr(op1, triton::ast::bvsub(op2, triton::ast::bv(1, bvSize))))
                      )
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
      }


      void x86Semantics::cfShl_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::arch::OperandWrapper& dst,
                                 triton::ast::AbstractNode* op1,
                                 triton::ast::AbstractNode* op2,
                                 bool vol) {

        auto bvSize = dst.getBitSize();
        auto cf     = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

        /*
         * Create the semantic.
         * cf = (op1 >> ((bvSize - op2) & 1) if op2 != 0
         */
        auto node = triton::ast::ite(
                      triton::ast::equal(op2, triton::ast::bv(0, bvSize)),
                      this->symbolicEngine->buildSymbolicOperand(inst, cf),
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
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
      }


      void x86Semantics::cfShld_s(triton::arch::Instruction& inst,
                                  triton::engines::symbolic::SymbolicExpression* parent,
                                  triton::arch::OperandWrapper& dst,
                                  triton::ast::AbstractNode* op1,
                                  triton::ast::AbstractNode* op2,
                                  triton::ast::AbstractNode* op3,
                                  bool vol) {

        auto bvSize = op3->getBitvectorSize();
        auto cf     = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

        /*
         * Create the semantic.
         * cf = MSB(rol(op3, concat(op2,op1))) if op3 != 0
         */
        auto node = triton::ast::ite(
                      triton::ast::equal(op3, triton::ast::bv(0, bvSize)),
                      this->symbolicEngine->buildSymbolicOperand(inst, cf),
                      triton::ast::extract(
                        dst.getBitSize(), dst.getBitSize(),
                        triton::ast::bvrol(
                          triton::ast::decimal(op3->evaluate()),
                          triton::ast::concat(op2, op1)
                        )
                      )
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
      }


      void x86Semantics::cfShr_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::arch::OperandWrapper& dst,
                                 triton::ast::AbstractNode* op1,
                                 triton::ast::AbstractNode* op2,
                                 bool vol) {

        auto bvSize = dst.getBitSize();
        auto cf     = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

        /*
         * Create the semantic.
         * cf = ((op1 >> (op2 - 1)) & 1) if op2 != 0
         */
        auto node = triton::ast::ite(
                      triton::ast::equal(op2, triton::ast::bv(0, bvSize)),
                      this->symbolicEngine->buildSymbolicOperand(inst, cf),
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
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
      }


      void x86Semantics::cfShrd_s(triton::arch::Instruction& inst,
                                  triton::engines::symbolic::SymbolicExpression* parent,
                                  triton::arch::OperandWrapper& dst,
                                  triton::ast::AbstractNode* op1,
                                  triton::ast::AbstractNode* op2,
                                  triton::ast::AbstractNode* op3,
                                  bool vol) {

        auto bvSize = op3->getBitvectorSize();
        auto cf     = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

        /*
         * Create the semantic.
         * cf = MSB(ror(op3, concat(op2,op1))) if op3 != 0
         */
        auto node = triton::ast::ite(
                      triton::ast::equal(op3, triton::ast::bv(0, bvSize)),
                      this->symbolicEngine->buildSymbolicOperand(inst, cf),
                      triton::ast::extract(
                        (dst.getBitSize() * 2)-1, (dst.getBitSize()*2)-1,
                        triton::ast::bvror(
                          triton::ast::decimal(op3->evaluate()),
                          triton::ast::concat(op2, op1)
                        )
                      )
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
      }


      void x86Semantics::cfSub_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::arch::OperandWrapper& dst,
                                 triton::ast::AbstractNode* op1,
                                 triton::ast::AbstractNode* op2,
                                 bool vol) {

        auto bvSize = dst.getBitSize();
        auto low    = vol ? 0 : dst.getAbstractLow();
        auto high   = vol ? bvSize-1 : dst.getAbstractHigh();

        /*
         * Create the semantic.
         * cf = extract(bvSize, bvSize (((op1 ^ op2 ^ res) ^ ((op1 ^ res) & (op1 ^ op2)))))
         */
        auto node = triton::ast::extract(bvSize-1, bvSize-1,
                      triton::ast::bvxor(
                        triton::ast::bvxor(op1, triton::ast::bvxor(op2, triton::ast::extract(high, low, triton::ast::reference(parent->getId())))),
                        triton::ast::bvand(
                          triton::ast::bvxor(op1, triton::ast::extract(high, low, triton::ast::reference(parent->getId()))),
                          triton::ast::bvxor(op1, op2)
                        )
                      )
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "Carry flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_CF, parent->isTainted);
      }


      void x86Semantics::ofAdd_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::arch::OperandWrapper& dst,
                                 triton::ast::AbstractNode* op1,
                                 triton::ast::AbstractNode* op2,
                                 bool vol) {

        auto bvSize = dst.getBitSize();
        auto low    = vol ? 0 : dst.getAbstractLow();
        auto high   = vol ? bvSize-1 : dst.getAbstractHigh();

        /*
         * Create the semantic.
         * of = MSB((op1 ^ ~op2) & (op1 ^ regDst))
         */
        auto node = triton::ast::extract(bvSize-1, bvSize-1,
                      triton::ast::bvand(
                        triton::ast::bvxor(op1, triton::ast::bvnot(op2)),
                        triton::ast::bvxor(op1, triton::ast::extract(high, low, triton::ast::reference(parent->getId())))
                      )
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_OF, parent->isTainted);
      }


      void x86Semantics::ofImul_s(triton::arch::Instruction& inst,
                                  triton::engines::symbolic::SymbolicExpression* parent,
                                  triton::arch::OperandWrapper& dst,
                                  triton::ast::AbstractNode* op1,
                                  triton::ast::AbstractNode* res,
                                  bool vol) {
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
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_OF, parent->isTainted);
      }


      void x86Semantics::ofMul_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::arch::OperandWrapper& dst,
                                 triton::ast::AbstractNode* op1,
                                 bool vol) {

        /*
         * Create the semantic.
         * of = 0 if up == 0 else 1
         */
        auto node = triton::ast::ite(
                      triton::ast::equal(
                        op1,
                        triton::ast::bv(0, dst.getBitSize())
                      ),
                      triton::ast::bv(0, 1),
                      triton::ast::bv(1, 1)
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_OF, parent->isTainted);
      }


      void x86Semantics::ofNeg_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::arch::OperandWrapper& dst,
                                 triton::ast::AbstractNode* op1,
                                 bool vol) {

        auto bvSize = dst.getBitSize();
        auto low    = vol ? 0 : dst.getAbstractLow();
        auto high   = vol ? bvSize-1 : dst.getAbstractHigh();

        /*
         * Create the semantic.
         * of = (res & op1) >> (bvSize - 1) & 1
         */
        auto node = triton::ast::extract(0, 0,
                      triton::ast::bvlshr(
                        triton::ast::bvand(triton::ast::extract(high, low, triton::ast::reference(parent->getId())), op1),
                        triton::ast::bvsub(triton::ast::bv(bvSize, bvSize), triton::ast::bv(1, bvSize))
                      )
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_OF, parent->isTainted);
      }


      void x86Semantics::ofRol_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::arch::OperandWrapper& dst,
                                 triton::ast::AbstractNode* op2,
                                 bool vol) {

        auto bvSize = dst.getBitSize();
        auto high   = vol ? bvSize-1 : dst.getAbstractHigh();
        auto cf     = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
        auto of     = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

        auto node = triton::ast::ite(
                      triton::ast::equal(op2, triton::ast::bv(1, bvSize)),
                      triton::ast::bvxor(
                        triton::ast::extract(high, high, triton::ast::reference(parent->getId())),
                        this->symbolicEngine->buildSymbolicOperand(inst, cf)
                      ),
                      this->symbolicEngine->buildSymbolicOperand(inst, of)
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_OF, parent->isTainted);
      }


      void x86Semantics::ofRor_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::arch::OperandWrapper& dst,
                                 triton::ast::AbstractNode* op2,
                                 bool vol) {

        auto bvSize = op2->getBitvectorSize();
        auto high   = vol ? bvSize-1 : dst.getAbstractHigh();
        auto of     = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

        auto node = triton::ast::ite(
                      triton::ast::equal(op2, triton::ast::bv(1, bvSize)),
                      triton::ast::bvxor(
                        triton::ast::extract(high, high, triton::ast::reference(parent->getId())),
                        triton::ast::extract(high-1, high-1, triton::ast::reference(parent->getId()))
                      ),
                      this->symbolicEngine->buildSymbolicOperand(inst, of)
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_OF, parent->isTainted);
      }


      void x86Semantics::ofRcr_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::arch::OperandWrapper& dst,
                                 triton::ast::AbstractNode* op1,
                                 triton::ast::AbstractNode* op2,
                                 bool vol) {

        auto bvSize = op2->getBitvectorSize();
        auto high   = dst.getBitSize()-1;
        auto cf     = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
        auto of     = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

        auto node = triton::ast::ite(
                      triton::ast::equal(op2, triton::ast::bv(1, bvSize)),
                      triton::ast::bvxor(
                        triton::ast::extract(high, high, op1),
                        this->symbolicEngine->buildSymbolicOperand(inst, cf)
                      ),
                      this->symbolicEngine->buildSymbolicOperand(inst, of)
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_OF, parent->isTainted);
      }


      void x86Semantics::ofSar_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::arch::OperandWrapper& dst,
                                 triton::ast::AbstractNode* op2,
                                 bool vol) {

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
                      this->symbolicEngine->buildSymbolicOperand(inst, of)
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_OF, parent->isTainted);
      }


      void x86Semantics::ofShl_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::arch::OperandWrapper& dst,
                                 triton::ast::AbstractNode* op1,
                                 triton::ast::AbstractNode* op2,
                                 bool vol) {

        auto bvSize = dst.getBitSize();
        auto of     = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

        /*
         * Create the semantic.
         * of = ((op1 >> (bvSize - 1)) ^ (op1 >> (bvSize - 2))) & 1; if op2 == 1
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
                      this->symbolicEngine->buildSymbolicOperand(inst, of)
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_OF, parent->isTainted);
      }


      void x86Semantics::ofShld_s(triton::arch::Instruction& inst,
                                  triton::engines::symbolic::SymbolicExpression* parent,
                                  triton::arch::OperandWrapper& dst,
                                  triton::ast::AbstractNode* op1,
                                  triton::ast::AbstractNode* op2,
                                  triton::ast::AbstractNode* op3,
                                  bool vol) {

        auto bvSize = dst.getBitSize();
        auto of     = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

        /*
         * Create the semantic.
         * of = MSB(rol(op3, concat(op2,op1))) ^ MSB(op1); if op3 == 1
         */
        auto node = triton::ast::ite(
                      triton::ast::equal(
                        op3,
                        triton::ast::bv(1, bvSize)),
                      triton::ast::bvxor(
                        triton::ast::extract(
                          dst.getBitSize()-1, dst.getBitSize()-1,
                          triton::ast::bvrol(
                            triton::ast::decimal(op3->evaluate()),
                            triton::ast::concat(op2, op1)
                          )
                        ),
                        triton::ast::extract(dst.getBitSize()-1, dst.getBitSize()-1, op1)
                      ),
                      this->symbolicEngine->buildSymbolicOperand(inst, of)
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_OF, parent->isTainted);
      }


      void x86Semantics::ofShr_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::arch::OperandWrapper& dst,
                                 triton::ast::AbstractNode* op1,
                                 triton::ast::AbstractNode* op2,
                                 bool vol) {

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
                      this->symbolicEngine->buildSymbolicOperand(inst, of)
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_OF, parent->isTainted);
      }


      void x86Semantics::ofShrd_s(triton::arch::Instruction& inst,
                                  triton::engines::symbolic::SymbolicExpression* parent,
                                  triton::arch::OperandWrapper& dst,
                                  triton::ast::AbstractNode* op1,
                                  triton::ast::AbstractNode* op2,
                                  triton::ast::AbstractNode* op3,
                                  bool vol) {

        auto bvSize = dst.getBitSize();
        auto of     = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

        /*
         * Create the semantic.
         * of = MSB(ror(op3, concat(op2,op1))) ^ MSB(op1); if op3 == 1
         */
        auto node = triton::ast::ite(
                      triton::ast::equal(
                        op3,
                        triton::ast::bv(1, bvSize)),
                      triton::ast::bvxor(
                        triton::ast::extract(
                          dst.getBitSize()-1, dst.getBitSize()-1,
                          triton::ast::bvror(
                            triton::ast::decimal(op3->evaluate()),
                            triton::ast::concat(op2, op1)
                          )
                        ),
                        triton::ast::extract(dst.getBitSize()-1, dst.getBitSize()-1, op1)
                      ),
                      this->symbolicEngine->buildSymbolicOperand(inst, of)
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_OF, parent->isTainted);
      }


      void x86Semantics::ofSub_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::arch::OperandWrapper& dst,
                                 triton::ast::AbstractNode* op1,
                                 triton::ast::AbstractNode* op2,
                                 bool vol) {

        auto bvSize = dst.getBitSize();
        auto low    = vol ? 0 : dst.getAbstractLow();
        auto high   = vol ? bvSize-1 : dst.getAbstractHigh();

        /*
         * Create the semantic.
         * of = high:bool((op1 ^ op2) & (op1 ^ regDst))
         */
        auto node = triton::ast::extract(bvSize-1, bvSize-1,
                      triton::ast::bvand(
                        triton::ast::bvxor(op1, op2),
                        triton::ast::bvxor(op1, triton::ast::extract(high, low, triton::ast::reference(parent->getId())))
                      )
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_OF, "Overflow flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_OF, parent->isTainted);
      }


      void x86Semantics::pf_s(triton::arch::Instruction& inst,
                              triton::engines::symbolic::SymbolicExpression* parent,
                              triton::arch::OperandWrapper& dst,
                              bool vol) {

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
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_PF, "Parity flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_PF, parent->isTainted);
      }


      void x86Semantics::pfShl_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::arch::OperandWrapper& dst,
                                 triton::ast::AbstractNode* op2,
                                 bool vol) {

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
                       this->symbolicEngine->buildSymbolicOperand(inst, pf),
                       node1
                     );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node2, TRITON_X86_REG_PF, "Parity flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_PF, parent->isTainted);
      }


      void x86Semantics::sf_s(triton::arch::Instruction& inst,
                              triton::engines::symbolic::SymbolicExpression* parent,
                              triton::arch::OperandWrapper& dst,
                              bool vol) {

        auto bvSize = dst.getBitSize();
        auto high   = vol ? bvSize-1 : dst.getAbstractHigh();

        /*
         * Create the semantic.
         * sf = high:bool(regDst)
         */
        auto node = triton::ast::extract(high, high, triton::ast::reference(parent->getId()));

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_SF, "Sign flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_SF, parent->isTainted);
      }


      void x86Semantics::sfShl_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::arch::OperandWrapper& dst,
                                 triton::ast::AbstractNode* op2,
                                 bool vol) {

        auto bvSize = dst.getBitSize();
        auto high   = vol ? bvSize-1 : dst.getAbstractHigh();
        auto sf     = triton::arch::OperandWrapper(TRITON_X86_REG_SF);

        /*
         * Create the semantic.
         * sf if op2 != 0
         */
        auto node = triton::ast::ite(
                      triton::ast::equal(op2, triton::ast::bv(0, bvSize)),
                      this->symbolicEngine->buildSymbolicOperand(inst, sf),
                      triton::ast::extract(high, high, triton::ast::reference(parent->getId()))
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_SF, "Sign flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_SF, parent->isTainted);
      }


      void x86Semantics::sfShld_s(triton::arch::Instruction& inst,
                                  triton::engines::symbolic::SymbolicExpression* parent,
                                  triton::arch::OperandWrapper& dst,
                                  triton::ast::AbstractNode* op1,
                                  triton::ast::AbstractNode* op2,
                                  triton::ast::AbstractNode* op3,
                                  bool vol) {

        auto bvSize = op3->getBitvectorSize();
        auto sf     = triton::arch::OperandWrapper(TRITON_X86_REG_SF);

        /*
         * Create the semantic.
         * MSB(rol(op3, concat(op2,op1))) if op3 != 0
         */
        auto node = triton::ast::ite(
                      triton::ast::equal(op3, triton::ast::bv(0, bvSize)),
                      this->symbolicEngine->buildSymbolicOperand(inst, sf),
                      triton::ast::extract(
                        dst.getBitSize()-1, dst.getBitSize()-1,
                        triton::ast::bvrol(
                          triton::ast::decimal(op3->evaluate()),
                          triton::ast::concat(op2, op1)
                        )
                      )
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_SF, "Sign flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_SF, parent->isTainted);
      }


      void x86Semantics::sfShrd_s(triton::arch::Instruction& inst,
                                  triton::engines::symbolic::SymbolicExpression* parent,
                                  triton::arch::OperandWrapper& dst,
                                  triton::ast::AbstractNode* op1,
                                  triton::ast::AbstractNode* op2,
                                  triton::ast::AbstractNode* op3,
                                  bool vol) {

        auto bvSize = op3->getBitvectorSize();
        auto sf     = triton::arch::OperandWrapper(TRITON_X86_REG_SF);

        /*
         * Create the semantic.
         * MSB(ror(op3, concat(op2,op1))) if op3 != 0
         */
        auto node = triton::ast::ite(
                      triton::ast::equal(op3, triton::ast::bv(0, bvSize)),
                      this->symbolicEngine->buildSymbolicOperand(inst, sf),
                      triton::ast::extract(
                        dst.getBitSize()-1, dst.getBitSize()-1,
                        triton::ast::bvror(
                          triton::ast::decimal(op3->evaluate()),
                          triton::ast::concat(op2, op1)
                        )
                      )
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_SF, "Sign flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_SF, parent->isTainted);
      }


      void x86Semantics::zf_s(triton::arch::Instruction& inst,
                              triton::engines::symbolic::SymbolicExpression* parent,
                              triton::arch::OperandWrapper& dst,
                              bool vol) {

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
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_ZF, "Zero flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_ZF, parent->isTainted);
      }


      void x86Semantics::zfBsf_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::arch::OperandWrapper& src,
                                 triton::ast::AbstractNode* op2,
                                 bool vol) {

        /*
         * Create the semantic.
         * zf = 1 if op2 == 0 else 0
         */
        auto node = triton::ast::ite(
                      triton::ast::equal(op2, triton::ast::bv(0, src.getBitSize())),
                      triton::ast::bvtrue(),
                      triton::ast::bvfalse()
                    );

        /* Create the symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_ZF, "Zero flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_ZF, parent->isTainted);
      }


      void x86Semantics::zfShl_s(triton::arch::Instruction& inst,
                                 triton::engines::symbolic::SymbolicExpression* parent,
                                 triton::arch::OperandWrapper& dst,
                                 triton::ast::AbstractNode* op2,
                                 bool vol) {

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
                      this->symbolicEngine->buildSymbolicOperand(inst, zf),
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
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_ZF, "Zero flag");

        /* Spread the taint from the parent to the child */
        expr->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_ZF, parent->isTainted);
      }


      void x86Semantics::aad_s(triton::arch::Instruction& inst) {
        auto  src1   = triton::arch::OperandWrapper(triton::arch::Immediate(0x0a, BYTE_SIZE)); /* D5 0A */
        auto  src2   = triton::arch::OperandWrapper(TRITON_X86_REG_AL);
        auto  src3   = triton::arch::OperandWrapper(TRITON_X86_REG_AH);
        auto  dst    = triton::arch::OperandWrapper(TRITON_X86_REG_AX);
        auto  dsttmp = triton::arch::OperandWrapper(TRITON_X86_REG_AL);

        /* D5 ib */
        if (inst.operands.size() == 1)
          src1 = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src2);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, src3);

        /* Create the semantics */
        auto node = triton::ast::zx(
                      BYTE_SIZE_BIT,
                      triton::ast::bvadd(
                        op2,
                        triton::ast::bvmul(op3, op1)
                      )
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "AAD operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate symbolic flags */
        this->pf_s(inst, expr, dsttmp);
        this->sf_s(inst, expr, dsttmp);
        this->zf_s(inst, expr, dsttmp);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::adc_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, cf);

        /* Create the semantics */
        auto node = triton::ast::bvadd(triton::ast::bvadd(op1, op2), triton::ast::zx(dst.getBitSize()-1, op3));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ADC operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);
        expr->isTainted = this->taintEngine->taintUnion(dst, cf);

        /* Upate symbolic flags */
        this->af_s(inst, expr, dst, op1, op2);
        this->cfAdd_s(inst, expr, dst, op1, op2);
        this->ofAdd_s(inst, expr, dst, op1, op2);
        this->pf_s(inst, expr, dst);
        this->sf_s(inst, expr, dst);
        this->zf_s(inst, expr, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::adcx_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, cf);

        /* Create the semantics */
        auto node = triton::ast::bvadd(triton::ast::bvadd(op1, op2), triton::ast::zx(dst.getBitSize()-1, op3));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ADCX operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);
        expr->isTainted = this->taintEngine->taintUnion(dst, cf);

        /* Upate symbolic flags */
        this->cfAdd_s(inst, expr, dst, op1, op2);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::add_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::bvadd(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ADD operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate symbolic flags */
        this->af_s(inst, expr, dst, op1, op2);
        this->cfAdd_s(inst, expr, dst, op1, op2);
        this->ofAdd_s(inst, expr, dst, op1, op2);
        this->pf_s(inst, expr, dst);
        this->sf_s(inst, expr, dst);
        this->zf_s(inst, expr, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::and_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::bvand(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "AND operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate symbolic flags */
        this->clearFlag_s(inst, TRITON_X86_REG_CF, "Clears carry flag");
        this->clearFlag_s(inst, TRITON_X86_REG_OF, "Clears overflow flag");
        this->pf_s(inst, expr, dst);
        this->sf_s(inst, expr, dst);
        this->zf_s(inst, expr, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::andn_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, src2);

        /* Create the semantics */
        auto node = triton::ast::bvand(triton::ast::bvnot(op2), op3);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ANDN operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src1) | this->taintEngine->taintUnion(dst, src2);

        this->clearFlag_s(inst, TRITON_X86_REG_CF, "Clears carry flag");
        this->clearFlag_s(inst, TRITON_X86_REG_OF, "Clears overflow flag");
        this->sf_s(inst, expr, dst);
        this->zf_s(inst, expr, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::andnpd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::bvand(triton::ast::bvnot(op1), op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ANDNPD operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::andnps_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::bvand(triton::ast::bvnot(op1), op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ANDNPS operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::andpd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::bvand(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ANDPD operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::andps_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::bvand(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ANDPS operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::bextr_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src2);

        /* Create the semantics */
        auto node = triton::ast::bvand(
                      triton::ast::bvlshr(
                        op1,
                        triton::ast::zx(src1.getBitSize() - BYTE_SIZE_BIT, triton::ast::extract(7, 0, op2))
                      ),
                      triton::ast::bvsub(
                        triton::ast::bvshl(
                          triton::ast::bv(1, src1.getBitSize()),
                          triton::ast::zx(src1.getBitSize() - BYTE_SIZE_BIT, triton::ast::extract(15, 8, op2))
                        ),
                        triton::ast::bv(1, src1.getBitSize())
                      )
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "BEXTR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src1) | this->taintEngine->taintUnion(dst, src2);

        /* Upate symbolic flags */
        this->clearFlag_s(inst, TRITON_X86_REG_CF, "Clears carry flag");
        this->clearFlag_s(inst, TRITON_X86_REG_OF, "Clears overflow flag");
        this->zf_s(inst, expr, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::blsi_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::bvand(triton::ast::bvneg(op1), op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "BLSI operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate symbolic flags */
        this->cfBlsi_s(inst, expr, src, op1);
        this->clearFlag_s(inst, TRITON_X86_REG_OF, "Clears overflow flag");
        this->sf_s(inst, expr, dst);
        this->zf_s(inst, expr, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::blsmsk_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::bvxor(
                      triton::ast::bvsub(op1, triton::ast::bv(1, src.getBitSize())),
                      op1
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "BLSMSK operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate symbolic flags */
        this->cfBlsmsk_s(inst, expr, src, op1);
        this->clearFlag_s(inst, TRITON_X86_REG_OF, "Clears overflow flag");
        this->sf_s(inst, expr, dst);
        this->clearFlag_s(inst, TRITON_X86_REG_ZF, "Clears zero flag");

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::blsr_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::bvand(
                      triton::ast::bvsub(op1, triton::ast::bv(1, src.getBitSize())),
                      op1
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "BLSR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate symbolic flags */
        this->cfBlsr_s(inst, expr, src, op1);
        this->clearFlag_s(inst, TRITON_X86_REG_OF, "Clears overflow flag");
        this->sf_s(inst, expr, dst);
        this->zf_s(inst, expr, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::bsf_s(triton::arch::Instruction& inst) {
        auto& dst     = inst.operands[0];
        auto& src     = inst.operands[1];
        auto  bvSize1 = dst.getBitSize();
        auto  bvSize2 = src.getBitSize();

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
            throw triton::exceptions::Semantics("x86Semantics::bsf_s(): Invalid operand size.");
        }

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "BSF operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate symbolic flags */
        this->zfBsf_s(inst, expr, src, op2);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::bsr_s(triton::arch::Instruction& inst) {
        auto& dst     = inst.operands[0];
        auto& src     = inst.operands[1];
        auto  bvSize1 = dst.getBitSize();
        auto  bvSize2 = src.getBitSize();

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
            throw triton::exceptions::Semantics("x86Semantics::bsr_s(): Invalid operand size.");
        }

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "BSR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate symbolic flags */
        this->zfBsf_s(inst, expr, src, op2); /* same as bsf */

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::bswap_s(triton::arch::Instruction& inst) {
        auto& src = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
            throw triton::exceptions::Semantics("x86Semantics::bswap_s(): Invalid operand size.");
        }

        auto node = triton::ast::concat(bytes);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, src, "BSWAP operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(src, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::bt_s(triton::arch::Instruction& inst) {
        auto  dst  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
        auto& src1 = inst.operands[0];
        auto& src2 = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src2);

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
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, TRITON_X86_REG_CF, "BT operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src1);
        expr->isTainted = this->taintEngine->taintUnion(dst, src2);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::btc_s(triton::arch::Instruction& inst) {
        auto  dst1 = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
        auto& dst2 = inst.operands[0];
        auto& src1 = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst2);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src1);

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
        auto expr1 = this->symbolicEngine->createSymbolicFlagExpression(inst, node1, TRITON_X86_REG_CF, "BTC carry operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, dst2, "BTC complement operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintUnion(dst1, dst2);
        expr1->isTainted = this->taintEngine->taintUnion(dst1, src1);
        expr2->isTainted = this->taintEngine->taintUnion(dst2, dst1);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::btr_s(triton::arch::Instruction& inst) {
        auto  dst1 = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
        auto& dst2 = inst.operands[0];
        auto& src1 = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst2);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src1);

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
        auto expr1 = this->symbolicEngine->createSymbolicFlagExpression(inst, node1, TRITON_X86_REG_CF, "BTR carry operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, dst2, "BTR reset operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintUnion(dst1, dst2);
        expr1->isTainted = this->taintEngine->taintUnion(dst1, src1);
        expr2->isTainted = this->taintEngine->taintUnion(dst2, dst1);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::bts_s(triton::arch::Instruction& inst) {
        auto  dst1 = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
        auto& dst2 = inst.operands[0];
        auto& src1 = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst2);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src1);

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
        auto expr1 = this->symbolicEngine->createSymbolicFlagExpression(inst, node1, TRITON_X86_REG_CF, "BTS carry operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, dst2, "BTS set operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintUnion(dst1, dst2);
        expr1->isTainted = this->taintEngine->taintUnion(dst1, src1);
        expr2->isTainted = this->taintEngine->taintUnion(dst2, dst1);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::call_s(triton::arch::Instruction& inst) {
        auto stack = TRITON_X86_REG_SP.getParent();

        /* Create the semantics - side effect */
        auto  stackValue = alignSubStack_s(inst, stack.getSize());
        auto  pc         = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
        auto  sp         = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue, stack.getSize()));
        auto& src        = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics - side effect */
        auto node1 = triton::ast::bv(inst.getNextAddress(), pc.getBitSize());

        /* Create the semantics */
        auto node2 = op1;

        /* Create the symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, sp, "Saved Program Counter");

        /* Create symbolic expression */
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, pc, "Program Counter");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignmentMemoryImmediate(sp.getMemory());
        expr2->isTainted = this->taintEngine->taintAssignment(pc, src);

        /* Create the path constraint */
        this->symbolicEngine->addPathConstraint(inst, expr2);
      }


      void x86Semantics::cbw_s(triton::arch::Instruction& inst) {
        auto dst = triton::arch::OperandWrapper(TRITON_X86_REG_AX);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);

        /* Create the semantics */
        auto node = triton::ast::sx(BYTE_SIZE_BIT, triton::ast::extract(BYTE_SIZE_BIT-1, 0, op1));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CBW operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cdq_s(triton::arch::Instruction& inst) {
        auto dst = triton::arch::OperandWrapper(TRITON_X86_REG_EDX);
        auto src = triton::arch::OperandWrapper(TRITON_X86_REG_EAX);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics - TMP = 64 bitvec (EDX:EAX) */
        auto node1 = triton::ast::sx(DWORD_SIZE_BIT, op1);

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node1, "Temporary variable");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->isRegisterTainted(TRITON_X86_REG_EDX) | this->taintEngine->isRegisterTainted(TRITON_X86_REG_EAX);

        /* Create the semantics - EAX = TMP[31...0] */
        auto node2 = triton::ast::extract(DWORD_SIZE_BIT-1, 0, triton::ast::reference(expr1->getId()));

        /* Create symbolic expression */
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, src, "CDQ EAX operation");

        /* Spread taint */
        expr2->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_EAX, expr1->isTainted);

        /* Create the semantics - EDX = TMP[63...32] */
        auto node3 = triton::ast::extract(QWORD_SIZE_BIT-1, DWORD_SIZE_BIT, triton::ast::reference(expr1->getId()));

        /* Create symbolic expression */
        auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, dst, "CDQ EDX operation");

        /* Spread taint */
        expr3->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_EDX, expr1->isTainted);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cdqe_s(triton::arch::Instruction& inst) {
        auto dst = triton::arch::OperandWrapper(TRITON_X86_REG_RAX);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);

        /* Create the semantics */
        auto node = triton::ast::sx(DWORD_SIZE_BIT, triton::ast::extract(DWORD_SIZE_BIT-1, 0, op1));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CDQE operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::clc_s(triton::arch::Instruction& inst) {
        this->clearFlag_s(inst, TRITON_X86_REG_CF, "Clears carry flag");
        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cld_s(triton::arch::Instruction& inst) {
        this->clearFlag_s(inst, TRITON_X86_REG_DF, "Clears direction flag");
        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::clflush_s(triton::arch::Instruction& inst) {
        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::clts_s(triton::arch::Instruction& inst) {
        auto dst = triton::arch::OperandWrapper(TRITON_X86_REG_CR0);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);

        /* Create the semantics */
        triton::ast::AbstractNode* node = nullptr;

        switch (dst.getBitSize()) {
          case QWORD_SIZE_BIT:
            node = triton::ast::bvand(op1, triton::ast::bv(0xfffffffffffffff7, QWORD_SIZE_BIT));
            break;
          case DWORD_SIZE_BIT:
            node = triton::ast::bvand(op1, triton::ast::bv(0xfffffff7, DWORD_SIZE_BIT));
            break;
          default:
            throw triton::exceptions::Semantics("x86Semantics::clts_s(): Invalid operand size.");
        }

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CLTS operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cli_s(triton::arch::Instruction& inst) {
        this->clearFlag_s(inst, TRITON_X86_REG_IF, "Clears interrupt flag");
        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cmc_s(triton::arch::Instruction& inst) {
        auto dst = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);

        /* Create the semantics */
        auto node = triton::ast::bvnot(op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicFlagExpression(inst, node, dst.getRegister(), "CMC operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cmova_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
        auto  zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, cf);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, zf);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(triton::ast::bvand(triton::ast::bvnot(op3), triton::ast::bvnot(op4)), triton::ast::bvtrue()), op2, op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CMOVA operation");

        /* Spread taint and condition flag */
        if (op3->evaluate().is_zero() && op4->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintAssignment(dst, src);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cmovae_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, cf);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(op3, triton::ast::bvfalse()), op2, op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CMOVAE operation");

        /* Spread taint and condition flag */
        if (op3->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintAssignment(dst, src);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cmovb_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, cf);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(op3, triton::ast::bvtrue()), op2, op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CMOVB operation");

        /* Spread taint and condition flag */
        if (!op3->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintAssignment(dst, src);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cmovbe_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
        auto  zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, cf);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, zf);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(triton::ast::bvor(op3, op4), triton::ast::bvtrue()), op2, op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CMOVBE operation");

        /* Spread taint and condition flag */
        if (!op3->evaluate().is_zero() || !op4->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintAssignment(dst, src);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cmove_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, zf);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(op3, triton::ast::bvtrue()), op2, op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CMOVE operation");

        /* Spread taint and condition flag */
        if (!op3->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintAssignment(dst, src);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cmovg_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
        auto  of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
        auto  zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, sf);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, of);
        auto op5 = this->symbolicEngine->buildSymbolicOperand(inst, zf);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(triton::ast::bvor(triton::ast::bvxor(op3, op4), op5), triton::ast::bvfalse()), op2, op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CMOVG operation");

        /* Spread taint and condition flag */
        if ((op3->evaluate().is_zero() == op4->evaluate().is_zero()) && op5->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintAssignment(dst, src);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cmovge_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
        auto  of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, sf);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, of);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(op3, op4), op2, op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CMOVGE operation");

        /* Spread taint and condition flag */
        if (op3->evaluate().is_zero() == op4->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintAssignment(dst, src);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cmovl_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
        auto  of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, sf);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, of);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(triton::ast::bvxor(op3, op4), triton::ast::bvtrue()), op2, op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CMOVL operation");

        /* Spread taint and condition flag */
        if (op3->evaluate().is_zero() != op4->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintAssignment(dst, src);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cmovle_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
        auto  of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
        auto  zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, sf);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, of);
        auto op5 = this->symbolicEngine->buildSymbolicOperand(inst, zf);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(triton::ast::bvor(triton::ast::bvxor(op3, op4), op5), triton::ast::bvtrue()), op2, op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CMOVBE operation");

        /* Spread taint and condition flag */
        if ((op3->evaluate().is_zero() != op4->evaluate().is_zero()) || !op5->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintAssignment(dst, src);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cmovne_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, zf);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(op3, triton::ast::bvfalse()), op2, op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CMOVNE operation");

        /* Spread taint and condition flag */
        if (op3->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintAssignment(dst, src);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cmovno_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, of);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(op3, triton::ast::bvfalse()), op2, op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CMOVNO operation");

        /* Spread taint and condition flag */
        if (op3->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintAssignment(dst, src);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cmovnp_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  pf  = triton::arch::OperandWrapper(TRITON_X86_REG_PF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, pf);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(op3, triton::ast::bvfalse()), op2, op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CMOVNP operation");

        /* Spread taint and condition flag */
        if (op3->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintAssignment(dst, src);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cmovns_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, sf);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(op3, triton::ast::bvfalse()), op2, op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CMOVNS operation");

        /* Spread taint and condition flag */
        if (op3->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintAssignment(dst, src);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cmovo_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, of);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(op3, triton::ast::bvtrue()), op2, op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CMOVO operation");

        /* Spread taint and condition flag */
        if (!op3->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintAssignment(dst, src);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cmovp_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  pf  = triton::arch::OperandWrapper(TRITON_X86_REG_PF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, pf);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(op3, triton::ast::bvtrue()), op2, op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CMOVP operation");

        /* Spread taint and condition flag */
        if (!op3->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintAssignment(dst, src);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cmovs_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto  sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, sf);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(op3, triton::ast::bvtrue()), op2, op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CMOVS operation");

        /* Spread taint and condition flag */
        if (!op3->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintAssignment(dst, src);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cmp_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = triton::ast::sx(dst.getBitSize() - src.getBitSize(), this->symbolicEngine->buildSymbolicOperand(inst, src));

        /* Create the semantics */
        auto node = triton::ast::bvsub(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicVolatileExpression(inst, node, "CMP operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->isTainted(dst) | this->taintEngine->isTainted(src);

        /* Upate symbolic flags */
        this->af_s(inst, expr, dst, op1, op2, true);
        this->cfSub_s(inst, expr, dst, op1, op2, true);
        this->ofSub_s(inst, expr, dst, op1, op2, true);
        this->pf_s(inst, expr, dst, true);
        this->sf_s(inst, expr, dst, true);
        this->zf_s(inst, expr, dst, true);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cmpsb_s(triton::arch::Instruction& inst) {
        auto& dst    = inst.operands[0];
        auto& src    = inst.operands[1];
        auto  index1 = triton::arch::OperandWrapper(TRITON_X86_REG_SI.getParent());
        auto  index2 = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
        auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

        /* If the REP prefix is defined, convert REP into REPE */
        if (inst.getPrefix() == triton::arch::x86::ID_PREFIX_REP)
          inst.setPrefix(triton::arch::x86::ID_PREFIX_REPE);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, index1);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, index2);
        auto op5 = this->symbolicEngine->buildSymbolicOperand(inst, df);

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
        auto expr1 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node1, "CMPSB operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, index1, "Index (SI) operation");
        auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, index2, "Index (DI) operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->isTainted(dst) | this->taintEngine->isTainted(src);
        expr2->isTainted = this->taintEngine->taintUnion(index1, index1);
        expr3->isTainted = this->taintEngine->taintUnion(index2, index2);

        /* Upate symbolic flags */
        this->af_s(inst, expr1, dst, op1, op2, true);
        this->cfSub_s(inst, expr1, dst, op1, op2, true);
        this->ofSub_s(inst, expr1, dst, op1, op2, true);
        this->pf_s(inst, expr1, dst, true);
        this->sf_s(inst, expr1, dst, true);
        this->zf_s(inst, expr1, dst, true);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cmpsd_s(triton::arch::Instruction& inst) {
        auto& dst    = inst.operands[0];
        auto& src    = inst.operands[1];
        auto  index1 = triton::arch::OperandWrapper(TRITON_X86_REG_SI.getParent());
        auto  index2 = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
        auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

        /* If the REP prefix is defined, convert REP into REPE */
        if (inst.getPrefix() == triton::arch::x86::ID_PREFIX_REP)
          inst.setPrefix(triton::arch::x86::ID_PREFIX_REPE);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, index1);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, index2);
        auto op5 = this->symbolicEngine->buildSymbolicOperand(inst, df);

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
        auto expr1 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node1, "CMPSD operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, index1, "Index (SI) operation");
        auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, index2, "Index (DI) operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->isTainted(dst) | this->taintEngine->isTainted(src);
        expr2->isTainted = this->taintEngine->taintUnion(index1, index1);
        expr3->isTainted = this->taintEngine->taintUnion(index2, index2);

        /* Upate symbolic flags */
        this->af_s(inst, expr1, dst, op1, op2, true);
        this->cfSub_s(inst, expr1, dst, op1, op2, true);
        this->ofSub_s(inst, expr1, dst, op1, op2, true);
        this->pf_s(inst, expr1, dst, true);
        this->sf_s(inst, expr1, dst, true);
        this->zf_s(inst, expr1, dst, true);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cmpsq_s(triton::arch::Instruction& inst) {
        auto& dst    = inst.operands[0];
        auto& src    = inst.operands[1];
        auto  index1 = triton::arch::OperandWrapper(TRITON_X86_REG_SI.getParent());
        auto  index2 = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
        auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

        /* If the REP prefix is defined, convert REP into REPE */
        if (inst.getPrefix() == triton::arch::x86::ID_PREFIX_REP)
          inst.setPrefix(triton::arch::x86::ID_PREFIX_REPE);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, index1);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, index2);
        auto op5 = this->symbolicEngine->buildSymbolicOperand(inst, df);

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
        auto expr1 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node1, "CMPSQ operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, index1, "Index (SI) operation");
        auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, index2, "Index (DI) operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->isTainted(dst) | this->taintEngine->isTainted(src);
        expr2->isTainted = this->taintEngine->taintUnion(index1, index1);
        expr3->isTainted = this->taintEngine->taintUnion(index2, index2);

        /* Upate symbolic flags */
        this->af_s(inst, expr1, dst, op1, op2, true);
        this->cfSub_s(inst, expr1, dst, op1, op2, true);
        this->ofSub_s(inst, expr1, dst, op1, op2, true);
        this->pf_s(inst, expr1, dst, true);
        this->sf_s(inst, expr1, dst, true);
        this->zf_s(inst, expr1, dst, true);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cmpsw_s(triton::arch::Instruction& inst) {
        auto& dst    = inst.operands[0];
        auto& src    = inst.operands[1];
        auto  index1 = triton::arch::OperandWrapper(TRITON_X86_REG_SI.getParent());
        auto  index2 = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
        auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

        /* If the REP prefix is defined, convert REP into REPE */
        if (inst.getPrefix() == triton::arch::x86::ID_PREFIX_REP)
          inst.setPrefix(triton::arch::x86::ID_PREFIX_REPE);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, index1);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, index2);
        auto op5 = this->symbolicEngine->buildSymbolicOperand(inst, df);

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
        auto expr1 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node1, "CMPSW operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, index1, "Index (SI) operation");
        auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, index2, "Index (DI) operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->isTainted(dst) | this->taintEngine->isTainted(src);
        expr2->isTainted = this->taintEngine->taintUnion(index1, index1);
        expr3->isTainted = this->taintEngine->taintUnion(index2, index2);

        /* Upate symbolic flags */
        this->af_s(inst, expr1, dst, op1, op2, true);
        this->cfSub_s(inst, expr1, dst, op1, op2, true);
        this->ofSub_s(inst, expr1, dst, op1, op2, true);
        this->pf_s(inst, expr1, dst, true);
        this->sf_s(inst, expr1, dst, true);
        this->zf_s(inst, expr1, dst, true);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cmpxchg_s(triton::arch::Instruction& inst) {
        auto& src1  = inst.operands[0];
        auto& src2  = inst.operands[1];
        auto src1p  = inst.operands[0].getRegister().getParent();
        auto src2p  = inst.operands[1].getRegister().getParent();;

        /* Create the tempory accumulator */
        triton::arch::OperandWrapper accumulator(TRITON_X86_REG_AL);
        triton::arch::OperandWrapper accumulatorp(TRITON_X86_REG_AL.getParent());

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
        auto op1  = this->symbolicEngine->buildSymbolicOperand(inst, accumulator);
        auto op2  = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op3  = this->symbolicEngine->buildSymbolicOperand(inst, src2);
        auto op1p = this->symbolicEngine->buildSymbolicOperand(accumulatorp);
        auto op2p = this->symbolicEngine->buildSymbolicRegister((src1.getType() == triton::arch::OP_REG ? src1.getRegister().getParent() : accumulatorp.getRegister()));
        auto op3p = this->symbolicEngine->buildSymbolicRegister((src1.getType() == triton::arch::OP_REG ? src2.getRegister().getParent() : accumulatorp.getRegister()));

        /* Create the semantics */
        auto nodeq  = triton::ast::equal(op1, op2);
        auto node1  = triton::ast::bvsub(op1, op2);
        auto node2  = triton::ast::ite(nodeq, op3, op2);
        auto node3  = triton::ast::ite(nodeq, op1, op2);
        auto node2p = triton::ast::ite(nodeq, op3p, op2p);
        auto node3p = triton::ast::ite(nodeq, op1p, op2p);

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node1, "CMP operation");
        auto expr2 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node2, "Temporary operation");
        auto expr3 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node2p, "Temporary operation");
        auto expr4 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node3, "Temporary operation");
        auto expr5 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node3p, "Temporary operation");

        triton::engines::symbolic::SymbolicExpression* expr6 = nullptr;
        triton::engines::symbolic::SymbolicExpression* expr7 = nullptr;

        /* Destination */
        if (nodeq->evaluate() == false && src1.getType() == triton::arch::OP_REG)
          expr6 = this->symbolicEngine->createSymbolicRegisterExpression(inst, node2p, src1p, "XCHG operation");
        else
          expr6 = this->symbolicEngine->createSymbolicExpression(inst, node2, src1, "XCHG operation");

        /* Accumulator */
        if (nodeq->evaluate() == true)
          expr7 = this->symbolicEngine->createSymbolicExpression(inst, node3p, accumulatorp, "XCHG operation");
        else
          expr7 = this->symbolicEngine->createSymbolicExpression(inst, node3, accumulator, "XCHG operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->isTainted(accumulator) | this->taintEngine->isTainted(src1);
        expr2->isTainted = expr1->isTainted;
        expr3->isTainted = expr1->isTainted;
        expr4->isTainted = expr1->isTainted;
        expr5->isTainted = expr1->isTainted;
        expr6->isTainted = this->taintEngine->taintAssignment(src1, src2);
        expr7->isTainted = this->taintEngine->taintAssignment(accumulator, src1);

        /* Upate symbolic flags */
        this->af_s(inst, expr1, accumulator, op1, op2, true);
        this->cfSub_s(inst, expr1, accumulator, op1, op2, true);
        this->ofSub_s(inst, expr1, accumulator, op1, op2, true);
        this->pf_s(inst, expr1, accumulator, true);
        this->sf_s(inst, expr1, accumulator, true);
        this->zf_s(inst, expr1, accumulator, true);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cmpxchg16b_s(triton::arch::Instruction& inst) {
        auto& src1 = inst.operands[0];
        auto  src2 = triton::arch::OperandWrapper(TRITON_X86_REG_RDX);
        auto  src3 = triton::arch::OperandWrapper(TRITON_X86_REG_RAX);
        auto  src4 = triton::arch::OperandWrapper(TRITON_X86_REG_RCX);
        auto  src5 = triton::arch::OperandWrapper(TRITON_X86_REG_RBX);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src2);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, src3);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, src4);
        auto op5 = this->symbolicEngine->buildSymbolicOperand(inst, src5);

        /* Create the semantics */
        /* CMP8B */
        auto node1 = triton::ast::bvsub(triton::ast::concat(op2, op3), op1);
        /* Destination */
        auto node2 = triton::ast::ite(triton::ast::equal(node1, triton::ast::bv(0, DQWORD_SIZE_BIT)), triton::ast::concat(op4, op5), op1);
        /* EDX:EAX */
        auto node3 = triton::ast::ite(triton::ast::equal(node1, triton::ast::bv(0, DQWORD_SIZE_BIT)), triton::ast::concat(op2, op3), op1);

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node1, "CMP operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, src1, "XCHG16B memory operation");
        auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, triton::ast::extract(127, 64, node3), src2, "XCHG16B RDX operation");
        auto expr4 = this->symbolicEngine->createSymbolicExpression(inst, triton::ast::extract(63, 0, node3), src3, "XCHG16B RAX operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2) | this->taintEngine->isTainted(src3);
        expr2->isTainted = this->taintEngine->setTaint(src1, this->taintEngine->isTainted(src2) | this->taintEngine->isTainted(src3));
        expr3->isTainted = this->taintEngine->taintAssignment(src2, src1);
        expr4->isTainted = this->taintEngine->taintAssignment(src3, src1);

        /* Upate symbolic flags */
        this->zf_s(inst, expr1, src1, true);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cmpxchg8b_s(triton::arch::Instruction& inst) {
        auto& src1  = inst.operands[0];
        auto  src2  = triton::arch::OperandWrapper(TRITON_X86_REG_EDX);
        auto  src3  = triton::arch::OperandWrapper(TRITON_X86_REG_EAX);
        auto  src4  = triton::arch::OperandWrapper(TRITON_X86_REG_ECX);
        auto  src5  = triton::arch::OperandWrapper(TRITON_X86_REG_EBX);
        auto  src2p = triton::arch::OperandWrapper(TRITON_X86_REG_EDX.getParent());
        auto  src3p = triton::arch::OperandWrapper(TRITON_X86_REG_EAX.getParent());

        /* Create symbolic operands */
        auto op1  = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op2  = this->symbolicEngine->buildSymbolicOperand(inst, src2);
        auto op3  = this->symbolicEngine->buildSymbolicOperand(inst, src3);
        auto op4  = this->symbolicEngine->buildSymbolicOperand(inst, src4);
        auto op5  = this->symbolicEngine->buildSymbolicOperand(inst, src5);
        auto op2p = this->symbolicEngine->buildSymbolicOperand(inst, src2p);
        auto op3p = this->symbolicEngine->buildSymbolicOperand(inst, src3p);

        /* Create the semantics */
        /* CMP8B */
        auto node1 = triton::ast::bvsub(triton::ast::concat(op2, op3), op1);
        /* Destination */
        auto node2 = triton::ast::ite(triton::ast::equal(node1, triton::ast::bv(0, QWORD_SIZE_BIT)), triton::ast::concat(op4, op5), op1);
        /* EDX:EAX */
        auto node3  = triton::ast::ite(triton::ast::equal(node1, triton::ast::bv(0, QWORD_SIZE_BIT)), triton::ast::concat(op2, op3), op1);
        auto node3p = triton::ast::ite(
                        triton::ast::equal(
                          node1,
                          triton::ast::bv(0, QWORD_SIZE_BIT)),
                          triton::ast::concat(op2p, op3p),
                          triton::ast::zx(src2p.getBitSize() + src3p.getBitSize() - src1.getBitSize(), op1)
                      );

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node1, "CMP operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, src1, "XCHG8B memory operation");
        auto expr3 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node3, "Temporary operation");
        auto expr4 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node3p, "Temporary operation");

        triton::engines::symbolic::SymbolicExpression* expr5 = nullptr;
        triton::engines::symbolic::SymbolicExpression* expr6 = nullptr;

        /* EDX */
        if (node1->evaluate() == 0)
          expr5 = this->symbolicEngine->createSymbolicExpression(inst, triton::ast::extract((src2p.getBitSize() * 2 - 1), src2p.getBitSize(), node3p), src2p, "XCHG8B EDX operation");
        else
          expr5 = this->symbolicEngine->createSymbolicExpression(inst, triton::ast::extract(63, 32, node3), src2, "XCHG8B EDX operation");

        /* EAX */
        if (node1->evaluate() == 0)
          expr6 = this->symbolicEngine->createSymbolicExpression(inst, triton::ast::extract(src2p.getBitSize() - 1, 0, node3p), src3p, "XCHG8B EAX operation");
        else
          expr6 = this->symbolicEngine->createSymbolicExpression(inst, triton::ast::extract(31, 0, node3), src3, "XCHG8B EAX operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2) | this->taintEngine->isTainted(src3);
        expr2->isTainted = this->taintEngine->setTaint(src1, this->taintEngine->isTainted(src2) | this->taintEngine->isTainted(src3));
        expr3->isTainted = this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2) | this->taintEngine->isTainted(src3);
        expr4->isTainted = this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2) | this->taintEngine->isTainted(src3);
        expr5->isTainted = this->taintEngine->taintAssignment(src2, src1);
        expr6->isTainted = this->taintEngine->taintAssignment(src3, src1);

        /* Upate symbolic flags */
        this->zf_s(inst, expr1, src1, true);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cpuid_s(triton::arch::Instruction& inst) {
        auto src  = triton::arch::OperandWrapper(TRITON_X86_REG_AX.getParent());
        auto dst1 = triton::arch::OperandWrapper(TRITON_X86_REG_AX.getParent());
        auto dst2 = triton::arch::OperandWrapper(TRITON_X86_REG_BX.getParent());
        auto dst3 = triton::arch::OperandWrapper(TRITON_X86_REG_CX.getParent());
        auto dst4 = triton::arch::OperandWrapper(TRITON_X86_REG_DX.getParent());

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst1, "CPUID AX operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, dst2, "CPUID BX operation");
        auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, dst3, "CPUID CX operation");
        auto expr4 = this->symbolicEngine->createSymbolicExpression(inst, node4, dst4, "CPUID DX operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_AX.getParent(), false);
        expr2->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_BX.getParent(), false);
        expr3->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_CX.getParent(), false);
        expr4->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_DX.getParent(), false);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cqo_s(triton::arch::Instruction& inst) {
        auto dst = triton::arch::OperandWrapper(TRITON_X86_REG_RDX);
        auto src = triton::arch::OperandWrapper(TRITON_X86_REG_RAX);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics - TMP = 128 bitvec (RDX:RAX) */
        auto node1 = triton::ast::sx(QWORD_SIZE_BIT, op1);

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node1, "Temporary variable");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->isRegisterTainted(TRITON_X86_REG_RDX) | this->taintEngine->isRegisterTainted(TRITON_X86_REG_RAX);

        /* Create the semantics - RAX = TMP[63...0] */
        auto node2 = triton::ast::extract(QWORD_SIZE_BIT-1, 0, triton::ast::reference(expr1->getId()));

        /* Create symbolic expression */
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, src, "CQO RAX operation");

        /* Spread taint */
        expr2->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_RAX, expr1->isTainted);

        /* Create the semantics - RDX = TMP[127...64] */
        auto node3 = triton::ast::extract(DQWORD_SIZE_BIT-1, QWORD_SIZE_BIT, triton::ast::reference(expr1->getId()));

        /* Create symbolic expression */
        auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, dst, "CQO RDX operation");

        /* Spread taint */
        expr3->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_RDX, expr1->isTainted);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cwd_s(triton::arch::Instruction& inst) {
        auto dst = triton::arch::OperandWrapper(TRITON_X86_REG_DX);
        auto src = triton::arch::OperandWrapper(TRITON_X86_REG_AX);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics - TMP = 32 bitvec (DX:AX) */
        auto node1 = triton::ast::sx(WORD_SIZE_BIT, op1);

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node1, "Temporary variable");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->isRegisterTainted(TRITON_X86_REG_DX) | this->taintEngine->isRegisterTainted(TRITON_X86_REG_AX);

        /* Create the semantics - AX = TMP[15...0] */
        auto node2 = triton::ast::extract(WORD_SIZE_BIT-1, 0, triton::ast::reference(expr1->getId()));

        /* Create symbolic expression */
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, src, "CWD AX operation");

        /* Spread taint */
        expr2->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_AX, expr1->isTainted);

        /* Create the semantics - DX = TMP[31...16] */
        auto node3 = triton::ast::extract(DWORD_SIZE_BIT-1, WORD_SIZE_BIT, triton::ast::reference(expr1->getId()));

        /* Create symbolic expression */
        auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, dst, "CWD DX operation");

        /* Spread taint */
        expr3->isTainted = this->taintEngine->setTaintRegister(TRITON_X86_REG_DX, expr1->isTainted);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::cwde_s(triton::arch::Instruction& inst) {
        auto dst = triton::arch::OperandWrapper(TRITON_X86_REG_EAX);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);

        /* Create the semantics */
        auto node = triton::ast::sx(WORD_SIZE_BIT, triton::ast::extract(WORD_SIZE_BIT-1, 0, op1));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "CWDE operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::dec_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = triton::ast::bv(1, dst.getBitSize());

        /* Create the semantics */
        auto node = triton::ast::bvsub(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "DEC operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate symbolic flags */
        this->af_s(inst, expr, dst, op1, op2);
        this->ofSub_s(inst, expr, dst, op1, op2);
        this->pf_s(inst, expr, dst);
        this->sf_s(inst, expr, dst);
        this->zf_s(inst, expr, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::div_s(triton::arch::Instruction& inst) {
        auto& src = inst.operands[0];

        /* Create symbolic operands */
        auto divisor = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create symbolic expression */
        switch (src.getSize()) {

          case BYTE_SIZE: {
            /* AX */
            auto ax = triton::arch::OperandWrapper(TRITON_X86_REG_AX);
            auto dividend = this->symbolicEngine->buildSymbolicOperand(inst, ax);
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
            auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, ax, "DIV operation");
            /* Apply the taint */
            expr->isTainted = this->taintEngine->taintUnion(ax, src);
            break;
          }

          case WORD_SIZE: {
            /* DX:AX */
            auto dx = triton::arch::OperandWrapper(TRITON_X86_REG_DX);
            auto ax = triton::arch::OperandWrapper(TRITON_X86_REG_AX);
            auto dividend = triton::ast::concat(this->symbolicEngine->buildSymbolicOperand(inst, dx), this->symbolicEngine->buildSymbolicOperand(inst, ax));
            /* res = DX:AX / Source */
            auto result = triton::ast::extract((WORD_SIZE_BIT - 1), 0, triton::ast::bvudiv(dividend, triton::ast::zx(WORD_SIZE_BIT, divisor)));
            /* mod = DX:AX % Source */
            auto mod = triton::ast::extract((WORD_SIZE_BIT - 1), 0, triton::ast::bvurem(dividend, triton::ast::zx(WORD_SIZE_BIT, divisor)));
            /* Create the symbolic expression for AX */
            auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, result, ax, "DIV operation");
            /* Apply the taint for AX */
            expr1->isTainted = this->taintEngine->taintUnion(ax, src);
            /* Create the symbolic expression for DX */
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, mod, dx, "DIV operation");
            /* Apply the taint for DX */
            expr2->isTainted = this->taintEngine->taintUnion(dx, src);
            break;
          }

          case DWORD_SIZE: {
            /* EDX:EAX */
            auto edx = triton::arch::OperandWrapper(TRITON_X86_REG_EDX);
            auto eax = triton::arch::OperandWrapper(TRITON_X86_REG_EAX);
            auto dividend = triton::ast::concat(this->symbolicEngine->buildSymbolicOperand(inst, edx), this->symbolicEngine->buildSymbolicOperand(inst, eax));
            /* res = EDX:EAX / Source */
            auto result = triton::ast::extract((DWORD_SIZE_BIT - 1), 0, triton::ast::bvudiv(dividend, triton::ast::zx(DWORD_SIZE_BIT, divisor)));
            /* mod = EDX:EAX % Source */
            auto mod = triton::ast::extract((DWORD_SIZE_BIT - 1), 0, triton::ast::bvurem(dividend, triton::ast::zx(DWORD_SIZE_BIT, divisor)));
            /* Create the symbolic expression for EAX */
            auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, result, eax, "DIV operation");
            /* Apply the taint for EAX */
            expr1->isTainted = this->taintEngine->taintUnion(eax, src);
            /* Create the symbolic expression for EDX */
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, mod, edx, "DIV operation");
            /* Apply the taint for EDX */
            expr2->isTainted = this->taintEngine->taintUnion(edx, src);
            break;
          }

          case QWORD_SIZE: {
            /* RDX:RAX */
            auto rdx = triton::arch::OperandWrapper(TRITON_X86_REG_RDX);
            auto rax = triton::arch::OperandWrapper(TRITON_X86_REG_RAX);
            auto dividend = triton::ast::concat(this->symbolicEngine->buildSymbolicOperand(inst, rdx), this->symbolicEngine->buildSymbolicOperand(inst, rax));
            /* res = RDX:RAX / Source */
            auto result = triton::ast::extract((QWORD_SIZE_BIT - 1), 0, triton::ast::bvudiv(dividend, triton::ast::zx(QWORD_SIZE_BIT, divisor)));
            /* mod = RDX:RAX % Source */
            auto mod = triton::ast::extract((QWORD_SIZE_BIT - 1), 0, triton::ast::bvurem(dividend, triton::ast::zx(QWORD_SIZE_BIT, divisor)));
            /* Create the symbolic expression for RAX */
            auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, result, rax, "DIV operation");
            /* Apply the taint for EAX */
            expr1->isTainted = this->taintEngine->taintUnion(rax, src);
            /* Create the symbolic expression for RDX */
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, mod, rdx, "DIV operation");
            /* Apply the taint for EDX */
            expr2->isTainted = this->taintEngine->taintUnion(rdx, src);
            break;
          }

        }

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::extractps_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, src2);

        /* Create the semantics */
        auto node = triton::ast::extract(DWORD_SIZE_BIT-1, 0,
                      triton::ast::bvlshr(
                        op2,
                        triton::ast::bvmul(
                          triton::ast::zx(126, triton::ast::extract(1, 0, op3)),
                          triton::ast::bv(DWORD_SIZE_BIT, DQWORD_SIZE_BIT)
                        )
                      )
                    );

        switch (dst.getBitSize()) {
          case DWORD_SIZE_BIT:
            break;
          case QWORD_SIZE_BIT:
            node = triton::ast::zx(DWORD_SIZE_BIT, node);
            break;
          default:
            throw triton::exceptions::Semantics("x86Semantics::extractps_s(): Invalid destination operand.");
        }

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "EXTRACTPS operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src1);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::idiv_s(triton::arch::Instruction& inst) {
        auto& src = inst.operands[0];

        /* Create symbolic operands */
        auto divisor = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create symbolic expression */
        switch (src.getSize()) {

          case BYTE_SIZE: {
            /* AX */
            auto ax = triton::arch::OperandWrapper(TRITON_X86_REG_AX);
            auto dividend = this->symbolicEngine->buildSymbolicOperand(inst, ax);
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
            auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, ax, "IDIV operation");
            /* Apply the taint */
            expr->isTainted = this->taintEngine->taintUnion(ax, src);
            break;
          }

          case WORD_SIZE: {
            /* DX:AX */
            auto dx = triton::arch::OperandWrapper(TRITON_X86_REG_DX);
            auto ax = triton::arch::OperandWrapper(TRITON_X86_REG_AX);
            auto dividend = triton::ast::concat(this->symbolicEngine->buildSymbolicOperand(inst, dx), this->symbolicEngine->buildSymbolicOperand(inst, ax));
            /* res = DX:AX / Source */
            auto result = triton::ast::extract((WORD_SIZE_BIT - 1), 0, triton::ast::bvsdiv(dividend, triton::ast::sx(WORD_SIZE_BIT, divisor)));
            /* mod = DX:AX % Source */
            auto mod = triton::ast::extract((WORD_SIZE_BIT - 1), 0, triton::ast::bvsrem(dividend, triton::ast::sx(WORD_SIZE_BIT, divisor)));
            /* Create the symbolic expression for AX */
            auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, result, ax, "IDIV operation");
            /* Apply the taint for AX */
            expr1->isTainted = this->taintEngine->taintUnion(ax, src);
            /* Create the symbolic expression for DX */
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, mod, dx, "IDIV operation");
            /* Apply the taint for DX */
            expr2->isTainted = this->taintEngine->taintUnion(dx, src);
            break;
          }

          case DWORD_SIZE: {
            /* EDX:EAX */
            auto edx = triton::arch::OperandWrapper(TRITON_X86_REG_EDX);
            auto eax = triton::arch::OperandWrapper(TRITON_X86_REG_EAX);
            auto dividend = triton::ast::concat(this->symbolicEngine->buildSymbolicOperand(inst, edx), this->symbolicEngine->buildSymbolicOperand(inst, eax));
            /* res = EDX:EAX / Source */
            auto result = triton::ast::extract((DWORD_SIZE_BIT - 1), 0, triton::ast::bvsdiv(dividend, triton::ast::sx(DWORD_SIZE_BIT, divisor)));
            /* mod = EDX:EAX % Source */
            auto mod = triton::ast::extract((DWORD_SIZE_BIT - 1), 0, triton::ast::bvsrem(dividend, triton::ast::sx(DWORD_SIZE_BIT, divisor)));
            /* Create the symbolic expression for EAX */
            auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, result, eax, "IDIV operation");
            /* Apply the taint for EAX */
            expr1->isTainted = this->taintEngine->taintUnion(eax, src);
            /* Create the symbolic expression for EDX */
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, mod, edx, "IDIV operation");
            /* Apply the taint for EDX */
            expr2->isTainted = this->taintEngine->taintUnion(edx, src);
            break;
          }

          case QWORD_SIZE: {
            /* RDX:RAX */
            auto rdx = triton::arch::OperandWrapper(TRITON_X86_REG_RDX);
            auto rax = triton::arch::OperandWrapper(TRITON_X86_REG_RAX);
            auto dividend = triton::ast::concat(this->symbolicEngine->buildSymbolicOperand(inst, rdx), this->symbolicEngine->buildSymbolicOperand(inst, rax));
            /* res = RDX:RAX / Source */
            auto result = triton::ast::extract((QWORD_SIZE_BIT - 1), 0, triton::ast::bvsdiv(dividend, triton::ast::sx(QWORD_SIZE_BIT, divisor)));
            /* mod = RDX:RAX % Source */
            auto mod = triton::ast::extract((QWORD_SIZE_BIT - 1), 0, triton::ast::bvsrem(dividend, triton::ast::sx(QWORD_SIZE_BIT, divisor)));
            /* Create the symbolic expression for RAX */
            auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, result, rax, "IDIV operation");
            /* Apply the taint for EAX */
            expr1->isTainted = this->taintEngine->taintUnion(rax, src);
            /* Create the symbolic expression for RDX */
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, mod, rdx, "IDIV operation");
            /* Apply the taint for EDX */
            expr2->isTainted = this->taintEngine->taintUnion(rdx, src);
            break;
          }

        }

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::imul_s(triton::arch::Instruction& inst) {
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
                auto op1  = this->symbolicEngine->buildSymbolicOperand(inst, al);
                auto op2  = this->symbolicEngine->buildSymbolicOperand(inst, src);
                auto node = triton::ast::bvmul(triton::ast::sx(BYTE_SIZE_BIT, op1), triton::ast::sx(BYTE_SIZE_BIT, op2));
                auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, ax, "IMUL operation");
                expr->isTainted = this->taintEngine->taintUnion(ax, src);
                this->cfImul_s(inst, expr, al, triton::ast::bvmul(op1, op2), node);
                this->ofImul_s(inst, expr, al, triton::ast::bvmul(op1, op2), node);
                break;
              }

              /* dst = DX:AX */
              case WORD_SIZE: {
                auto ax    = triton::arch::OperandWrapper(TRITON_X86_REG_AX);
                auto dx    = triton::arch::OperandWrapper(TRITON_X86_REG_DX);
                auto op1   = this->symbolicEngine->buildSymbolicOperand(inst, ax);
                auto op2   = this->symbolicEngine->buildSymbolicOperand(inst, src);
                auto node  = triton::ast::bvmul(triton::ast::sx(WORD_SIZE_BIT, op1), triton::ast::sx(WORD_SIZE_BIT, op2));
                auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, triton::ast::extract(WORD_SIZE_BIT-1, 0, node), ax, "IMUL operation");
                auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, triton::ast::extract(DWORD_SIZE_BIT-1, WORD_SIZE_BIT, node), dx, "IMUL operation");
                expr1->isTainted = this->taintEngine->taintUnion(ax, src);
                expr2->isTainted = this->taintEngine->taintUnion(dx, ax);
                this->cfImul_s(inst, expr1, ax, triton::ast::bvmul(op1, op2), node);
                this->ofImul_s(inst, expr1, ax, triton::ast::bvmul(op1, op2), node);
                break;
              }

              /* dst = EDX:EAX */
              case DWORD_SIZE: {
                auto eax   = triton::arch::OperandWrapper(TRITON_X86_REG_EAX);
                auto edx   = triton::arch::OperandWrapper(TRITON_X86_REG_EDX);
                auto op1   = this->symbolicEngine->buildSymbolicOperand(inst, eax);
                auto op2   = this->symbolicEngine->buildSymbolicOperand(inst, src);
                auto node  = triton::ast::bvmul(triton::ast::sx(DWORD_SIZE_BIT, op1), triton::ast::sx(DWORD_SIZE_BIT, op2));
                auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, triton::ast::extract(DWORD_SIZE_BIT-1, 0, node), eax, "IMUL operation");
                auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, triton::ast::extract(QWORD_SIZE_BIT-1, DWORD_SIZE_BIT, node), edx, "IMUL operation");
                expr1->isTainted = this->taintEngine->taintUnion(eax, src);
                expr2->isTainted = this->taintEngine->taintUnion(edx, eax);
                this->cfImul_s(inst, expr1, eax, triton::ast::bvmul(op1, op2), node);
                this->ofImul_s(inst, expr1, eax, triton::ast::bvmul(op1, op2), node);
                break;
              }

              /* dst = RDX:RAX */
              case QWORD_SIZE: {
                auto rax   = triton::arch::OperandWrapper(TRITON_X86_REG_RAX);
                auto rdx   = triton::arch::OperandWrapper(TRITON_X86_REG_RDX);
                auto op1   = this->symbolicEngine->buildSymbolicOperand(inst, rax);
                auto op2   = this->symbolicEngine->buildSymbolicOperand(inst, src);
                auto node  = triton::ast::bvmul(triton::ast::sx(QWORD_SIZE_BIT, op1), triton::ast::sx(QWORD_SIZE_BIT, op2));
                auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, triton::ast::extract(QWORD_SIZE_BIT-1, 0, node), rax, "IMUL operation");
                auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, triton::ast::extract(DQWORD_SIZE_BIT-1, QWORD_SIZE_BIT, node), rdx, "IMUL operation");
                expr1->isTainted = this->taintEngine->taintUnion(rax, src);
                expr2->isTainted = this->taintEngine->taintUnion(rdx, rax);
                this->cfImul_s(inst, expr1, rax, triton::ast::bvmul(op1, op2), node);
                this->ofImul_s(inst, expr1, rax, triton::ast::bvmul(op1, op2), node);
                break;
              }

            }
            break;
          }

          /* two operands */
          case 2: {
            auto& dst  = inst.operands[0];
            auto& src  = inst.operands[1];
            auto  op1  = this->symbolicEngine->buildSymbolicOperand(inst, dst);
            auto  op2  = this->symbolicEngine->buildSymbolicOperand(inst, src);
            auto  node = triton::ast::bvmul(triton::ast::sx(dst.getBitSize(), op1), triton::ast::sx(src.getBitSize(), op2));
            auto  expr = this->symbolicEngine->createSymbolicExpression(inst, triton::ast::extract(dst.getBitSize()-1, 0, node), dst, "IMUL operation");
            expr->isTainted = this->taintEngine->taintUnion(dst, src);
            this->cfImul_s(inst, expr, dst, triton::ast::bvmul(op1, op2), node);
            this->ofImul_s(inst, expr, dst, triton::ast::bvmul(op1, op2), node);
            break;
          }

          /* three operands */
          case 3: {
            auto& dst  = inst.operands[0];
            auto& src1 = inst.operands[1];
            auto& src2 = inst.operands[2];
            auto  op2  = this->symbolicEngine->buildSymbolicOperand(inst, src1);
            auto  op3  = this->symbolicEngine->buildSymbolicOperand(inst, src2);
            auto  node = triton::ast::bvmul(triton::ast::sx(src1.getBitSize(), op2), triton::ast::sx(src2.getBitSize(), op3));
            auto  expr = this->symbolicEngine->createSymbolicExpression(inst, triton::ast::extract(dst.getBitSize()-1, 0, node), dst, "IMUL operation");
            expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2));
            this->cfImul_s(inst, expr, dst, triton::ast::bvmul(op2, op3), node);
            this->ofImul_s(inst, expr, dst, triton::ast::bvmul(op2, op3), node);
            break;
          }

        }

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::inc_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = triton::ast::bv(1, dst.getBitSize());

        /* Create the semantics */
        auto node = triton::ast::bvadd(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "INC operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate symbolic flags */
        this->af_s(inst, expr, dst, op1, op2);
        this->ofAdd_s(inst, expr, dst, op1, op2);
        this->pf_s(inst, expr, dst);
        this->sf_s(inst, expr, dst);
        this->zf_s(inst, expr, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::invd_s(triton::arch::Instruction& inst) {
        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::invlpg_s(triton::arch::Instruction& inst) {
        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::ja_s(triton::arch::Instruction& inst) {
        auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
        auto  cf      = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
        auto  zf      = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
        auto  srcImm1 = triton::arch::OperandWrapper(Immediate(inst.getNextAddress(), pc.getSize()));
        auto& srcImm2 = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, cf);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, zf);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm1);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm2);

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Set condition flag */
        if (op1->evaluate().is_zero() && op2->evaluate().is_zero())
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(pc, cf);
        expr->isTainted = this->taintEngine->taintUnion(pc, zf);

        /* Create the path constraint */
        this->symbolicEngine->addPathConstraint(inst, expr);
      }


      void x86Semantics::jae_s(triton::arch::Instruction& inst) {
        auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
        auto  cf      = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
        auto  srcImm1 = triton::arch::OperandWrapper(Immediate(inst.getNextAddress(), pc.getSize()));
        auto& srcImm2 = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, cf);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm1);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm2);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(op1, triton::ast::bvfalse()), op3, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Set condition flag */
        if (op1->evaluate().is_zero())
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(pc, cf);

        /* Create the path constraint */
        this->symbolicEngine->addPathConstraint(inst, expr);
      }


      void x86Semantics::jb_s(triton::arch::Instruction& inst) {
        auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
        auto  cf      = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
        auto  srcImm1 = triton::arch::OperandWrapper(Immediate(inst.getNextAddress(), pc.getSize()));
        auto& srcImm2 = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, cf);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm1);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm2);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(op1, triton::ast::bvtrue()), op3, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Set condition flag */
        if (!op1->evaluate().is_zero())
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(pc, cf);

        /* Create the path constraint */
        this->symbolicEngine->addPathConstraint(inst, expr);
      }


      void x86Semantics::jbe_s(triton::arch::Instruction& inst) {
        auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
        auto  cf      = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
        auto  zf      = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
        auto  srcImm1 = triton::arch::OperandWrapper(Immediate(inst.getNextAddress(), pc.getSize()));
        auto& srcImm2 = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, cf);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, zf);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm1);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm2);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(triton::ast::bvor(op1, op2), triton::ast::bvtrue()), op4, op3);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Set condition flag */
        if (!op1->evaluate().is_zero() || !op2->evaluate().is_zero())
          inst.setConditionTaken(true);


        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(pc, cf);
        expr->isTainted = this->taintEngine->taintUnion(pc, zf);

        /* Create the path constraint */
        this->symbolicEngine->addPathConstraint(inst, expr);
      }


      void x86Semantics::je_s(triton::arch::Instruction& inst) {
        auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
        auto  zf      = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
        auto  srcImm1 = triton::arch::OperandWrapper(Immediate(inst.getNextAddress(), pc.getSize()));
        auto& srcImm2 = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, zf);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm1);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm2);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(op1, triton::ast::bvtrue()), op3, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Set condition flag */
        if (!op1->evaluate().is_zero())
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(pc, zf);

        /* Create the path constraint */
        this->symbolicEngine->addPathConstraint(inst, expr);
      }


      void x86Semantics::jg_s(triton::arch::Instruction& inst) {
        auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
        auto  sf      = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
        auto  of      = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
        auto  zf      = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
        auto  srcImm1 = triton::arch::OperandWrapper(Immediate(inst.getNextAddress(), pc.getSize()));
        auto& srcImm2 = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, sf);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, of);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, zf);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm1);
        auto op5 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm2);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(triton::ast::bvor(triton::ast::bvxor(op1, op2), op3), triton::ast::bvfalse()), op5, op4);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Set condition flag */
        if ((op1->evaluate().is_zero() == op2->evaluate().is_zero()) && op3->evaluate().is_zero())
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(pc, sf);
        expr->isTainted = this->taintEngine->taintUnion(pc, of);
        expr->isTainted = this->taintEngine->taintUnion(pc, zf);

        /* Create the path constraint */
        this->symbolicEngine->addPathConstraint(inst, expr);
      }


      void x86Semantics::jge_s(triton::arch::Instruction& inst) {
        auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
        auto  sf      = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
        auto  of      = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
        auto  srcImm1 = triton::arch::OperandWrapper(Immediate(inst.getNextAddress(), pc.getSize()));
        auto& srcImm2 = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, sf);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, of);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm1);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm2);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(op1, op2), op4, op3);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Set condition flag */
        if (op1->evaluate().is_zero() == op2->evaluate().is_zero())
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(pc, sf);
        expr->isTainted = this->taintEngine->taintUnion(pc, of);

        /* Create the path constraint */
        this->symbolicEngine->addPathConstraint(inst, expr);
      }


      void x86Semantics::jl_s(triton::arch::Instruction& inst) {
        auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
        auto  sf      = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
        auto  of      = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
        auto  srcImm1 = triton::arch::OperandWrapper(Immediate(inst.getNextAddress(), pc.getSize()));
        auto& srcImm2 = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, sf);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, of);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm1);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm2);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(triton::ast::bvxor(op1, op2), triton::ast::bvtrue()), op4, op3);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Set condition flag */
        if (op1->evaluate().is_zero() != op2->evaluate().is_zero())
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(pc, sf);
        expr->isTainted = this->taintEngine->taintUnion(pc, of);

        /* Create the path constraint */
        this->symbolicEngine->addPathConstraint(inst, expr);
      }


      void x86Semantics::jle_s(triton::arch::Instruction& inst) {
        auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
        auto  sf      = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
        auto  of      = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
        auto  zf      = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
        auto  srcImm1 = triton::arch::OperandWrapper(Immediate(inst.getNextAddress(), pc.getSize()));
        auto& srcImm2 = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, sf);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, of);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, zf);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm1);
        auto op5 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm2);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(triton::ast::bvor(triton::ast::bvxor(op1, op2), op3), triton::ast::bvtrue()), op5, op4);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Set condition flag */
        if ((op1->evaluate().is_zero() != op2->evaluate().is_zero()) || !op3->evaluate().is_zero())
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(pc, sf);
        expr->isTainted = this->taintEngine->taintUnion(pc, of);
        expr->isTainted = this->taintEngine->taintUnion(pc, zf);

        /* Create the path constraint */
        this->symbolicEngine->addPathConstraint(inst, expr);
      }


      void x86Semantics::jmp_s(triton::arch::Instruction& inst) {
        auto  pc  = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
        auto& src = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = op1;

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Set condition flag */
        inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(pc, src);

        /* Create the path constraint */
        this->symbolicEngine->addPathConstraint(inst, expr);
      }


      void x86Semantics::jne_s(triton::arch::Instruction& inst) {
        auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
        auto  zf      = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
        auto  srcImm1 = triton::arch::OperandWrapper(Immediate(inst.getNextAddress(), pc.getSize()));
        auto& srcImm2 = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, zf);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm1);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm2);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(op1, triton::ast::bvfalse()), op3, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Set condition flag */
        if (op1->evaluate().is_zero())
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(pc, zf);

        /* Create the path constraint */
        this->symbolicEngine->addPathConstraint(inst, expr);
      }


      void x86Semantics::jno_s(triton::arch::Instruction& inst) {
        auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
        auto  of      = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
        auto  srcImm1 = triton::arch::OperandWrapper(Immediate(inst.getNextAddress(), pc.getSize()));
        auto& srcImm2 = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, of);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm1);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm2);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(op1, triton::ast::bvfalse()), op3, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Set condition flag */
        if (op1->evaluate().is_zero())
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(pc, of);

        /* Create the path constraint */
        this->symbolicEngine->addPathConstraint(inst, expr);
      }


      void x86Semantics::jnp_s(triton::arch::Instruction& inst) {
        auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
        auto  pf      = triton::arch::OperandWrapper(TRITON_X86_REG_PF);
        auto  srcImm1 = triton::arch::OperandWrapper(Immediate(inst.getNextAddress(), pc.getSize()));
        auto& srcImm2 = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, pf);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm1);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm2);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(op1, triton::ast::bvfalse()), op3, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Set condition flag */
        if (op1->evaluate().is_zero())
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(pc, pf);

        /* Create the path constraint */
        this->symbolicEngine->addPathConstraint(inst, expr);
      }


      void x86Semantics::jns_s(triton::arch::Instruction& inst) {
        auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
        auto  sf      = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
        auto  srcImm1 = triton::arch::OperandWrapper(Immediate(inst.getNextAddress(), pc.getSize()));
        auto& srcImm2 = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, sf);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm1);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm2);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(op1, triton::ast::bvfalse()), op3, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Set condition flag */
        if (op1->evaluate().is_zero())
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(pc, sf);

        /* Create the path constraint */
        this->symbolicEngine->addPathConstraint(inst, expr);
      }


      void x86Semantics::jo_s(triton::arch::Instruction& inst) {
        auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
        auto  of      = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
        auto  srcImm1 = triton::arch::OperandWrapper(Immediate(inst.getNextAddress(), pc.getSize()));
        auto& srcImm2 = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, of);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm1);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm2);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(op1, triton::ast::bvtrue()), op3, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Set condition flag */
        if (!op1->evaluate().is_zero())
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(pc, of);

        /* Create the path constraint */
        this->symbolicEngine->addPathConstraint(inst, expr);
      }


      void x86Semantics::jp_s(triton::arch::Instruction& inst) {
        auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
        auto  pf      = triton::arch::OperandWrapper(TRITON_X86_REG_PF);
        auto  srcImm1 = triton::arch::OperandWrapper(Immediate(inst.getNextAddress(), pc.getSize()));
        auto& srcImm2 = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, pf);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm1);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm2);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(op1, triton::ast::bvtrue()), op3, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Set condition flag */
        if (!op1->evaluate().is_zero())
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(pc, pf);

        /* Create the path constraint */
        this->symbolicEngine->addPathConstraint(inst, expr);
      }


      void x86Semantics::js_s(triton::arch::Instruction& inst) {
        auto  pc      = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
        auto  sf      = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
        auto  srcImm1 = triton::arch::OperandWrapper(Immediate(inst.getNextAddress(), pc.getSize()));
        auto& srcImm2 = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, sf);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm1);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, srcImm2);

        /* Create the semantics */
        auto node = triton::ast::ite(triton::ast::equal(op1, triton::ast::bvtrue()), op3, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Set condition flag */
        if (!op1->evaluate().is_zero())
          inst.setConditionTaken(true);

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(pc, sf);

        /* Create the path constraint */
        this->symbolicEngine->addPathConstraint(inst, expr);
      }


      void x86Semantics::lahf_s(triton::arch::Instruction& inst) {
        auto dst  = triton::arch::OperandWrapper(TRITON_X86_REG_AH);
        auto src1 = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
        auto src2 = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
        auto src3 = triton::arch::OperandWrapper(TRITON_X86_REG_AF);
        auto src4 = triton::arch::OperandWrapper(TRITON_X86_REG_PF);
        auto src5 = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src2);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, src3);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, src4);
        auto op5 = this->symbolicEngine->buildSymbolicOperand(inst, src5);

        /* Create the semantics */
        std::list<triton::ast::AbstractNode*> flags;

        flags.push_back(op1);
        flags.push_back(op2);
        flags.push_back(triton::ast::bvfalse());
        flags.push_back(op3);
        flags.push_back(triton::ast::bvfalse());
        flags.push_back(op4);
        flags.push_back(triton::ast::bvtrue());
        flags.push_back(op5);

        auto node = triton::ast::concat(flags);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LAHF operation");

        /* Spread taint */
        this->taintEngine->taintUnion(dst, src1);
        this->taintEngine->taintUnion(dst, src2);
        this->taintEngine->taintUnion(dst, src3);
        this->taintEngine->taintUnion(dst, src4);
        expr->isTainted = this->taintEngine->taintUnion(dst, src5);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::lddqu_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create the semantics */
        auto node = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LDDQU operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::ldmxcsr_s(triton::arch::Instruction& inst) {
        auto  dst = triton::arch::OperandWrapper(TRITON_X86_REG_MXCSR);
        auto& src = inst.operands[0];

        /* Create the semantics */
        auto node = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "LDMXCSR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::lea_s(triton::arch::Instruction& inst) {
        auto& dst                = inst.operands[0].getRegister();
        auto& srcDisp            = inst.operands[1].getMemory().getDisplacement();
        auto& srcBase            = inst.operands[1].getMemory().getBaseRegister();
        auto& srcIndex           = inst.operands[1].getMemory().getIndexRegister();
        auto& srcScale           = inst.operands[1].getMemory().getScale();
        triton::uint32 leaSize   = 0;

        /* Setup LEA size */
        if (this->architecture->isRegisterValid(srcBase))
          leaSize = srcBase.getBitSize();
        else if (this->architecture->isRegisterValid(srcIndex))
          leaSize = srcIndex.getBitSize();
        else
          leaSize = srcDisp.getBitSize();

        /* Create symbolic operands */

        /* Displacement */
        auto op2 = this->symbolicEngine->buildSymbolicImmediate(inst, srcDisp);
        if (leaSize > srcDisp.getBitSize())
          op2 = triton::ast::zx(leaSize - srcDisp.getBitSize(), op2);

        /* Base */
        triton::ast::AbstractNode* op3;
        if (this->architecture->isRegisterValid(srcBase))
          op3 = this->symbolicEngine->buildSymbolicRegister(inst, srcBase);
        else
          op3 = triton::ast::bv(0, leaSize);

        /* Base with PC */
        if (this->architecture->isRegisterValid(srcBase) && (srcBase.getParent().getId() == TRITON_X86_REG_PC.getId()))
          op3 = triton::ast::bvadd(op3, triton::ast::bv(inst.getSize(), leaSize));

        /* Index */
        triton::ast::AbstractNode* op4;
        if (this->architecture->isRegisterValid(srcIndex))
          op4 = this->symbolicEngine->buildSymbolicRegister(inst, srcIndex);
        else
          op4 = triton::ast::bv(0, leaSize);

        /* Scale */
        auto op5 = this->symbolicEngine->buildSymbolicImmediate(inst, srcScale);
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
        auto expr = this->symbolicEngine->createSymbolicRegisterExpression(inst, node, dst, "LEA operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->setTaint(dst, this->taintEngine->isTainted(srcBase) | this->taintEngine->isTainted(srcIndex));

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::leave_s(triton::arch::Instruction& inst) {
        auto stack     = TRITON_X86_REG_SP.getParent();
        auto base      = TRITON_X86_REG_BP.getParent();
        auto baseValue = this->architecture->getConcreteRegisterValue(base).convert_to<triton::uint64>();
        auto bp1       = triton::arch::OperandWrapper(triton::arch::MemoryAccess(baseValue, base.getSize()));
        auto bp2       = triton::arch::OperandWrapper(TRITON_X86_REG_BP.getParent());
        auto sp        = triton::arch::OperandWrapper(stack);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, bp2);

        /* RSP = RBP */
        auto node1 = op1;

        /* Create the symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, sp, "Stack Pointer");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(sp, bp2);

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, bp1);

        /* RBP = pop() */
        auto node2 = op2;

        /* Create the symbolic expression */
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, bp2, "Stack Top Pointer");

        /* Spread taint */
        expr2->isTainted = this->taintEngine->taintAssignment(bp2, bp1);

        /* Create the semantics - side effect */
        alignAddStack_s(inst, bp1.getSize());

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::lfence_s(triton::arch::Instruction& inst) {
        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::lodsb_s(triton::arch::Instruction& inst) {
        auto& dst    = inst.operands[0];
        auto& src    = inst.operands[1];
        auto  index  = triton::arch::OperandWrapper(TRITON_X86_REG_SI.getParent());
        auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, index);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, df);

        /* Create the semantics */
        auto node1 = op1;
        auto node2 = triton::ast::ite(
                       triton::ast::equal(op3, triton::ast::bvfalse()),
                       triton::ast::bvadd(op2, triton::ast::bv(BYTE_SIZE, index.getBitSize())),
                       triton::ast::bvsub(op2, triton::ast::bv(BYTE_SIZE, index.getBitSize()))
                     );

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "LODSB operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, index, "Index operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst, src);
        expr2->isTainted = this->taintEngine->taintUnion(index, index);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::lodsd_s(triton::arch::Instruction& inst) {
        auto& dst    = inst.operands[0];
        auto& src    = inst.operands[1];
        auto  index  = triton::arch::OperandWrapper(TRITON_X86_REG_SI.getParent());
        auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, index);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, df);

        /* Create the semantics */
        auto node1 = op1;
        auto node2 = triton::ast::ite(
                       triton::ast::equal(op3, triton::ast::bvfalse()),
                       triton::ast::bvadd(op2, triton::ast::bv(DWORD_SIZE, index.getBitSize())),
                       triton::ast::bvsub(op2, triton::ast::bv(DWORD_SIZE, index.getBitSize()))
                     );

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "LODSD operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, index, "Index operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst, src);
        expr2->isTainted = this->taintEngine->taintUnion(index, index);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::lodsq_s(triton::arch::Instruction& inst) {
        auto& dst    = inst.operands[0];
        auto& src    = inst.operands[1];
        auto  index  = triton::arch::OperandWrapper(TRITON_X86_REG_SI.getParent());
        auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, index);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, df);

        /* Create the semantics */
        auto node1 = op1;
        auto node2 = triton::ast::ite(
                       triton::ast::equal(op3, triton::ast::bvfalse()),
                       triton::ast::bvadd(op2, triton::ast::bv(QWORD_SIZE, index.getBitSize())),
                       triton::ast::bvsub(op2, triton::ast::bv(QWORD_SIZE, index.getBitSize()))
                     );

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "LODSQ operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, index, "Index operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst, src);
        expr2->isTainted = this->taintEngine->taintUnion(index, index);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::lodsw_s(triton::arch::Instruction& inst) {
        auto& dst    = inst.operands[0];
        auto& src    = inst.operands[1];
        auto  index  = triton::arch::OperandWrapper(TRITON_X86_REG_SI.getParent());
        auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, index);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, df);

        /* Create the semantics */
        auto node1 = op1;
        auto node2 = triton::ast::ite(
                       triton::ast::equal(op3, triton::ast::bvfalse()),
                       triton::ast::bvadd(op2, triton::ast::bv(WORD_SIZE, index.getBitSize())),
                       triton::ast::bvsub(op2, triton::ast::bv(WORD_SIZE, index.getBitSize()))
                     );

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "LODSW operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, index, "Index operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst, src);
        expr2->isTainted = this->taintEngine->taintUnion(index, index);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::mfence_s(triton::arch::Instruction& inst) {
        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::mov_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create the semantics */
        auto node = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /*
         * Special cases:
         *
         * Triton defines segment registers as 32 or 64  bits vector to
         * avoid to simulate the GDT which allows users to directly define
         * their segments offset.
         *
         * The code below, handles the case: MOV r/m{16/32/64}, Sreg
         */
        if (src.getType() == triton::arch::OP_REG) {
          uint32 id = src.getConstRegister().getId();
          if (id >= triton::arch::x86::ID_REG_CS && id <= triton::arch::x86::ID_REG_SS) {
            node = triton::ast::extract(dst.getBitSize()-1, 0, node);
          }
        }

        /*
         * The code below, handles the case: MOV Sreg, r/m{16/32/64}
         */
        if (dst.getType() == triton::arch::OP_REG) {
          uint32 id = dst.getConstRegister().getId();
          if (id >= triton::arch::x86::ID_REG_CS && id <= triton::arch::x86::ID_REG_SS) {
            node = triton::ast::extract(WORD_SIZE_BIT-1, 0, node);
          }
        }

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOV operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movabs_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create the semantics */
        auto node = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVABS operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movapd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create the semantics */
        auto node = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVAPD operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movaps_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create the semantics */
        auto node = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVAPS operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVD operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movddup_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::concat(triton::ast::extract(QWORD_SIZE_BIT-1, 0, op2), triton::ast::extract(QWORD_SIZE_BIT-1, 0, op2));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVDDUP operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movdq2q_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::extract(QWORD_SIZE_BIT-1, 0, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVDQ2Q operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movdqa_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create the semantics */
        auto node = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVDQA operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movdqu_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create the semantics */
        auto node = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVDQU operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movhlps_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::concat(
                      triton::ast::extract((DQWORD_SIZE_BIT - 1), QWORD_SIZE_BIT, op1), /* Destination[127..64] unchanged */
                      triton::ast::extract((DQWORD_SIZE_BIT - 1), QWORD_SIZE_BIT, op2)  /* Destination[63..0] = Source[127..64]; */
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVHLPS operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movhpd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        triton::ast::AbstractNode* node = nullptr;

        /* xmm, m64 */
        if (dst.getSize() == DQWORD_SIZE) {
          node = triton::ast::concat(
                   triton::ast::extract((QWORD_SIZE_BIT - 1), 0, op2), /* Destination[127..64] = Source */
                   triton::ast::extract((QWORD_SIZE_BIT - 1), 0, op1)  /* Destination[63..0] unchanged */
                 );
        }

        /* m64, xmm */
        else {
          node = triton::ast::extract((DQWORD_SIZE_BIT - 1), QWORD_SIZE_BIT, op2); /* Destination[63..00] = Source[127..64] */
        }

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVHPD operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movhps_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        triton::ast::AbstractNode* node = nullptr;

        /* xmm, m64 */
        if (dst.getSize() == DQWORD_SIZE) {
          node = triton::ast::concat(
                   triton::ast::extract((QWORD_SIZE_BIT - 1), 0, op2), /* Destination[127..64] = Source */
                   triton::ast::extract((QWORD_SIZE_BIT - 1), 0, op1)  /* Destination[63..0] unchanged */
                 );
        }

        /* m64, xmm */
        else {
          node = triton::ast::extract((DQWORD_SIZE_BIT - 1), QWORD_SIZE_BIT, op2); /* Destination[63..00] = Source[127..64] */
        }

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVHPS operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movlhps_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::concat(
                      triton::ast::extract((QWORD_SIZE_BIT - 1), 0, op2), /* Destination[127..64] = Source[63..0] */
                      triton::ast::extract((QWORD_SIZE_BIT - 1), 0, op1)  /* Destination[63..0] unchanged */
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVLHPS operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movlpd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        triton::ast::AbstractNode* node = nullptr;

        /* xmm, m64 */
        if (dst.getSize() == DQWORD_SIZE) {
          node = triton::ast::concat(
                   triton::ast::extract((DQWORD_SIZE_BIT - 1), QWORD_SIZE_BIT, op1), /* Destination[127..64] unchanged */
                   triton::ast::extract((QWORD_SIZE_BIT - 1), 0, op2)                /* Destination[63..0] = Source */
                 );
        }

        /* m64, xmm */
        else {
          node = triton::ast::extract((QWORD_SIZE_BIT - 1), 0, op2); /* Destination = Source[63..00] */
        }

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVLPD operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movlps_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        triton::ast::AbstractNode* node = nullptr;

        /* xmm, m64 */
        if (dst.getSize() == DQWORD_SIZE) {
          node = triton::ast::concat(
                   triton::ast::extract((DQWORD_SIZE_BIT - 1), QWORD_SIZE_BIT, op1), /* Destination[127..64] unchanged */
                   triton::ast::extract((QWORD_SIZE_BIT - 1), 0, op2)                /* Destination[63..0] = Source */
                 );
        }

        /* m64, xmm */
        else {
          node = triton::ast::extract((QWORD_SIZE_BIT - 1), 0, op2); /* Destination = Source[63..00] */
        }

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVLPS operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movmskpd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::zx(30,                       /* Destination[2..31] = 0        */
                      triton::ast::concat(
                        triton::ast::extract(127, 127, op2),  /* Destination[1] = Source[127]; */
                        triton::ast::extract(63, 63, op2)     /* Destination[0] = Source[63];  */
                      )
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVMSKPD operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movmskps_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        std::list<triton::ast::AbstractNode*> signs;

        signs.push_back(triton::ast::extract(127, 127, op2)); /* Destination[3] = Source[127]; */
        signs.push_back(triton::ast::extract(95, 95,   op2)); /* Destination[2] = Source[95];  */
        signs.push_back(triton::ast::extract(63, 63,   op2)); /* Destination[1] = Source[63];  */
        signs.push_back(triton::ast::extract(31, 31,   op2)); /* Destination[0] = Source[31];  */

        auto node = triton::ast::zx(28, triton::ast::concat(signs));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVMSKPS operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movntdq_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create the semantics */
        auto node = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVNTDQ operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movnti_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create the semantics */
        auto node = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVNTI operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movntpd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create the semantics */
        auto node = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVNTPD operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movntps_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create the semantics */
        auto node = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVNTPS operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movntq_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create the semantics */
        auto node = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVNTQ operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movshdup_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        std::list<triton::ast::AbstractNode*> bytes;

        bytes.push_back(triton::ast::extract(127, 96, op2));
        bytes.push_back(triton::ast::extract(127, 96, op2));
        bytes.push_back(triton::ast::extract(63, 32, op2));
        bytes.push_back(triton::ast::extract(63, 32, op2));

        auto node = triton::ast::concat(bytes);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVSHDUP operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movsldup_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        std::list<triton::ast::AbstractNode*> bytes;

        bytes.push_back(triton::ast::extract(95, 64, op2));
        bytes.push_back(triton::ast::extract(95, 64, op2));
        bytes.push_back(triton::ast::extract(31, 0, op2));
        bytes.push_back(triton::ast::extract(31, 0, op2));

        auto node = triton::ast::concat(bytes);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVSLDUP operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movq_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
          throw triton::exceptions::Semantics("x86Semantics::movq_s(): Invalid operation.");

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVQ operation");

        /* Spread taint */
        if (dst.getBitSize() == DQWORD_SIZE_BIT && src.getBitSize() == DQWORD_SIZE_BIT)
          expr->isTainted = this->taintEngine->taintUnion(dst, src);
        else
          expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movq2dq_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::zx(QWORD_SIZE_BIT, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVQ2DQ operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movsb_s(triton::arch::Instruction& inst) {
        auto& dst    = inst.operands[0];
        auto& src    = inst.operands[1];
        auto  index1 = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
        auto  index2 = triton::arch::OperandWrapper(TRITON_X86_REG_SI.getParent());
        auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, index1);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, index2);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, df);

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
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "MOVSB operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, index1, "Index (DI) operation");
        auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, index2, "Index (SI) operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst, src);
        expr2->isTainted = this->taintEngine->taintUnion(index1, index1);
        expr3->isTainted = this->taintEngine->taintUnion(index2, index2);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movsd_s(triton::arch::Instruction& inst) {
        auto& dst    = inst.operands[0];
        auto& src    = inst.operands[1];
        auto  index1 = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
        auto  index2 = triton::arch::OperandWrapper(TRITON_X86_REG_SI.getParent());
        auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, index1);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, index2);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, df);

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
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "MOVSD operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, index1, "Index (DI) operation");
        auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, index2, "Index (SI) operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst, src);
        expr2->isTainted = this->taintEngine->taintUnion(index1, index1);
        expr3->isTainted = this->taintEngine->taintUnion(index2, index2);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movupd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create the semantics */
        auto node = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVUPD operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movups_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create the semantics */
        auto node = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVUPS operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movsq_s(triton::arch::Instruction& inst) {
        auto& dst    = inst.operands[0];
        auto& src    = inst.operands[1];
        auto  index1 = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
        auto  index2 = triton::arch::OperandWrapper(TRITON_X86_REG_SI.getParent());
        auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, index1);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, index2);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, df);

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
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "MOVSQ operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, index1, "Index (DI) operation");
        auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, index2, "Index (SI) operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst, src);
        expr2->isTainted = this->taintEngine->taintUnion(index1, index1);
        expr3->isTainted = this->taintEngine->taintUnion(index2, index2);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movsw_s(triton::arch::Instruction& inst) {
        auto& dst    = inst.operands[0];
        auto& src    = inst.operands[1];
        auto  index1 = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
        auto  index2 = triton::arch::OperandWrapper(TRITON_X86_REG_SI.getParent());
        auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, index1);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, index2);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, df);

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
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "MOVSW operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, index1, "Index (DI) operation");
        auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, index2, "Index (SI) operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst, src);
        expr2->isTainted = this->taintEngine->taintUnion(index1, index1);
        expr3->isTainted = this->taintEngine->taintUnion(index2, index2);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movsx_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::sx(dst.getBitSize() - src.getBitSize(), op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVSX operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movsxd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::sx(dst.getBitSize() - src.getBitSize(), op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVSXD operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::movzx_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::zx(dst.getBitSize() - src.getBitSize(), op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MOVZX operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::mul_s(triton::arch::Instruction& inst) {
        auto& src2 = inst.operands[0];

        switch (src2.getSize()) {

          /* AX = AL * r/m8 */
          case BYTE_SIZE: {
            auto dst  = triton::arch::OperandWrapper(TRITON_X86_REG_AX);
            auto src1 = triton::arch::OperandWrapper(TRITON_X86_REG_AL);
            /* Create symbolic operands */
            auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
            auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src2);
            /* Create the semantics */
            auto node = triton::ast::bvmul(triton::ast::zx(BYTE_SIZE_BIT, op1), triton::ast::zx(BYTE_SIZE_BIT, op2));
            /* Create symbolic expression */
            auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "MUL operation");
            /* Apply the taint */
            expr->isTainted = this->taintEngine->taintUnion(dst, src2);
            /* Upate symbolic flags */
            auto ah = triton::ast::extract((WORD_SIZE_BIT - 1), BYTE_SIZE_BIT, node);
            this->cfMul_s(inst, expr, src2, ah);
            this->ofMul_s(inst, expr, src2, ah);
            break;
          }

          /* DX:AX = AX * r/m16 */
          case WORD_SIZE: {
            auto dst1 = triton::arch::OperandWrapper(TRITON_X86_REG_AX);
            auto dst2 = triton::arch::OperandWrapper(TRITON_X86_REG_DX);
            auto src1 = triton::arch::OperandWrapper(TRITON_X86_REG_AX);
            /* Create symbolic operands */
            auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
            auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src2);
            /* Create the semantics */
            auto node = triton::ast::bvmul(triton::ast::zx(WORD_SIZE_BIT, op1), triton::ast::zx(WORD_SIZE_BIT, op2));
            /* Create symbolic expression for ax */
            auto ax = triton::ast::extract((WORD_SIZE_BIT - 1), 0, node);
            auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, ax, dst1, "MUL operation");
            /* Apply the taint */
            expr1->isTainted = this->taintEngine->taintUnion(dst1, src2);
            /* Create symbolic expression for dx */
            auto dx = triton::ast::extract((DWORD_SIZE_BIT - 1), WORD_SIZE_BIT, node);
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, dx, dst2, "MUL operation");
            /* Apply the taint */
            expr2->isTainted = this->taintEngine->taintUnion(dst2, src2);
            expr2->isTainted = this->taintEngine->taintUnion(dst2, src1);
            /* Upate symbolic flags */
            this->cfMul_s(inst, expr2, src2, dx);
            this->ofMul_s(inst, expr2, src2, dx);
            break;
          }

          /* EDX:EAX = EAX * r/m32 */
          case DWORD_SIZE: {
            auto dst1 = triton::arch::OperandWrapper(TRITON_X86_REG_EAX);
            auto dst2 = triton::arch::OperandWrapper(TRITON_X86_REG_EDX);
            auto src1 = triton::arch::OperandWrapper(TRITON_X86_REG_EAX);
            /* Create symbolic operands */
            auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
            auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src2);
            /* Create the semantics */
            auto node = triton::ast::bvmul(triton::ast::zx(DWORD_SIZE_BIT, op1), triton::ast::zx(DWORD_SIZE_BIT, op2));
            /* Create symbolic expression for eax */
            auto eax = triton::ast::extract((DWORD_SIZE_BIT - 1), 0, node);
            auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, eax, dst1, "MUL operation");
            /* Apply the taint */
            expr1->isTainted = this->taintEngine->taintUnion(dst1, src2);
            /* Create symbolic expression for edx */
            auto edx = triton::ast::extract((QWORD_SIZE_BIT - 1), DWORD_SIZE_BIT, node);
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, edx, dst2, "MUL operation");
            /* Apply the taint */
            expr2->isTainted = this->taintEngine->taintUnion(dst2, src2);
            expr2->isTainted = this->taintEngine->taintUnion(dst2, src1);
            /* Upate symbolic flags */
            this->cfMul_s(inst, expr2, src2, edx);
            this->ofMul_s(inst, expr2, src2, edx);
            break;
          }

          /* RDX:RAX = RAX * r/m64 */
          case QWORD_SIZE: {
            auto dst1 = triton::arch::OperandWrapper(TRITON_X86_REG_RAX);
            auto dst2 = triton::arch::OperandWrapper(TRITON_X86_REG_RDX);
            auto src1 = triton::arch::OperandWrapper(TRITON_X86_REG_RAX);
            /* Create symbolic operands */
            auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
            auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src2);
            /* Create the semantics */
            auto node = triton::ast::bvmul(triton::ast::zx(QWORD_SIZE_BIT, op1), triton::ast::zx(QWORD_SIZE_BIT, op2));
            /* Create symbolic expression for eax */
            auto rax = triton::ast::extract((QWORD_SIZE_BIT - 1), 0, node);
            auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, rax, dst1, "MUL operation");
            /* Apply the taint */
            expr1->isTainted = this->taintEngine->taintUnion(dst1, src2);
            /* Create symbolic expression for rdx */
            auto rdx = triton::ast::extract((DQWORD_SIZE_BIT - 1), QWORD_SIZE_BIT, node);
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, rdx, dst2, "MUL operation");
            /* Apply the taint */
            expr2->isTainted = this->taintEngine->taintUnion(dst2, src2);
            expr2->isTainted = this->taintEngine->taintUnion(dst2, src1);
            /* Upate symbolic flags */
            this->cfMul_s(inst, expr2, src2, rdx);
            this->ofMul_s(inst, expr2, src2, rdx);
            break;
          }

        }

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::mulx_s(triton::arch::Instruction& inst) {
        switch (inst.operands[0].getSize()) {

          /* r32a, r32b, r/m32 */
          case DWORD_SIZE: {
            auto& dst1 = inst.operands[0];
            auto& dst2 = inst.operands[1];
            auto  src1 = inst.operands[2];
            auto  src2 = triton::arch::OperandWrapper(TRITON_X86_REG_EDX);

            /* Create symbolic operands */
            auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
            auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src2);

            /* Create the semantics */
            auto node  = triton::ast::bvmul(triton::ast::zx(DWORD_SIZE_BIT, op1), triton::ast::zx(DWORD_SIZE_BIT, op2));
            auto node1 = triton::ast::extract((DWORD_SIZE_BIT - 1), 0, node);
            auto node2 = triton::ast::extract((QWORD_SIZE_BIT - 1), DWORD_SIZE_BIT, node);

            /* Create symbolic expression for eax */
            auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst2, "MULX operation");
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, dst1, "MULX operation");

            /* Apply the taint */
            expr1->isTainted = this->taintEngine->taintUnion(dst2, src1);
            expr1->isTainted = this->taintEngine->taintUnion(dst2, src2);

            expr2->isTainted = this->taintEngine->taintUnion(dst1, src1);
            expr2->isTainted = this->taintEngine->taintUnion(dst1, src2);
            break;
          }

          /* r64a, r64b, r/m64 */
          case QWORD_SIZE: {
            auto& dst1 = inst.operands[0];
            auto& dst2 = inst.operands[1];
            auto  src1 = inst.operands[2];
            auto  src2 = triton::arch::OperandWrapper(TRITON_X86_REG_RDX);

            /* Create symbolic operands */
            auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
            auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src2);

            /* Create the semantics */
            auto node  = triton::ast::bvmul(triton::ast::zx(QWORD_SIZE_BIT, op1), triton::ast::zx(QWORD_SIZE_BIT, op2));
            auto node1 = triton::ast::extract((QWORD_SIZE_BIT - 1), 0, node);
            auto node2 = triton::ast::extract((DQWORD_SIZE_BIT - 1), QWORD_SIZE_BIT, node);

            /* Create symbolic expression for eax */
            auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst2, "MULX operation");
            auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, dst1, "MULX operation");

            /* Apply the taint */
            expr1->isTainted = this->taintEngine->taintUnion(dst2, src1);
            expr1->isTainted = this->taintEngine->taintUnion(dst2, src2);

            expr2->isTainted = this->taintEngine->taintUnion(dst1, src1);
            expr2->isTainted = this->taintEngine->taintUnion(dst1, src2);
            break;
          }

        }

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::neg_s(triton::arch::Instruction& inst) {
        auto& src = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::bvneg(op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, src, "NEG operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintUnion(src, src);

        /* Upate symbolic flags */
        this->afNeg_s(inst, expr, src, op1);
        this->cfNeg_s(inst, expr, src, op1);
        this->ofNeg_s(inst, expr, src, op1);
        this->pf_s(inst, expr, src);
        this->sf_s(inst, expr, src);
        this->zf_s(inst, expr, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::nop_s(triton::arch::Instruction& inst) {
        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::not_s(triton::arch::Instruction& inst) {
        auto& src = inst.operands[0];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::bvnot(op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, src, "NOT operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintUnion(src, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::or_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::bvor(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "OR operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate symbolic flags */
        this->clearFlag_s(inst, TRITON_X86_REG_CF, "Clears carry flag");
        this->clearFlag_s(inst, TRITON_X86_REG_OF, "Clears overflow flag");
        this->pf_s(inst, expr, dst);
        this->sf_s(inst, expr, dst);
        this->zf_s(inst, expr, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::orpd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::bvor(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ORPD operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::orps_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::bvor(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ORPS operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::paddb_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
            throw triton::exceptions::Semantics("x86Semantics::paddb_s(): Invalid operand size.");

        }

        auto node = triton::ast::concat(packed);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PADDB operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::paddd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
            throw triton::exceptions::Semantics("x86Semantics::paddd_s(): Invalid operand size.");

        }

        auto node = triton::ast::concat(packed);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PADDD operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::paddq_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
            throw triton::exceptions::Semantics("x86Semantics::paddq_s(): Invalid operand size.");

        }

        auto node = triton::ast::concat(packed);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PADDQ operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::paddw_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
            throw triton::exceptions::Semantics("x86Semantics::paddw_s(): Invalid operand size.");

        }

        auto node = triton::ast::concat(packed);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PADDW operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pand_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::bvand(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PAND operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pandn_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::bvand(triton::ast::bvnot(op1), op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PANDN operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pause_s(triton::arch::Instruction& inst) {
        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pavgb_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        std::list<triton::ast::AbstractNode*> pck;

        for (triton::uint32 index = 0; index < dst.getSize(); index++) {
          uint32 high = (dst.getBitSize() - 1) - (index * BYTE_SIZE_BIT);
          uint32 low  = (dst.getBitSize() - BYTE_SIZE_BIT) - (index * BYTE_SIZE_BIT);
          pck.push_back(
            triton::ast::extract(BYTE_SIZE_BIT-1, 0,
              triton::ast::bvlshr(
                triton::ast::bvadd(
                  triton::ast::bvadd(
                    triton::ast::zx(1, triton::ast::extract(high, low, op1)),
                    triton::ast::zx(1, triton::ast::extract(high, low, op2))
                  ),
                  triton::ast::bv(1, BYTE_SIZE_BIT+1)
                ),
                triton::ast::bv(1, BYTE_SIZE_BIT+1)
              )
            )
          );
        }

        auto node = triton::ast::concat(pck);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PAVGB operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pavgw_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        std::list<triton::ast::AbstractNode*> pck;

        for (triton::uint32 index = 0; index < dst.getSize() / WORD_SIZE; index++) {
          uint32 high = (dst.getBitSize() - 1) - (index * WORD_SIZE_BIT);
          uint32 low  = (dst.getBitSize() - WORD_SIZE_BIT) - (index * WORD_SIZE_BIT);
          pck.push_back(
            triton::ast::extract(WORD_SIZE_BIT-1, 0,
              triton::ast::bvlshr(
                triton::ast::bvadd(
                  triton::ast::bvadd(
                    triton::ast::zx(1, triton::ast::extract(high, low, op1)),
                    triton::ast::zx(1, triton::ast::extract(high, low, op2))
                  ),
                  triton::ast::bv(1, WORD_SIZE_BIT+1)
                ),
                triton::ast::bv(1, WORD_SIZE_BIT+1)
              )
            )
          );
        }

        auto node = triton::ast::concat(pck);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PAVGW operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pcmpeqb_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PCMPEQB operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pcmpeqd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PCMPEQD operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pcmpeqw_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PCMPEQW operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pcmpgtb_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PCMPGTB operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pcmpgtd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PCMPGTD operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pcmpgtw_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PCMPGTW operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pmaxsb_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PMAXSB operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pmaxsd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PMAXSD operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pmaxsw_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PMAXSW operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pmaxub_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PMAXUB operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pmaxud_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PMAXUD operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pmaxuw_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PMAXUW operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pminsb_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PMINSB operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pminsd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PMINSD operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pminsw_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PMINSW operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pminub_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PMINUB operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pminud_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PMINUD operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pminuw_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PMINUW operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pmovmskb_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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

        auto node = triton::ast::zx(
                      dst.getBitSize() - static_cast<triton::uint32>(mskb.size()),
                      triton::ast::concat(mskb)
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PMOVMSKB operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pmovsxbd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        std::list<triton::ast::AbstractNode *> pck;

        pck.push_back(triton::ast::sx(DWORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(31, 24, op2)));
        pck.push_back(triton::ast::sx(DWORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(23, 16, op2)));
        pck.push_back(triton::ast::sx(DWORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(15, 8,  op2)));
        pck.push_back(triton::ast::sx(DWORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(7,  0,  op2)));

        auto node = triton::ast::concat(pck);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PMOVSXBD operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pmovsxbq_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        std::list<triton::ast::AbstractNode *> pck;

        pck.push_back(triton::ast::sx(QWORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(15, 8,  op2)));
        pck.push_back(triton::ast::sx(QWORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(7,  0,  op2)));

        auto node = triton::ast::concat(pck);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PMOVSXBQ operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pmovsxbw_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        std::list<triton::ast::AbstractNode *> pck;

        pck.push_back(triton::ast::sx(WORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(63, 56, op2)));
        pck.push_back(triton::ast::sx(WORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(55, 48, op2)));
        pck.push_back(triton::ast::sx(WORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(47, 40, op2)));
        pck.push_back(triton::ast::sx(WORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(39, 32, op2)));
        pck.push_back(triton::ast::sx(WORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(31, 24, op2)));
        pck.push_back(triton::ast::sx(WORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(23, 16, op2)));
        pck.push_back(triton::ast::sx(WORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(15, 8,  op2)));
        pck.push_back(triton::ast::sx(WORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(7,  0,  op2)));

        auto node = triton::ast::concat(pck);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PMOVSXBW operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pmovsxdq_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        std::list<triton::ast::AbstractNode *> pck;

        pck.push_back(triton::ast::sx(QWORD_SIZE_BIT - DWORD_SIZE_BIT, triton::ast::extract(63, 32, op2)));
        pck.push_back(triton::ast::sx(QWORD_SIZE_BIT - DWORD_SIZE_BIT, triton::ast::extract(31, 0,  op2)));

        auto node = triton::ast::concat(pck);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PMOVSXDQ operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pmovsxwd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        std::list<triton::ast::AbstractNode *> pck;

        pck.push_back(triton::ast::sx(DWORD_SIZE_BIT - WORD_SIZE_BIT, triton::ast::extract(63, 48, op2)));
        pck.push_back(triton::ast::sx(DWORD_SIZE_BIT - WORD_SIZE_BIT, triton::ast::extract(47, 32, op2)));
        pck.push_back(triton::ast::sx(DWORD_SIZE_BIT - WORD_SIZE_BIT, triton::ast::extract(31, 16, op2)));
        pck.push_back(triton::ast::sx(DWORD_SIZE_BIT - WORD_SIZE_BIT, triton::ast::extract(15, 0,  op2)));

        auto node = triton::ast::concat(pck);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PMOVSXWD operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pmovsxwq_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        std::list<triton::ast::AbstractNode *> pck;

        pck.push_back(triton::ast::sx(QWORD_SIZE_BIT - WORD_SIZE_BIT, triton::ast::extract(31, 16, op2)));
        pck.push_back(triton::ast::sx(QWORD_SIZE_BIT - WORD_SIZE_BIT, triton::ast::extract(15, 0,  op2)));

        auto node = triton::ast::concat(pck);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PMOVSXWQ operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pmovzxbd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        std::list<triton::ast::AbstractNode *> pck;

        pck.push_back(triton::ast::zx(DWORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(31, 24, op2)));
        pck.push_back(triton::ast::zx(DWORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(23, 16, op2)));
        pck.push_back(triton::ast::zx(DWORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(15, 8,  op2)));
        pck.push_back(triton::ast::zx(DWORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(7,  0,  op2)));

        auto node = triton::ast::concat(pck);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PMOVZXBD operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pmovzxbq_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        std::list<triton::ast::AbstractNode *> pck;

        pck.push_back(triton::ast::zx(QWORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(15, 8,  op2)));
        pck.push_back(triton::ast::zx(QWORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(7,  0,  op2)));

        auto node = triton::ast::concat(pck);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PMOVZXBQ operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pmovzxbw_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        std::list<triton::ast::AbstractNode *> pck;

        pck.push_back(triton::ast::zx(WORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(63, 56, op2)));
        pck.push_back(triton::ast::zx(WORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(55, 48, op2)));
        pck.push_back(triton::ast::zx(WORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(47, 40, op2)));
        pck.push_back(triton::ast::zx(WORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(39, 32, op2)));
        pck.push_back(triton::ast::zx(WORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(31, 24, op2)));
        pck.push_back(triton::ast::zx(WORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(23, 16, op2)));
        pck.push_back(triton::ast::zx(WORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(15, 8,  op2)));
        pck.push_back(triton::ast::zx(WORD_SIZE_BIT - BYTE_SIZE_BIT, triton::ast::extract(7,  0,  op2)));

        auto node = triton::ast::concat(pck);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PMOVZXBW operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pmovzxdq_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        std::list<triton::ast::AbstractNode *> pck;

        pck.push_back(triton::ast::zx(QWORD_SIZE_BIT - DWORD_SIZE_BIT, triton::ast::extract(63, 32, op2)));
        pck.push_back(triton::ast::zx(QWORD_SIZE_BIT - DWORD_SIZE_BIT, triton::ast::extract(31, 0,  op2)));

        auto node = triton::ast::concat(pck);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PMOVZXDQ operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pmovzxwd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        std::list<triton::ast::AbstractNode *> pck;

        pck.push_back(triton::ast::zx(DWORD_SIZE_BIT - WORD_SIZE_BIT, triton::ast::extract(63, 48, op2)));
        pck.push_back(triton::ast::zx(DWORD_SIZE_BIT - WORD_SIZE_BIT, triton::ast::extract(47, 32, op2)));
        pck.push_back(triton::ast::zx(DWORD_SIZE_BIT - WORD_SIZE_BIT, triton::ast::extract(31, 16, op2)));
        pck.push_back(triton::ast::zx(DWORD_SIZE_BIT - WORD_SIZE_BIT, triton::ast::extract(15, 0,  op2)));

        auto node = triton::ast::concat(pck);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PMOVZXWD operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pmovzxwq_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        std::list<triton::ast::AbstractNode *> pck;

        pck.push_back(triton::ast::zx(QWORD_SIZE_BIT - WORD_SIZE_BIT, triton::ast::extract(31, 16, op2)));
        pck.push_back(triton::ast::zx(QWORD_SIZE_BIT - WORD_SIZE_BIT, triton::ast::extract(15, 0,  op2)));

        auto node = triton::ast::concat(pck);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PMOVZXWQ operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pop_s(triton::arch::Instruction& inst) {
        bool  stackRelative = false;
        auto  stack         = TRITON_X86_REG_SP.getParent();
        auto  stackValue    = this->architecture->getConcreteRegisterValue(stack).convert_to<triton::uint64>();
        auto& dst           = inst.operands[0];
        auto  src           = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue, dst.getSize()));

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = op1;

        /*
         * Create the semantics - side effect
         *
         * Intel: If the ESP register is used as a base register for addressing a destination operand in
         * memory, the POP instruction computes the effective address of the operand after it increments
         * the ESP register.
         */
        if (dst.getType() == triton::arch::OP_MEM) {
          if (dst.getMemory().getBaseRegister().getParent().getId() == stack.getId()) {
            /* Align the stack */
            alignAddStack_s(inst, src.getSize());

            /* Re-initialize the memory access */
            this->symbolicEngine->initLeaAst(dst.getMemory(), triton::arch::FORCE_MEMORY_INITIALIZATION);

            stackRelative = true;
          }
        }

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "POP operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Create the semantics - side effect */
        if (!stackRelative)
          alignAddStack_s(inst, src.getSize());

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::popal_s(triton::arch::Instruction& inst) {
        auto stack      = TRITON_X86_REG_SP.getParent();
        auto stackValue = this->architecture->getConcreteRegisterValue(stack).convert_to<triton::uint64>();
        auto dst1       = triton::arch::OperandWrapper(TRITON_X86_REG_EDI);
        auto dst2       = triton::arch::OperandWrapper(TRITON_X86_REG_ESI);
        auto dst3       = triton::arch::OperandWrapper(TRITON_X86_REG_EBP);
        auto dst4       = triton::arch::OperandWrapper(TRITON_X86_REG_ESP);
        auto dst5       = triton::arch::OperandWrapper(TRITON_X86_REG_EBX);
        auto dst6       = triton::arch::OperandWrapper(TRITON_X86_REG_EDX);
        auto dst7       = triton::arch::OperandWrapper(TRITON_X86_REG_ECX);
        auto dst8       = triton::arch::OperandWrapper(TRITON_X86_REG_EAX);
        auto src1       = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue+(stack.getSize() * 0), stack.getSize()));
        auto src2       = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue+(stack.getSize() * 1), stack.getSize()));
        auto src3       = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue+(stack.getSize() * 2), stack.getSize()));
        auto src4       = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue+(stack.getSize() * 3), stack.getSize()));
        auto src5       = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue+(stack.getSize() * 4), stack.getSize()));
        auto src6       = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue+(stack.getSize() * 5), stack.getSize()));
        auto src7       = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue+(stack.getSize() * 6), stack.getSize()));
        auto src8       = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue+(stack.getSize() * 7), stack.getSize()));

        /* Create symbolic operands and semantics */
        auto node1 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto node2 = this->symbolicEngine->buildSymbolicOperand(inst, src2);
        auto node3 = this->symbolicEngine->buildSymbolicOperand(inst, src3);
        auto node4 = this->symbolicEngine->buildSymbolicOperand(inst, src4);
        auto node5 = this->symbolicEngine->buildSymbolicOperand(inst, src5);
        auto node6 = this->symbolicEngine->buildSymbolicOperand(inst, src6);
        auto node7 = this->symbolicEngine->buildSymbolicOperand(inst, src7);
        auto node8 = this->symbolicEngine->buildSymbolicOperand(inst, src8);

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst1, "POPAL EDI operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, dst2, "POPAL ESI operation");
        auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, dst3, "POPAL EBP operation");
        auto expr4 = this->symbolicEngine->createSymbolicExpression(inst, node4, dst4, "POPAL ESP operation");
        auto expr5 = this->symbolicEngine->createSymbolicExpression(inst, node5, dst5, "POPAL EBX operation");
        auto expr6 = this->symbolicEngine->createSymbolicExpression(inst, node6, dst6, "POPAL EDX operation");
        auto expr7 = this->symbolicEngine->createSymbolicExpression(inst, node7, dst7, "POPAL ECX operation");
        auto expr8 = this->symbolicEngine->createSymbolicExpression(inst, node8, dst8, "POPAL EAX operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst1, src1);
        expr2->isTainted = this->taintEngine->taintAssignment(dst2, src2);
        expr3->isTainted = this->taintEngine->taintAssignment(dst3, src3);
        expr4->isTainted = this->taintEngine->taintAssignment(dst4, src4);
        expr5->isTainted = this->taintEngine->taintAssignment(dst5, src5);
        expr6->isTainted = this->taintEngine->taintAssignment(dst6, src6);
        expr7->isTainted = this->taintEngine->taintAssignment(dst7, src7);
        expr8->isTainted = this->taintEngine->taintAssignment(dst8, src8);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::popfd_s(triton::arch::Instruction& inst) {
        auto  stack      = TRITON_X86_REG_SP.getParent();
        auto  stackValue = this->architecture->getConcreteRegisterValue(stack).convert_to<triton::uint64>();
        auto  dst1       = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
        auto  dst2       = triton::arch::OperandWrapper(TRITON_X86_REG_PF);
        auto  dst3       = triton::arch::OperandWrapper(TRITON_X86_REG_AF);
        auto  dst4       = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
        auto  dst5       = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
        auto  dst6       = triton::arch::OperandWrapper(TRITON_X86_REG_TF);
        auto  dst7       = triton::arch::OperandWrapper(TRITON_X86_REG_IF);
        auto  dst8       = triton::arch::OperandWrapper(TRITON_X86_REG_DF);
        auto  dst9       = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
        auto  src        = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue, stack.getSize()));

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
        auto expr1 = this->symbolicEngine->createSymbolicFlagExpression(inst, node1, dst1.getRegister(), "POPFD CF operation");
        auto expr2 = this->symbolicEngine->createSymbolicFlagExpression(inst, node2, dst2.getRegister(), "POPFD PF operation");
        auto expr3 = this->symbolicEngine->createSymbolicFlagExpression(inst, node3, dst3.getRegister(), "POPFD AF operation");
        auto expr4 = this->symbolicEngine->createSymbolicFlagExpression(inst, node4, dst4.getRegister(), "POPFD ZF operation");
        auto expr5 = this->symbolicEngine->createSymbolicFlagExpression(inst, node5, dst5.getRegister(), "POPFD SF operation");
        auto expr6 = this->symbolicEngine->createSymbolicFlagExpression(inst, node6, dst6.getRegister(), "POPFD TF operation");
        auto expr7 = this->symbolicEngine->createSymbolicFlagExpression(inst, node7, dst7.getRegister(), "POPFD IF operation");
        auto expr8 = this->symbolicEngine->createSymbolicFlagExpression(inst, node8, dst8.getRegister(), "POPFD DF operation");
        auto expr9 = this->symbolicEngine->createSymbolicFlagExpression(inst, node9, dst9.getRegister(), "POPFD OF operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst1, src);
        expr2->isTainted = this->taintEngine->taintAssignment(dst2, src);
        expr3->isTainted = this->taintEngine->taintAssignment(dst3, src);
        expr4->isTainted = this->taintEngine->taintAssignment(dst4, src);
        expr5->isTainted = this->taintEngine->taintAssignment(dst5, src);
        expr6->isTainted = this->taintEngine->taintAssignment(dst6, src);
        expr7->isTainted = this->taintEngine->taintAssignment(dst7, src);
        expr8->isTainted = this->taintEngine->taintAssignment(dst8, src);
        expr9->isTainted = this->taintEngine->taintAssignment(dst9, src);

        /* Create the semantics - side effect */
        alignAddStack_s(inst, src.getSize());

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::popfq_s(triton::arch::Instruction& inst) {
        auto  stack      = TRITON_X86_REG_SP.getParent();
        auto  stackValue = this->architecture->getConcreteRegisterValue(stack).convert_to<triton::uint64>();
        auto  dst1       = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
        auto  dst2       = triton::arch::OperandWrapper(TRITON_X86_REG_PF);
        auto  dst3       = triton::arch::OperandWrapper(TRITON_X86_REG_AF);
        auto  dst4       = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
        auto  dst5       = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
        auto  dst6       = triton::arch::OperandWrapper(TRITON_X86_REG_TF);
        auto  dst7       = triton::arch::OperandWrapper(TRITON_X86_REG_IF);
        auto  dst8       = triton::arch::OperandWrapper(TRITON_X86_REG_DF);
        auto  dst9       = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
        auto  src        = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue, stack.getSize()));

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
        auto expr1 = this->symbolicEngine->createSymbolicFlagExpression(inst, node1, dst1.getRegister(), "POPFQ CF operation");
        auto expr2 = this->symbolicEngine->createSymbolicFlagExpression(inst, node2, dst2.getRegister(), "POPFQ PF operation");
        auto expr3 = this->symbolicEngine->createSymbolicFlagExpression(inst, node3, dst3.getRegister(), "POPFQ AF operation");
        auto expr4 = this->symbolicEngine->createSymbolicFlagExpression(inst, node4, dst4.getRegister(), "POPFQ ZF operation");
        auto expr5 = this->symbolicEngine->createSymbolicFlagExpression(inst, node5, dst5.getRegister(), "POPFQ SF operation");
        auto expr6 = this->symbolicEngine->createSymbolicFlagExpression(inst, node6, dst6.getRegister(), "POPFQ TF operation");
        auto expr7 = this->symbolicEngine->createSymbolicFlagExpression(inst, node7, dst7.getRegister(), "POPFQ IF operation");
        auto expr8 = this->symbolicEngine->createSymbolicFlagExpression(inst, node8, dst8.getRegister(), "POPFQ DF operation");
        auto expr9 = this->symbolicEngine->createSymbolicFlagExpression(inst, node9, dst9.getRegister(), "POPFQ OF operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst1, src);
        expr2->isTainted = this->taintEngine->taintAssignment(dst2, src);
        expr3->isTainted = this->taintEngine->taintAssignment(dst3, src);
        expr4->isTainted = this->taintEngine->taintAssignment(dst4, src);
        expr5->isTainted = this->taintEngine->taintAssignment(dst5, src);
        expr6->isTainted = this->taintEngine->taintAssignment(dst6, src);
        expr7->isTainted = this->taintEngine->taintAssignment(dst7, src);
        expr8->isTainted = this->taintEngine->taintAssignment(dst8, src);
        expr9->isTainted = this->taintEngine->taintAssignment(dst9, src);

        /* Create the semantics - side effect */
        alignAddStack_s(inst, src.getSize());

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::por_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::bvor(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "POR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::prefetchx_s(triton::arch::Instruction& inst) {
        auto& src = inst.operands[0];

        /* Only specify that the instruction performs an implicit memory read */
        this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pshufd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto& ord = inst.operands[2];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, ord);

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PSHUFD operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pshufhw_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto& ord = inst.operands[2];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, ord);

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PSHUFHW operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pshuflw_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto& ord = inst.operands[2];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, ord);

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PSHUFLW operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pshufw_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];
        auto& ord = inst.operands[2];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, ord);

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PSHUFW operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pslldq_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = triton::ast::zx(dst.getBitSize() - src.getBitSize(), this->symbolicEngine->buildSymbolicOperand(inst, src));

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PSLLDQ operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::psrldq_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = triton::ast::zx(dst.getBitSize() - src.getBitSize(), this->symbolicEngine->buildSymbolicOperand(inst, src));

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PSRLDQ operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::psubb_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
            throw triton::exceptions::Semantics("x86Semantics::psubb_s(): Invalid operand size.");

        }

        auto node = triton::ast::concat(packed);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PSUBB operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::psubd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
            throw triton::exceptions::Semantics("x86Semantics::psubd_s(): Invalid operand size.");

        }

        auto node = triton::ast::concat(packed);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PSUBD operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::psubq_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
            throw triton::exceptions::Semantics("x86Semantics::psubq_s(): Invalid operand size.");

        }

        auto node = triton::ast::concat(packed);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PSUBQ operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::psubw_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
            throw triton::exceptions::Semantics("x86Semantics::psubw_s(): Invalid operand size.");

        }

        auto node = triton::ast::concat(packed);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PSUBW operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::ptest_s(triton::arch::Instruction& inst) {
        auto& src1 = inst.operands[0];
        auto& src2 = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src2);

        /* Create the semantics */
        auto node1 = triton::ast::bvand(op1, op2);
        auto node2 = triton::ast::bvand(op1, triton::ast::bvnot(op2));

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node1, "PTEST operation");
        auto expr2 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node2, "PTEST operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2);
        expr2->isTainted = this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2);

        /* Upate symbolic flags */
        this->clearFlag_s(inst, TRITON_X86_REG_AF, "Clears adjust flag");
        this->cfPtest_s(inst, expr2, src1, true);
        this->clearFlag_s(inst, TRITON_X86_REG_OF, "Clears overflow flag");
        this->clearFlag_s(inst, TRITON_X86_REG_PF, "Clears parity flag");
        this->clearFlag_s(inst, TRITON_X86_REG_SF, "Clears sign flag");
        this->zf_s(inst, expr1, src1, true);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::punpckhbw_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
            throw triton::exceptions::Semantics("x86Semantics::punpckhbw_s(): Invalid operand size.");
        }

        auto node = triton::ast::concat(unpack);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PUNPCKHBW operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::punpckhdq_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
            throw triton::exceptions::Semantics("x86Semantics::punpckhdq_s(): Invalid operand size.");
        }

        auto node = triton::ast::concat(unpack);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PUNPCKHDQ operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::punpckhqdq_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        std::list<triton::ast::AbstractNode*> unpack;

        switch (dst.getBitSize()) {

          /* XMM */
          case DQWORD_SIZE_BIT:
            unpack.push_back(triton::ast::extract(127, 64, op2));
            unpack.push_back(triton::ast::extract(127, 64, op1));
            break;

          default:
            throw triton::exceptions::Semantics("x86Semantics::punpckhqdq_s(): Invalid operand size.");
        }

        auto node = triton::ast::concat(unpack);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PUNPCKHQDQ operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::punpckhwd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
            throw triton::exceptions::Semantics("x86Semantics::punpckhwd_s(): Invalid operand size.");
        }

        auto node = triton::ast::concat(unpack);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PUNPCKHWD operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::punpcklbw_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
            throw triton::exceptions::Semantics("x86Semantics::punpcklbw_s(): Invalid operand size.");
        }

        auto node = triton::ast::concat(unpack);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PUNPCKLBW operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::punpckldq_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
            throw triton::exceptions::Semantics("x86Semantics::punpckldq_s(): Invalid operand size.");
        }

        auto node = triton::ast::concat(unpack);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PUNPCKLDQ operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::punpcklqdq_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        std::list<triton::ast::AbstractNode*> unpack;

        switch (dst.getBitSize()) {

          /* XMM */
          case DQWORD_SIZE_BIT:
            unpack.push_back(triton::ast::extract(63, 0, op2));
            unpack.push_back(triton::ast::extract(63, 0, op1));
            break;

          default:
            throw triton::exceptions::Semantics("x86Semantics::punpcklqdq_s(): Invalid operand size.");
        }

        auto node = triton::ast::concat(unpack);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PUNPCKLQDQ operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::punpcklwd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

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
            throw triton::exceptions::Semantics("x86Semantics::punpcklwd_s(): Invalid operand size.");
        }

        auto node = triton::ast::concat(unpack);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PUNPCKLWD operation");

        /* Apply the taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::push_s(triton::arch::Instruction& inst) {
        auto& src           = inst.operands[0];
        auto stack          = TRITON_X86_REG_SP.getParent();
        triton::uint32 size = stack.getSize();

        /* If it's an immediate source, the memory access is always based on the arch size */
        if (src.getType() != triton::arch::OP_IMM)
          size = src.getSize();

        /* Create the semantics - side effect */
        auto  stackValue = alignSubStack_s(inst, size);
        auto  dst        = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue, size));

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::zx(dst.getBitSize() - src.getBitSize(), op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PUSH operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pushal_s(triton::arch::Instruction& inst) {
        auto stack      = TRITON_X86_REG_SP.getParent();
        auto stackValue = this->architecture->getConcreteRegisterValue(stack).convert_to<triton::uint64>();
        auto dst1       = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue-(stack.getSize() * 1), stack.getSize()));
        auto dst2       = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue-(stack.getSize() * 2), stack.getSize()));
        auto dst3       = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue-(stack.getSize() * 3), stack.getSize()));
        auto dst4       = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue-(stack.getSize() * 4), stack.getSize()));
        auto dst5       = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue-(stack.getSize() * 5), stack.getSize()));
        auto dst6       = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue-(stack.getSize() * 6), stack.getSize()));
        auto dst7       = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue-(stack.getSize() * 7), stack.getSize()));
        auto dst8       = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue-(stack.getSize() * 8), stack.getSize()));
        auto src1       = triton::arch::OperandWrapper(TRITON_X86_REG_EAX);
        auto src2       = triton::arch::OperandWrapper(TRITON_X86_REG_ECX);
        auto src3       = triton::arch::OperandWrapper(TRITON_X86_REG_EDX);
        auto src4       = triton::arch::OperandWrapper(TRITON_X86_REG_EBX);
        auto src5       = triton::arch::OperandWrapper(TRITON_X86_REG_ESP);
        auto src6       = triton::arch::OperandWrapper(TRITON_X86_REG_EBP);
        auto src7       = triton::arch::OperandWrapper(TRITON_X86_REG_ESI);
        auto src8       = triton::arch::OperandWrapper(TRITON_X86_REG_EDI);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src2);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, src3);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, src4);
        auto op5 = this->symbolicEngine->buildSymbolicOperand(inst, src5);
        auto op6 = this->symbolicEngine->buildSymbolicOperand(inst, src6);
        auto op7 = this->symbolicEngine->buildSymbolicOperand(inst, src7);
        auto op8 = this->symbolicEngine->buildSymbolicOperand(inst, src8);

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
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst1, "PUSHAL EAX operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, dst2, "PUSHAL ECX operation");
        auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, dst3, "PUSHAL EDX operation");
        auto expr4 = this->symbolicEngine->createSymbolicExpression(inst, node4, dst4, "PUSHAL EBX operation");
        auto expr5 = this->symbolicEngine->createSymbolicExpression(inst, node5, dst5, "PUSHAL ESP operation");
        auto expr6 = this->symbolicEngine->createSymbolicExpression(inst, node6, dst6, "PUSHAL EBP operation");
        auto expr7 = this->symbolicEngine->createSymbolicExpression(inst, node7, dst7, "PUSHAL ESI operation");
        auto expr8 = this->symbolicEngine->createSymbolicExpression(inst, node8, dst8, "PUSHAL EDI operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst1, src1);
        expr2->isTainted = this->taintEngine->taintAssignment(dst2, src2);
        expr3->isTainted = this->taintEngine->taintAssignment(dst3, src3);
        expr4->isTainted = this->taintEngine->taintAssignment(dst4, src4);
        expr5->isTainted = this->taintEngine->taintAssignment(dst5, src5);
        expr6->isTainted = this->taintEngine->taintAssignment(dst6, src6);
        expr7->isTainted = this->taintEngine->taintAssignment(dst7, src7);
        expr8->isTainted = this->taintEngine->taintAssignment(dst8, src8);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pushfd_s(triton::arch::Instruction& inst) {
        auto stack = TRITON_X86_REG_SP.getParent();

        /* Create the semantics - side effect */
        auto stackValue = alignSubStack_s(inst, stack.getSize());
        auto dst        = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue, stack.getSize()));
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
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src2);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, src3);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, src4);
        auto op5 = this->symbolicEngine->buildSymbolicOperand(inst, src5);
        auto op6 = this->symbolicEngine->buildSymbolicOperand(inst, src6);
        auto op7 = this->symbolicEngine->buildSymbolicOperand(inst, src7);
        auto op8 = this->symbolicEngine->buildSymbolicOperand(inst, src8);
        auto op9 = this->symbolicEngine->buildSymbolicOperand(inst, src9);

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

        auto node = triton::ast::zx(
                      dst.getBitSize() - static_cast<triton::uint32>(eflags.size()),
                      triton::ast::concat(eflags)
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PUSHFD operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src1);
        expr->isTainted = this->taintEngine->taintUnion(dst, src2);
        expr->isTainted = this->taintEngine->taintUnion(dst, src3);
        expr->isTainted = this->taintEngine->taintUnion(dst, src4);
        expr->isTainted = this->taintEngine->taintUnion(dst, src5);
        expr->isTainted = this->taintEngine->taintUnion(dst, src6);
        expr->isTainted = this->taintEngine->taintUnion(dst, src7);
        expr->isTainted = this->taintEngine->taintUnion(dst, src8);
        expr->isTainted = this->taintEngine->taintUnion(dst, src9);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pushfq_s(triton::arch::Instruction& inst) {
        auto stack = TRITON_X86_REG_SP.getParent();

        /* Create the semantics - side effect */
        auto stackValue = alignSubStack_s(inst, stack.getSize());
        auto dst        = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue, stack.getSize()));
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
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src2);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, src3);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, src4);
        auto op5 = this->symbolicEngine->buildSymbolicOperand(inst, src5);
        auto op6 = this->symbolicEngine->buildSymbolicOperand(inst, src6);
        auto op7 = this->symbolicEngine->buildSymbolicOperand(inst, src7);
        auto op8 = this->symbolicEngine->buildSymbolicOperand(inst, src8);
        auto op9 = this->symbolicEngine->buildSymbolicOperand(inst, src9);

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

        auto node = triton::ast::zx(
                      dst.getBitSize() - static_cast<triton::uint32>(eflags.size()),
                      triton::ast::concat(eflags)
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PUSHFQ operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src1);
        expr->isTainted = this->taintEngine->taintUnion(dst, src2);
        expr->isTainted = this->taintEngine->taintUnion(dst, src3);
        expr->isTainted = this->taintEngine->taintUnion(dst, src4);
        expr->isTainted = this->taintEngine->taintUnion(dst, src5);
        expr->isTainted = this->taintEngine->taintUnion(dst, src6);
        expr->isTainted = this->taintEngine->taintUnion(dst, src7);
        expr->isTainted = this->taintEngine->taintUnion(dst, src8);
        expr->isTainted = this->taintEngine->taintUnion(dst, src9);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::pxor_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::bvxor(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "PXOR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::rcl_s(triton::arch::Instruction& inst) {
        auto& dst   = inst.operands[0];
        auto& src   = inst.operands[1];
        auto  srcCf = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

        /* Create symbolic operands */
        auto op1    = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2    = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op2bis = this->symbolicEngine->buildSymbolicOperand(src);
        auto op3    = this->symbolicEngine->buildSymbolicOperand(inst, srcCf);

        switch (dst.getBitSize()) {
          /* Mask: 0x1f without MOD */
          case QWORD_SIZE_BIT:
            op2 = triton::ast::bvand(
                    op2,
                    triton::ast::bv(QWORD_SIZE_BIT-1, src.getBitSize())
                  );
            break;

          /* Mask: 0x1f without MOD */
          case DWORD_SIZE_BIT:
            op2 = triton::ast::bvand(
                    op2,
                    triton::ast::bv(DWORD_SIZE_BIT-1, src.getBitSize())
                  );
            break;

          /* Mask: 0x1f MOD size + 1 */
          case WORD_SIZE_BIT:
          case BYTE_SIZE_BIT:
            op2 = triton::ast::bvsmod(
                    triton::ast::bvand(
                      op2,
                      triton::ast::bv(DWORD_SIZE_BIT-1, src.getBitSize())),
                    triton::ast::bv(dst.getBitSize()+1, src.getBitSize())
                  );
            break;

          default:
            throw triton::exceptions::Semantics("x86Semantics::rcl_s(): Invalid destination size");
        }

        /* Create the semantics */
        auto node1 = triton::ast::bvrol(triton::ast::decimal(op2->evaluate()), triton::ast::concat(op3, op1));

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node1, "RCL tempory operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->isTainted(dst) | this->taintEngine->isTainted(src);

        /* Create the semantics */
        auto node2 = triton::ast::extract(dst.getBitSize()-1, 0, node1);

        /* Create symbolic expression */
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "RCL operation");

        /* Spread taint */
        expr2->isTainted = this->taintEngine->taintUnion(dst, src);
        expr2->isTainted = this->taintEngine->taintUnion(dst, srcCf);

        /* Upate symbolic flags */
        this->cfRcl_s(inst, expr2, node1, op2bis);
        this->ofRol_s(inst, expr2, dst, op2bis); /* Same as ROL */

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::rcr_s(triton::arch::Instruction& inst) {
        auto& dst   = inst.operands[0];
        auto& src   = inst.operands[1];
        auto  srcCf = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

        /* Create symbolic operands */
        auto op1    = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2    = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3    = this->symbolicEngine->buildSymbolicOperand(inst, srcCf);

        switch (dst.getBitSize()) {
          /* Mask: 0x3f without MOD */
          case QWORD_SIZE_BIT:
            op2 = triton::ast::bvand(
                    op2,
                    triton::ast::bv(QWORD_SIZE_BIT-1, src.getBitSize())
                  );
            break;

          /* Mask: 0x1f without MOD */
          case DWORD_SIZE_BIT:
            op2 = triton::ast::bvand(
                    op2,
                    triton::ast::bv(DWORD_SIZE_BIT-1, src.getBitSize())
                  );
            break;

          /* Mask: 0x1f MOD size + 1 */
          case WORD_SIZE_BIT:
          case BYTE_SIZE_BIT:
            op2 = triton::ast::bvsmod(
                    triton::ast::bvand(
                      op2,
                      triton::ast::bv(DWORD_SIZE_BIT-1, src.getBitSize())),
                    triton::ast::bv(dst.getBitSize()+1, src.getBitSize())
                  );
            break;

          default:
            throw triton::exceptions::Semantics("x86Semantics::rcr_s(): Invalid destination size");
        }

        /* Create the semantics */
        auto node1 = triton::ast::bvror(triton::ast::decimal(op2->evaluate()), triton::ast::concat(op3, op1));

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node1, "RCR tempory operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->isTainted(dst) | this->taintEngine->isTainted(src);

        /* Create the semantics */
        auto node2 = triton::ast::extract(dst.getBitSize()-1, 0, node1);

        /* Create symbolic expression */
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, dst, "RCR operation");

        /* Spread taint */
        expr2->isTainted = this->taintEngine->taintUnion(dst, src);
        expr2->isTainted = this->taintEngine->taintUnion(dst, srcCf);

        /* Upate symbolic flags */
        this->ofRcr_s(inst, expr2, dst, op1, op2); /* OF must be set before CF */
        this->cfRcr_s(inst, expr2, dst, node1, op2);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::rdtsc_s(triton::arch::Instruction& inst) {
        auto dst1 = triton::arch::OperandWrapper(TRITON_X86_REG_EDX);
        auto dst2 = triton::arch::OperandWrapper(TRITON_X86_REG_EAX);

        /* Create symbolic operands */
        auto op1 = triton::ast::bv(0, dst1.getBitSize());
        auto op2 = triton::ast::bv(this->symbolicEngine->getSymbolicExpressions().size(), dst2.getBitSize());

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, op1, dst1, "RDTSC EDX operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, op2, dst2, "RDTSC EAX operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->setTaint(dst1, triton::engines::taint::UNTAINTED);
        expr2->isTainted = this->taintEngine->setTaint(dst2, triton::engines::taint::UNTAINTED);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::ret_s(triton::arch::Instruction& inst) {
        auto stack      = TRITON_X86_REG_SP.getParent();
        auto stackValue = this->architecture->getConcreteRegisterValue(stack).convert_to<triton::uint64>();
        auto pc         = triton::arch::OperandWrapper(TRITON_X86_REG_PC);
        auto sp         = triton::arch::OperandWrapper(triton::arch::MemoryAccess(stackValue, stack.getSize()));

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, sp);

        /* Create the semantics */
        auto node = op1;

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, pc, "Program Counter");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(pc, sp);

        /* Create the semantics - side effect */
        alignAddStack_s(inst, sp.getSize());

        /* Create the semantics - side effect */
        if (inst.operands.size() > 0) {
          auto offset = inst.operands[0].getImmediate();
          this->symbolicEngine->buildSymbolicImmediate(inst, offset);
          alignAddStack_s(inst, static_cast<triton::uint32>(offset.getValue()));
        }

        /* Create the path constraint */
        this->symbolicEngine->addPathConstraint(inst, expr);
      }


      void x86Semantics::rol_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1    = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2    = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op2bis = this->symbolicEngine->buildSymbolicOperand(src);

        switch (dst.getBitSize()) {
          /* Mask 0x3f MOD size */
          case QWORD_SIZE_BIT:
            op2 = triton::ast::bvsmod(
                    triton::ast::bvand(
                      op2,
                      triton::ast::bv(QWORD_SIZE_BIT-1, src.getBitSize())),
                    triton::ast::bv(dst.getBitSize(), src.getBitSize())
                  );

            op2bis = triton::ast::bvand(
                       op2bis,
                       triton::ast::bv(QWORD_SIZE_BIT-1, src.getBitSize())
                     );
            break;

          /* Mask 0x1f MOD size */
          case DWORD_SIZE_BIT:
          case WORD_SIZE_BIT:
          case BYTE_SIZE_BIT:
            op2 = triton::ast::bvsmod(
                    triton::ast::bvand(
                      op2,
                      triton::ast::bv(DWORD_SIZE_BIT-1, src.getBitSize())),
                    triton::ast::bv(dst.getBitSize(), src.getBitSize())
                  );

            op2bis = triton::ast::bvand(
                       op2bis,
                       triton::ast::bv(DWORD_SIZE_BIT-1, src.getBitSize())
                     );
            break;

          default:
            throw triton::exceptions::Semantics("x86Semantics::rol_s(): Invalid destination size");
        }

        /* Create the semantics */
        auto node = triton::ast::bvrol(triton::ast::decimal(op2->evaluate()), op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ROL operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate symbolic flags */
        this->cfRol_s(inst, expr, dst, op2bis);
        this->ofRol_s(inst, expr, dst, op2bis);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::ror_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1    = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2    = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op2bis = this->symbolicEngine->buildSymbolicOperand(src);

        switch (dst.getBitSize()) {
          /* Mask 0x3f MOD size */
          case QWORD_SIZE_BIT:
            op2 = triton::ast::bvsmod(
                    triton::ast::bvand(
                      op2,
                      triton::ast::bv(QWORD_SIZE_BIT-1, src.getBitSize())),
                    triton::ast::bv(dst.getBitSize(), src.getBitSize())
                  );

            op2bis = triton::ast::bvand(
                       op2bis,
                       triton::ast::bv(QWORD_SIZE_BIT-1, src.getBitSize())
                     );
            break;

          /* Mask 0x1f MOD size */
          case DWORD_SIZE_BIT:
          case WORD_SIZE_BIT:
          case BYTE_SIZE_BIT:
            op2 = triton::ast::bvsmod(
                    triton::ast::bvand(
                      op2,
                      triton::ast::bv(DWORD_SIZE_BIT-1, src.getBitSize())),
                    triton::ast::bv(dst.getBitSize(), src.getBitSize())
                  );

            op2bis = triton::ast::bvand(
                       op2bis,
                       triton::ast::bv(DWORD_SIZE_BIT-1, src.getBitSize())
                     );
            break;

          default:
            throw triton::exceptions::Semantics("x86Semantics::ror_s(): Invalid destination size");
        }

        /* Create the semantics */
        auto node = triton::ast::bvror(triton::ast::decimal(op2->evaluate()), op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "ROR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate symbolic flags */
        this->cfRor_s(inst, expr, dst, op2);
        this->ofRor_s(inst, expr, dst, op2bis);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::rorx_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src2);

        switch (dst.getBitSize()) {
          /* Mask 0x3f MOD size */
          case QWORD_SIZE_BIT:
            op2 = triton::ast::bvand(op2, triton::ast::bv(QWORD_SIZE_BIT-1, src2.getBitSize()));
            break;

          /* Mask 0x1f MOD size */
          case DWORD_SIZE_BIT:
            op2 = triton::ast::bvand(op2, triton::ast::bv(DWORD_SIZE_BIT-1, src2.getBitSize()));
            break;

          default:
            throw triton::exceptions::Semantics("x86Semantics::rorx_s(): Invalid destination size");
        }

        /* Create the semantics */
        auto node = triton::ast::bvror(triton::ast::decimal(op2->evaluate()), op1);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "RORX operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src1);
        expr->isTainted |= this->taintEngine->taintUnion(dst, src2);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::sahf_s(triton::arch::Instruction& inst) {
        auto dst1 = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
        auto dst2 = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);
        auto dst3 = triton::arch::OperandWrapper(TRITON_X86_REG_AF);
        auto dst4 = triton::arch::OperandWrapper(TRITON_X86_REG_PF);
        auto dst5 = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
        auto src  = triton::arch::OperandWrapper(TRITON_X86_REG_AH);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node1 = triton::ast::extract(7, 7, op1);
        auto node2 = triton::ast::extract(6, 6, op1);
        auto node3 = triton::ast::extract(4, 4, op1);
        auto node4 = triton::ast::extract(2, 2, op1);
        auto node5 = triton::ast::extract(0, 0, op1);

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicFlagExpression(inst, node1, dst1.getRegister(), "SAHF SF operation");
        auto expr2 = this->symbolicEngine->createSymbolicFlagExpression(inst, node2, dst2.getRegister(), "SAHF ZF operation");
        auto expr3 = this->symbolicEngine->createSymbolicFlagExpression(inst, node3, dst3.getRegister(), "SAHF AF operation");
        auto expr4 = this->symbolicEngine->createSymbolicFlagExpression(inst, node4, dst4.getRegister(), "SAHF PF operation");
        auto expr5 = this->symbolicEngine->createSymbolicFlagExpression(inst, node5, dst5.getRegister(), "SAHF CF operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst1, src);
        expr2->isTainted = this->taintEngine->taintAssignment(dst2, src);
        expr3->isTainted = this->taintEngine->taintAssignment(dst3, src);
        expr4->isTainted = this->taintEngine->taintAssignment(dst4, src);
        expr5->isTainted = this->taintEngine->taintAssignment(dst5, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::sar_s(triton::arch::Instruction& inst) {
        auto& dst   = inst.operands[0];
        auto& src   = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = triton::ast::zx(dst.getBitSize() - src.getBitSize(), this->symbolicEngine->buildSymbolicOperand(inst, src));

        if (dst.getBitSize() == QWORD_SIZE_BIT)
          op2 = triton::ast::bvand(op2, triton::ast::bv(QWORD_SIZE_BIT-1, dst.getBitSize()));
        else
          op2 = triton::ast::bvand(op2, triton::ast::bv(DWORD_SIZE_BIT-1, dst.getBitSize()));

        /* Create the semantics */
        auto node = triton::ast::bvashr(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SAR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate symbolic flags */
        this->cfSar_s(inst, expr, dst, op1, op2);
        this->ofSar_s(inst, expr, dst, op2);
        this->pfShl_s(inst, expr, dst, op2); /* Same that shl */
        this->sfShl_s(inst, expr, dst, op2); /* Same that shl */
        this->zfShl_s(inst, expr, dst, op2); /* Same that shl */

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::sarx_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src2);

        switch (dst.getBitSize()) {
          /* Mask 0x3f MOD size */
          case QWORD_SIZE_BIT:
            op2 = triton::ast::bvand(op2, triton::ast::bv(QWORD_SIZE_BIT-1, src2.getBitSize()));
            break;

          /* Mask 0x1f MOD size */
          case DWORD_SIZE_BIT:
            op2 = triton::ast::bvand(op2, triton::ast::bv(DWORD_SIZE_BIT-1, src2.getBitSize()));
            break;

          default:
            throw triton::exceptions::Semantics("x86Semantics::sarx_s(): Invalid destination size");
        }

        /* Create the semantics */
        auto node = triton::ast::bvashr(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SARX operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src1);
        expr->isTainted |= this->taintEngine->taintUnion(dst, src2);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::sbb_s(triton::arch::Instruction& inst) {
        auto& dst   = inst.operands[0];
        auto& src   = inst.operands[1];
        auto  srcCf = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = triton::ast::zx(src.getBitSize()-1, this->symbolicEngine->buildSymbolicOperand(inst, srcCf));

        /* Create the semantics */
        auto node = triton::ast::bvsub(op1, triton::ast::bvadd(op2, op3));

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SBB operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);
        expr->isTainted = this->taintEngine->taintUnion(dst, srcCf);

        /* Upate symbolic flags */
        this->af_s(inst, expr, dst, op1, op2);
        this->cfSub_s(inst, expr, dst, op1, op2);
        this->ofSub_s(inst, expr, dst, op1, op2);
        this->pf_s(inst, expr, dst);
        this->sf_s(inst, expr, dst);
        this->zf_s(inst, expr, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::scasb_s(triton::arch::Instruction& inst) {
        auto& dst    = inst.operands[0];
        auto& src    = inst.operands[1];
        auto  index  = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
        auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

        /* If the REP prefix is defined, convert REP into REPE */
        if (inst.getPrefix() == triton::arch::x86::ID_PREFIX_REP)
          inst.setPrefix(triton::arch::x86::ID_PREFIX_REPE);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, index);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, df);

        /* Create the semantics */
        auto node1 = triton::ast::bvsub(op1, op2);
        auto node2 = triton::ast::ite(
                       triton::ast::equal(op4, triton::ast::bvfalse()),
                       triton::ast::bvadd(op3, triton::ast::bv(BYTE_SIZE, index.getBitSize())),
                       triton::ast::bvsub(op3, triton::ast::bv(BYTE_SIZE, index.getBitSize()))
                     );

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node1, "SCASB operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, index, "Index operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->isTainted(dst) | this->taintEngine->isTainted(src);
        expr2->isTainted = this->taintEngine->taintUnion(index, index);

        /* Upate symbolic flags */
        this->af_s(inst, expr1, dst, op1, op2, true);
        this->cfSub_s(inst, expr1, dst, op1, op2, true);
        this->ofSub_s(inst, expr1, dst, op1, op2, true);
        this->pf_s(inst, expr1, dst, true);
        this->sf_s(inst, expr1, dst, true);
        this->zf_s(inst, expr1, dst, true);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::scasd_s(triton::arch::Instruction& inst) {
        auto& dst    = inst.operands[0];
        auto& src    = inst.operands[1];
        auto  index  = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
        auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

        /* If the REP prefix is defined, convert REP into REPE */
        if (inst.getPrefix() == triton::arch::x86::ID_PREFIX_REP)
          inst.setPrefix(triton::arch::x86::ID_PREFIX_REPE);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, index);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, df);

        /* Create the semantics */
        auto node1 = triton::ast::bvsub(op1, op2);
        auto node2 = triton::ast::ite(
                       triton::ast::equal(op4, triton::ast::bvfalse()),
                       triton::ast::bvadd(op3, triton::ast::bv(DWORD_SIZE, index.getBitSize())),
                       triton::ast::bvsub(op3, triton::ast::bv(DWORD_SIZE, index.getBitSize()))
                     );

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node1, "SCASD operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, index, "Index operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->isTainted(dst) | this->taintEngine->isTainted(src);
        expr2->isTainted = this->taintEngine->taintUnion(index, index);

        /* Upate symbolic flags */
        this->af_s(inst, expr1, dst, op1, op2, true);
        this->cfSub_s(inst, expr1, dst, op1, op2, true);
        this->ofSub_s(inst, expr1, dst, op1, op2, true);
        this->pf_s(inst, expr1, dst, true);
        this->sf_s(inst, expr1, dst, true);
        this->zf_s(inst, expr1, dst, true);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::scasq_s(triton::arch::Instruction& inst) {
        auto& dst    = inst.operands[0];
        auto& src    = inst.operands[1];
        auto  index  = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
        auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

        /* If the REP prefix is defined, convert REP into REPE */
        if (inst.getPrefix() == triton::arch::x86::ID_PREFIX_REP)
          inst.setPrefix(triton::arch::x86::ID_PREFIX_REPE);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, index);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, df);

        /* Create the semantics */
        auto node1 = triton::ast::bvsub(op1, op2);
        auto node2 = triton::ast::ite(
                       triton::ast::equal(op4, triton::ast::bvfalse()),
                       triton::ast::bvadd(op3, triton::ast::bv(QWORD_SIZE, index.getBitSize())),
                       triton::ast::bvsub(op3, triton::ast::bv(QWORD_SIZE, index.getBitSize()))
                     );

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node1, "SCASQ operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, index, "Index operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->isTainted(dst) | this->taintEngine->isTainted(src);
        expr2->isTainted = this->taintEngine->taintUnion(index, index);

        /* Upate symbolic flags */
        this->af_s(inst, expr1, dst, op1, op2, true);
        this->cfSub_s(inst, expr1, dst, op1, op2, true);
        this->ofSub_s(inst, expr1, dst, op1, op2, true);
        this->pf_s(inst, expr1, dst, true);
        this->sf_s(inst, expr1, dst, true);
        this->zf_s(inst, expr1, dst, true);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::scasw_s(triton::arch::Instruction& inst) {
        auto& dst    = inst.operands[0];
        auto& src    = inst.operands[1];
        auto  index  = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
        auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

        /* If the REP prefix is defined, convert REP into REPE */
        if (inst.getPrefix() == triton::arch::x86::ID_PREFIX_REP)
          inst.setPrefix(triton::arch::x86::ID_PREFIX_REPE);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, index);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, df);

        /* Create the semantics */
        auto node1 = triton::ast::bvsub(op1, op2);
        auto node2 = triton::ast::ite(
                       triton::ast::equal(op4, triton::ast::bvfalse()),
                       triton::ast::bvadd(op3, triton::ast::bv(WORD_SIZE, index.getBitSize())),
                       triton::ast::bvsub(op3, triton::ast::bv(WORD_SIZE, index.getBitSize()))
                     );

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node1, "SCASW operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, index, "Index operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->isTainted(dst) | this->taintEngine->isTainted(src);
        expr2->isTainted = this->taintEngine->taintUnion(index, index);

        /* Upate symbolic flags */
        this->af_s(inst, expr1, dst, op1, op2, true);
        this->cfSub_s(inst, expr1, dst, op1, op2, true);
        this->ofSub_s(inst, expr1, dst, op1, op2, true);
        this->pf_s(inst, expr1, dst, true);
        this->sf_s(inst, expr1, dst, true);
        this->zf_s(inst, expr1, dst, true);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::seta_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto  cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
        auto  zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, cf);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, zf);

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
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SETA operation");

        /* Spread taint and condition flag */
        if (op2->evaluate().is_zero() && op3->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintUnion(dst, cf);
          expr->isTainted = this->taintEngine->taintUnion(dst, zf);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::setae_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto  cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, cf);

        /* Create the semantics */
        auto node = triton::ast::ite(
                      triton::ast::equal(op2, triton::ast::bvfalse()),
                      triton::ast::bv(1, dst.getBitSize()),
                      triton::ast::bv(0, dst.getBitSize())
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SETAE operation");

        /* Spread taint and condition flag */
        if (op2->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintUnion(dst, cf);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::setb_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto  cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, cf);

        /* Create the semantics */
        auto node = triton::ast::ite(
                      triton::ast::equal(op2, triton::ast::bvtrue()),
                      triton::ast::bv(1, dst.getBitSize()),
                      triton::ast::bv(0, dst.getBitSize())
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SETB operation");

        /* Spread taint and condition flag */
        if (!op2->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintUnion(dst, cf);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::setbe_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto  cf  = triton::arch::OperandWrapper(TRITON_X86_REG_CF);
        auto  zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, cf);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, zf);

        /* Create the semantics */
        auto node = triton::ast::ite(
                      triton::ast::equal(triton::ast::bvor(op2, op3), triton::ast::bvtrue()),
                      triton::ast::bv(1, dst.getBitSize()),
                      triton::ast::bv(0, dst.getBitSize())
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SETBE operation");

        /* Spread taint and condition flag */
        if (!op2->evaluate().is_zero() || !op3->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintUnion(dst, cf);
          expr->isTainted = this->taintEngine->taintUnion(dst, zf);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::sete_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto  zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, zf);

        /* Create the semantics */
        auto node = triton::ast::ite(
                      triton::ast::equal(op2, triton::ast::bvtrue()),
                      triton::ast::bv(1, dst.getBitSize()),
                      triton::ast::bv(0, dst.getBitSize())
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SETE operation");

        /* Spread taint and condition flag */
        if (!op2->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintUnion(dst, zf);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::setg_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto  sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
        auto  of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
        auto  zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, sf);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, of);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, zf);

        /* Create the semantics */
        auto node = triton::ast::ite(
                      triton::ast::equal(triton::ast::bvor(triton::ast::bvxor(op2, op3), op4), triton::ast::bvfalse()),
                      triton::ast::bv(1, dst.getBitSize()),
                      triton::ast::bv(0, dst.getBitSize())
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SETG operation");

        /* Spread taint and condition flag */
        if ((op2->evaluate().is_zero() == op3->evaluate().is_zero()) && op4->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintUnion(dst, sf);
          expr->isTainted = this->taintEngine->taintUnion(dst, of);
          expr->isTainted = this->taintEngine->taintUnion(dst, zf);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::setge_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto  sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
        auto  of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, sf);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, of);

        /* Create the semantics */
        auto node = triton::ast::ite(
                      triton::ast::equal(op2, op3),
                      triton::ast::bv(1, dst.getBitSize()),
                      triton::ast::bv(0, dst.getBitSize())
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SETGE operation");

        /* Spread taint and condition flag */
        if (op2->evaluate().is_zero() == op3->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintUnion(dst, sf);
          expr->isTainted = this->taintEngine->taintUnion(dst, of);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::setl_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto  sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
        auto  of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, sf);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, of);

        /* Create the semantics */
        auto node = triton::ast::ite(
                      triton::ast::equal(triton::ast::bvxor(op2, op3), triton::ast::bvtrue()),
                      triton::ast::bv(1, dst.getBitSize()),
                      triton::ast::bv(0, dst.getBitSize())
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SETL operation");

        /* Spread taint and condition flag */
        if (op2->evaluate().is_zero() != op3->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintUnion(dst, sf);
          expr->isTainted = this->taintEngine->taintUnion(dst, of);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::setle_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto  sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);
        auto  of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);
        auto  zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, sf);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, of);
        auto op4 = this->symbolicEngine->buildSymbolicOperand(inst, zf);

        /* Create the semantics */
        auto node = triton::ast::ite(
                      triton::ast::equal(triton::ast::bvor(triton::ast::bvxor(op2, op3), op4), triton::ast::bvtrue()),
                      triton::ast::bv(1, dst.getBitSize()),
                      triton::ast::bv(0, dst.getBitSize())
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SETLE operation");

        /* Spread taint and condition flag */
        if ((op2->evaluate().is_zero() != op3->evaluate().is_zero()) || !op4->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintUnion(dst, sf);
          expr->isTainted = this->taintEngine->taintUnion(dst, of);
          expr->isTainted = this->taintEngine->taintUnion(dst, zf);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::setne_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto  zf  = triton::arch::OperandWrapper(TRITON_X86_REG_ZF);

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, zf);

        /* Create the semantics */
        auto node = triton::ast::ite(
                      triton::ast::equal(op2, triton::ast::bvfalse()),
                      triton::ast::bv(1, dst.getBitSize()),
                      triton::ast::bv(0, dst.getBitSize())
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SETNE operation");

        /* Spread taint and condition flag */
        if (op2->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintUnion(dst, zf);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::setno_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto  of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, of);

        /* Create the semantics */
        auto node = triton::ast::ite(
                      triton::ast::equal(op2, triton::ast::bvfalse()),
                      triton::ast::bv(1, dst.getBitSize()),
                      triton::ast::bv(0, dst.getBitSize())
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SETNO operation");

        /* Spread taint and condition flag */
        if (op2->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintUnion(dst, of);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::setnp_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto  pf  = triton::arch::OperandWrapper(TRITON_X86_REG_PF);

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, pf);

        /* Create the semantics */
        auto node = triton::ast::ite(
                      triton::ast::equal(op2, triton::ast::bvfalse()),
                      triton::ast::bv(1, dst.getBitSize()),
                      triton::ast::bv(0, dst.getBitSize())
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SETNP operation");

        /* Spread taint and condition flag */
        if (op2->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintUnion(dst, pf);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::setns_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto  sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, sf);

        /* Create the semantics */
        auto node = triton::ast::ite(
                      triton::ast::equal(op2, triton::ast::bvfalse()),
                      triton::ast::bv(1, dst.getBitSize()),
                      triton::ast::bv(0, dst.getBitSize())
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SETNS operation");

        /* Spread taint and condition flag */
        if (op2->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintUnion(dst, sf);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::seto_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto  of  = triton::arch::OperandWrapper(TRITON_X86_REG_OF);

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, of);

        /* Create the semantics */
        auto node = triton::ast::ite(
                      triton::ast::equal(op2, triton::ast::bvtrue()),
                      triton::ast::bv(1, dst.getBitSize()),
                      triton::ast::bv(0, dst.getBitSize())
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SETO operation");

        /* Spread taint and condition flag */
        if (!op2->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintUnion(dst, of);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::setp_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto  pf  = triton::arch::OperandWrapper(TRITON_X86_REG_PF);

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, pf);

        /* Create the semantics */
        auto node = triton::ast::ite(
                      triton::ast::equal(op2, triton::ast::bvtrue()),
                      triton::ast::bv(1, dst.getBitSize()),
                      triton::ast::bv(0, dst.getBitSize())
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SETP operation");

        /* Spread taint and condition flag */
        if (!op2->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintUnion(dst, pf);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::sets_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto  sf  = triton::arch::OperandWrapper(TRITON_X86_REG_SF);

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, sf);

        /* Create the semantics */
        auto node = triton::ast::ite(
                      triton::ast::equal(op2, triton::ast::bvtrue()),
                      triton::ast::bv(1, dst.getBitSize()),
                      triton::ast::bv(0, dst.getBitSize())
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SETS operation");

        /* Spread taint and condition flag */
        if (!op2->evaluate().is_zero()) {
          expr->isTainted = this->taintEngine->taintUnion(dst, sf);
          inst.setConditionTaken(true);
        }
        else
          expr->isTainted = this->taintEngine->taintUnion(dst, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::sfence_s(triton::arch::Instruction& inst) {
        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::shl_s(triton::arch::Instruction& inst) {
        auto& dst   = inst.operands[0];
        auto& src   = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = triton::ast::zx(dst.getBitSize() - src.getBitSize(), this->symbolicEngine->buildSymbolicOperand(inst, src));

        if (dst.getBitSize() == QWORD_SIZE_BIT)
          op2 = triton::ast::bvand(op2, triton::ast::bv(QWORD_SIZE_BIT-1, dst.getBitSize()));
        else
          op2 = triton::ast::bvand(op2, triton::ast::bv(DWORD_SIZE_BIT-1, dst.getBitSize()));

        /* Create the semantics */
        auto node = triton::ast::bvshl(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SHL operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate symbolic flags */
        this->cfShl_s(inst, expr, dst, op1, op2);
        this->ofShl_s(inst, expr, dst, op1, op2);
        this->pfShl_s(inst, expr, dst, op2);
        this->sfShl_s(inst, expr, dst, op2);
        this->zfShl_s(inst, expr, dst, op2);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::shld_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, src2);

        switch (dst.getBitSize()) {
          /* Mask 0x3f MOD size */
          case QWORD_SIZE_BIT:
            op3 = triton::ast::bvsmod(
                    triton::ast::bvand(
                      op3,
                      triton::ast::bv(QWORD_SIZE_BIT-1, src2.getBitSize())),
                    triton::ast::bv(dst.getBitSize(), src2.getBitSize())
                  );
            break;

          /* Mask 0x1f MOD size */
          case DWORD_SIZE_BIT:
          case WORD_SIZE_BIT:
            op3 = triton::ast::bvsmod(
                    triton::ast::bvand(
                      op3,
                      triton::ast::bv(DWORD_SIZE_BIT-1, src2.getBitSize())),
                    triton::ast::bv(DWORD_SIZE_BIT, src2.getBitSize())
                  );
            break;

          default:
            throw triton::exceptions::Semantics("x86Semantics::shld_s(): Invalid destination size");
        }

        /* Create the semantics */
        auto node = triton::ast::extract(
                      dst.getBitSize()-1, 0,
                      triton::ast::bvrol(
                        triton::ast::decimal(op3->evaluate()),
                        triton::ast::concat(op2, op1))
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SHLD operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src1);
        expr->isTainted |= this->taintEngine->taintUnion(dst, src2);

        /* Upate symbolic flags */
        this->cfShld_s(inst, expr, dst, op1, op2, op3);
        this->ofShld_s(inst, expr, dst, op1, op2, op3);
        this->pfShl_s(inst, expr, dst, op3); /* Same that shl */
        this->sfShld_s(inst, expr, dst, op1, op2, op3);
        this->zfShl_s(inst, expr, dst, op3); /* Same that shl */

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::shlx_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src2);

        switch (dst.getBitSize()) {
          /* Mask 0x3f MOD size */
          case QWORD_SIZE_BIT:
            op2 = triton::ast::bvand(op2, triton::ast::bv(QWORD_SIZE_BIT-1, src2.getBitSize()));
            break;

          /* Mask 0x1f MOD size */
          case DWORD_SIZE_BIT:
            op2 = triton::ast::bvand(op2, triton::ast::bv(DWORD_SIZE_BIT-1, src2.getBitSize()));
            break;

          default:
            throw triton::exceptions::Semantics("x86Semantics::shlx_s(): Invalid destination size");
        }

        /* Create the semantics */
        auto node = triton::ast::bvshl(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SHLX operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src1);
        expr->isTainted |= this->taintEngine->taintUnion(dst, src2);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::shr_s(triton::arch::Instruction& inst) {
        auto& dst   = inst.operands[0];
        auto& src   = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = triton::ast::zx(dst.getBitSize() - src.getBitSize(), this->symbolicEngine->buildSymbolicOperand(inst, src));

        if (dst.getBitSize() == QWORD_SIZE_BIT)
          op2 = triton::ast::bvand(op2, triton::ast::bv(QWORD_SIZE_BIT-1, dst.getBitSize()));
        else
          op2 = triton::ast::bvand(op2, triton::ast::bv(DWORD_SIZE_BIT-1, dst.getBitSize()));

        /* Create the semantics */
        auto node = triton::ast::bvlshr(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SHR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate symbolic flags */
        this->cfShr_s(inst, expr, dst, op1, op2);
        this->ofShr_s(inst, expr, dst, op1, op2);
        this->pfShl_s(inst, expr, dst, op2); /* Same that shl */
        this->sfShl_s(inst, expr, dst, op2); /* Same that shl */
        this->zfShl_s(inst, expr, dst, op2); /* Same that shl */

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::shrd_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, src2);

        switch (dst.getBitSize()) {
          /* Mask 0x3f MOD size */
          case QWORD_SIZE_BIT:
            op3 = triton::ast::bvsmod(
                    triton::ast::bvand(
                      op3,
                      triton::ast::bv(QWORD_SIZE_BIT-1, src2.getBitSize())),
                    triton::ast::bv(dst.getBitSize(), src2.getBitSize())
                  );
            break;

          /* Mask 0x1f MOD size */
          case DWORD_SIZE_BIT:
          case WORD_SIZE_BIT:
            op3 = triton::ast::bvsmod(
                    triton::ast::bvand(
                      op3,
                      triton::ast::bv(DWORD_SIZE_BIT-1, src2.getBitSize())),
                    triton::ast::bv(DWORD_SIZE_BIT, src2.getBitSize())
                  );
            break;

          default:
            throw triton::exceptions::Semantics("x86Semantics::shrd_s(): Invalid destination size");
        }

        /* Create the semantics */
        auto node = triton::ast::extract(
                      dst.getBitSize()-1, 0,
                      triton::ast::bvror(
                        triton::ast::decimal(op3->evaluate()),
                        triton::ast::concat(op2, op1))
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SHRD operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src1);
        expr->isTainted |= this->taintEngine->taintUnion(dst, src2);

        /* Upate symbolic flags */
        this->cfShrd_s(inst, expr, dst, op1, op2, op3);
        this->ofShrd_s(inst, expr, dst, op1, op2, op3);
        this->pfShl_s(inst, expr, dst, op3); /* Same that shl */
        this->sfShrd_s(inst, expr, dst, op1, op2, op3);
        this->zfShl_s(inst, expr, dst, op3); /* Same that shl */

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::shrx_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src2);

        switch (dst.getBitSize()) {
          /* Mask 0x3f MOD size */
          case QWORD_SIZE_BIT:
            op2 = triton::ast::bvand(op2, triton::ast::bv(QWORD_SIZE_BIT-1, src2.getBitSize()));
            break;

          /* Mask 0x1f MOD size */
          case DWORD_SIZE_BIT:
            op2 = triton::ast::bvand(op2, triton::ast::bv(DWORD_SIZE_BIT-1, src2.getBitSize()));
            break;

          default:
            throw triton::exceptions::Semantics("x86Semantics::shrx_s(): Invalid destination size");
        }

        /* Create the semantics */
        auto node = triton::ast::bvlshr(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SHRX operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src1);
        expr->isTainted |= this->taintEngine->taintUnion(dst, src2);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::stc_s(triton::arch::Instruction& inst) {
        this->setFlag_s(inst, TRITON_X86_REG_CF, "Sets carry flag");
        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::std_s(triton::arch::Instruction& inst) {
        this->setFlag_s(inst, TRITON_X86_REG_DF, "Sets direction flag");
        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::sti_s(triton::arch::Instruction& inst) {
        this->setFlag_s(inst, TRITON_X86_REG_IF, "Sets interrupt flag");
        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::stmxcsr_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto  src = triton::arch::OperandWrapper(TRITON_X86_REG_MXCSR);

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::extract(DWORD_SIZE_BIT-1, 0, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "STMXCSR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::stosb_s(triton::arch::Instruction& inst) {
        auto& dst    = inst.operands[0];
        auto& src    = inst.operands[1];
        auto  index  = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
        auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, index);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, df);

        /* Create the semantics */
        auto node1 = op1;
        auto node2 = triton::ast::ite(
                       triton::ast::equal(op3, triton::ast::bvfalse()),
                       triton::ast::bvadd(op2, triton::ast::bv(BYTE_SIZE, index.getBitSize())),
                       triton::ast::bvsub(op2, triton::ast::bv(BYTE_SIZE, index.getBitSize()))
                     );

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "STOSB operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, index, "Index operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst, src);
        expr2->isTainted = this->taintEngine->taintUnion(index, index);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::stosd_s(triton::arch::Instruction& inst) {
        auto& dst    = inst.operands[0];
        auto& src    = inst.operands[1];
        auto  index  = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
        auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, index);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, df);

        /* Create the semantics */
        auto node1 = op1;
        auto node2 = triton::ast::ite(
                       triton::ast::equal(op3, triton::ast::bvfalse()),
                       triton::ast::bvadd(op2, triton::ast::bv(DWORD_SIZE, index.getBitSize())),
                       triton::ast::bvsub(op2, triton::ast::bv(DWORD_SIZE, index.getBitSize()))
                     );

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "STOSD operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, index, "Index operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst, src);
        expr2->isTainted = this->taintEngine->taintUnion(index, index);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::stosq_s(triton::arch::Instruction& inst) {
        auto& dst    = inst.operands[0];
        auto& src    = inst.operands[1];
        auto  index  = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
        auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, index);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, df);

        /* Create the semantics */
        auto node1 = op1;
        auto node2 = triton::ast::ite(
                       triton::ast::equal(op3, triton::ast::bvfalse()),
                       triton::ast::bvadd(op2, triton::ast::bv(QWORD_SIZE, index.getBitSize())),
                       triton::ast::bvsub(op2, triton::ast::bv(QWORD_SIZE, index.getBitSize()))
                     );

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "STOSQ operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, index, "Index operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst, src);
        expr2->isTainted = this->taintEngine->taintUnion(index, index);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::stosw_s(triton::arch::Instruction& inst) {
        auto& dst    = inst.operands[0];
        auto& src    = inst.operands[1];
        auto  index  = triton::arch::OperandWrapper(TRITON_X86_REG_DI.getParent());
        auto  df     = triton::arch::OperandWrapper(TRITON_X86_REG_DF);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, index);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, df);

        /* Create the semantics */
        auto node1 = op1;
        auto node2 = triton::ast::ite(
                       triton::ast::equal(op3, triton::ast::bvfalse()),
                       triton::ast::bvadd(op2, triton::ast::bv(WORD_SIZE, index.getBitSize())),
                       triton::ast::bvsub(op2, triton::ast::bv(WORD_SIZE, index.getBitSize()))
                     );

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "STOSW operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, index, "Index operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst, src);
        expr2->isTainted = this->taintEngine->taintUnion(index, index);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::sub_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::bvsub(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "SUB operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate symbolic flags */
        this->af_s(inst, expr, dst, op1, op2);
        this->cfSub_s(inst, expr, dst, op1, op2);
        this->ofSub_s(inst, expr, dst, op1, op2);
        this->pf_s(inst, expr, dst);
        this->sf_s(inst, expr, dst);
        this->zf_s(inst, expr, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::syscall_s(triton::arch::Instruction& inst) {
        auto dst1 = triton::arch::OperandWrapper(TRITON_X86_REG_RCX);
        auto dst2 = triton::arch::OperandWrapper(TRITON_X86_REG_R11);
        auto src1 = triton::arch::OperandWrapper(TRITON_X86_REG_RIP);
        auto src2 = triton::arch::OperandWrapper(TRITON_X86_REG_EFLAGS);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src2);

        /* Create the semantics */
        auto node1 = triton::ast::bvadd(op1, triton::ast::bv(inst.getSize(), src1.getBitSize()));
        auto node2 = op2;

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst1, "SYSCALL RCX operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, dst2, "SYSCALL R11 operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->taintAssignment(dst1, src1);
        expr2->isTainted = this->taintEngine->taintAssignment(dst2, src2);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::test_s(triton::arch::Instruction& inst) {
        auto& src1 = inst.operands[0];
        auto& src2 = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src2);

        /* Create the semantics */
        auto node = triton::ast::bvand(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicVolatileExpression(inst, node, "TEST operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2);

        /* Upate symbolic flags */
        this->clearFlag_s(inst, TRITON_X86_REG_CF, "Clears carry flag");
        this->clearFlag_s(inst, TRITON_X86_REG_OF, "Clears overflow flag");
        this->pf_s(inst, expr, src1, true);
        this->sf_s(inst, expr, src1, true);
        this->zf_s(inst, expr, src1, true);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::tzcnt_s(triton::arch::Instruction& inst) {
        auto& dst     = inst.operands[0];
        auto& src     = inst.operands[1];
        auto  bvSize1 = dst.getBitSize();
        auto  bvSize2 = src.getBitSize();

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        triton::ast::AbstractNode* node = nullptr;
        switch (src.getSize()) {
          case BYTE_SIZE:
            node = triton::ast::ite(
                     triton::ast::equal(op2, triton::ast::bv(0, bvSize2)),
                     triton::ast::bv(bvSize1, bvSize1),
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
                     triton::ast::equal(op2, triton::ast::bv(0, bvSize2)),
                     triton::ast::bv(bvSize1, bvSize1),
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
                     triton::ast::equal(op2, triton::ast::bv(0, bvSize2)),
                     triton::ast::bv(bvSize1, bvSize1),
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
                     triton::ast::equal(op2, triton::ast::bv(0, bvSize2)),
                     triton::ast::bv(bvSize1, bvSize1),
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
            throw triton::exceptions::Semantics("x86Semantics::tzcnt_s(): Invalid operand size.");
        }

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "TZCNT operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate symbolic flags */
        this->zf_s(inst, expr, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::unpckhpd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::concat(
                      triton::ast::extract(127, 64, op2),
                      triton::ast::extract(127, 64, op1)
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "UNPCKHPD operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::unpckhps_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        std::list<triton::ast::AbstractNode*> unpack;

        unpack.push_back(triton::ast::extract(127, 96, op2));
        unpack.push_back(triton::ast::extract(127, 96, op1));
        unpack.push_back(triton::ast::extract(95, 64, op2));
        unpack.push_back(triton::ast::extract(95, 64, op1));

        auto node = triton::ast::concat(unpack);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "UNPCKHPS operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::unpcklpd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::concat(
                      triton::ast::extract(63, 0, op2),
                      triton::ast::extract(63, 0, op1)
                    );

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "UNPCKLPD operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::unpcklps_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        std::list<triton::ast::AbstractNode*> unpack;

        unpack.push_back(triton::ast::extract(63, 32, op2));
        unpack.push_back(triton::ast::extract(63, 32, op1));
        unpack.push_back(triton::ast::extract(31, 0, op2));
        unpack.push_back(triton::ast::extract(31, 0, op1));

        auto node = triton::ast::concat(unpack);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "UNPCKLPS operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::vmovdqa_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create the semantics */
        auto node = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "VMOVDQA operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::vmovdqu_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create the semantics */
        auto node = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "VMOVDQU operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::vpand_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, src2);

        /* Create the semantics */
        auto node = triton::ast::bvand(op2, op3);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "VPAND operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src1) | this->taintEngine->taintUnion(dst, src2);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::vpandn_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, src2);

        /* Create the semantics */
        auto node = triton::ast::bvand(triton::ast::bvnot(op2), op3);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "VPANDN operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src1) | this->taintEngine->taintUnion(dst, src2);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::vpor_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, src2);

        /* Create the semantics */
        auto node = triton::ast::bvor(op2, op3);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "VPOR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src1) | this->taintEngine->taintUnion(dst, src2);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::vpshufd_s(triton::arch::Instruction& inst) {
        auto& dst               = inst.operands[0];
        auto& src               = inst.operands[1];
        auto& ord               = inst.operands[2];
        triton::uint32 dstSize  = dst.getBitSize();

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, ord);

        /* Create the semantics */
        std::list<triton::ast::AbstractNode*> pack;

        switch (dstSize) {

          /* YMM */
          case QQWORD_SIZE_BIT:
            pack.push_back(
              triton::ast::extract(31, 0,
                triton::ast::bvlshr(
                  op2,
                  triton::ast::bvmul(
                    triton::ast::zx(dstSize-2, triton::ast::extract(7, 6, op3)),
                    triton::ast::bv(32, dstSize)
                  )
                )
              )
            );
            pack.push_back(
              triton::ast::extract(31, 0,
                triton::ast::bvlshr(
                  op2,
                  triton::ast::bvmul(
                    triton::ast::zx(dstSize-2, triton::ast::extract(5, 4, op3)),
                    triton::ast::bv(32, dstSize)
                  )
                )
              )
            );
            pack.push_back(
              triton::ast::extract(31, 0,
                triton::ast::bvlshr(
                  op2,
                  triton::ast::bvmul(
                    triton::ast::zx(dstSize-2, triton::ast::extract(3, 2, op3)),
                    triton::ast::bv(32, dstSize)
                  )
                )
              )
            );
            pack.push_back(
              triton::ast::extract(31, 0,
                triton::ast::bvlshr(
                  op2,
                  triton::ast::bvmul(
                    triton::ast::zx(dstSize-2, triton::ast::extract(1, 0, op3)),
                    triton::ast::bv(32, dstSize)
                  )
                )
              )
            );

          /* XMM */
          case DQWORD_SIZE_BIT:
            pack.push_back(
              triton::ast::extract(31, 0,
                triton::ast::bvlshr(
                  op2,
                  triton::ast::bvmul(
                    triton::ast::zx(dstSize-2, triton::ast::extract(7, 6, op3)),
                    triton::ast::bv(32, dstSize)
                  )
                )
              )
            );
            pack.push_back(
              triton::ast::extract(31, 0,
                triton::ast::bvlshr(
                  op2,
                  triton::ast::bvmul(
                    triton::ast::zx(dstSize-2, triton::ast::extract(5, 4, op3)),
                    triton::ast::bv(32, dstSize)
                  )
                )
              )
            );
            pack.push_back(
              triton::ast::extract(31, 0,
                triton::ast::bvlshr(
                  op2,
                  triton::ast::bvmul(
                    triton::ast::zx(dstSize-2, triton::ast::extract(3, 2, op3)),
                    triton::ast::bv(32, dstSize)
                  )
                )
              )
            );
            pack.push_back(
              triton::ast::extract(31, 0,
                triton::ast::bvlshr(
                  op2,
                  triton::ast::bvmul(
                    triton::ast::zx(dstSize-2, triton::ast::extract(1, 0, op3)),
                    triton::ast::bv(32, dstSize)
                  )
                )
              )
            );
            break;

          default:
            throw triton::exceptions::Semantics("x86Semantics::vpshufd_s(): Invalid operand size.");
        }

        auto node = triton::ast::concat(pack);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "VPSHUFD operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::vptest_s(triton::arch::Instruction& inst) {
        auto& src1 = inst.operands[0];
        auto& src2 = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src2);

        /* Create the semantics */
        auto node1 = triton::ast::bvand(op1, op2);
        auto node2 = triton::ast::bvand(op1, triton::ast::bvnot(op2));

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node1, "VPTEST operation");
        auto expr2 = this->symbolicEngine->createSymbolicVolatileExpression(inst, node2, "VPTEST operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2);
        expr2->isTainted = this->taintEngine->isTainted(src1) | this->taintEngine->isTainted(src2);

        /* Upate symbolic flags */
        this->clearFlag_s(inst, TRITON_X86_REG_AF, "Clears adjust flag");
        this->cfPtest_s(inst, expr2, src1, true);
        this->clearFlag_s(inst, TRITON_X86_REG_OF, "Clears overflow flag");
        this->clearFlag_s(inst, TRITON_X86_REG_PF, "Clears parity flag");
        this->clearFlag_s(inst, TRITON_X86_REG_SF, "Clears sign flag");
        this->zf_s(inst, expr1, src1, true);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::vpxor_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src1 = inst.operands[1];
        auto& src2 = inst.operands[2];

        /* Create symbolic operands */
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src1);
        auto op3 = this->symbolicEngine->buildSymbolicOperand(inst, src2);

        /* Create the semantics */
        auto node = triton::ast::bvxor(op2, op3);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "VPXOR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintAssignment(dst, src1) | this->taintEngine->taintUnion(dst, src2);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::wbinvd_s(triton::arch::Instruction& inst) {
        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::xadd_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src  = inst.operands[1];
        bool  dstT = this->taintEngine->isTainted(dst);
        bool  srcT = this->taintEngine->isTainted(src);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node1 = op2;
        auto node2 = op1;

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "XCHG operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, src, "XCHG operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->setTaint(dst, srcT);
        expr2->isTainted = this->taintEngine->setTaint(src, dstT);

        /* Create symbolic operands */
        op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node3 = triton::ast::bvadd(op1, op2);

        /* Create symbolic expression */
        auto expr3 = this->symbolicEngine->createSymbolicExpression(inst, node3, dst, "ADD operation");

        /* Spread taint */
        expr3->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate symbolic flags */
        this->af_s(inst, expr3, dst, op1, op2);
        this->cfAdd_s(inst, expr3, dst, op1, op2);
        this->ofAdd_s(inst, expr3, dst, op1, op2);
        this->pf_s(inst, expr3, dst);
        this->sf_s(inst, expr3, dst);
        this->zf_s(inst, expr3, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::xchg_s(triton::arch::Instruction& inst) {
        auto& dst  = inst.operands[0];
        auto& src  = inst.operands[1];
        bool  dstT = this->taintEngine->isTainted(dst);
        bool  srcT = this->taintEngine->isTainted(src);

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node1 = op2;
        auto node2 = op1;

        /* Create symbolic expression */
        auto expr1 = this->symbolicEngine->createSymbolicExpression(inst, node1, dst, "XCHG operation");
        auto expr2 = this->symbolicEngine->createSymbolicExpression(inst, node2, src, "XCHG operation");

        /* Spread taint */
        expr1->isTainted = this->taintEngine->setTaint(dst, srcT);
        expr2->isTainted = this->taintEngine->setTaint(src, dstT);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::xor_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::bvxor(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "XOR operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate symbolic flags */
        this->clearFlag_s(inst, TRITON_X86_REG_CF, "Clears carry flag");
        this->clearFlag_s(inst, TRITON_X86_REG_OF, "Clears overflow flag");
        this->pf_s(inst, expr, dst);
        this->sf_s(inst, expr, dst);
        this->zf_s(inst, expr, dst);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::xorpd_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::bvxor(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "XORPD operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }


      void x86Semantics::xorps_s(triton::arch::Instruction& inst) {
        auto& dst = inst.operands[0];
        auto& src = inst.operands[1];

        /* Create symbolic operands */
        auto op1 = this->symbolicEngine->buildSymbolicOperand(inst, dst);
        auto op2 = this->symbolicEngine->buildSymbolicOperand(inst, src);

        /* Create the semantics */
        auto node = triton::ast::bvxor(op1, op2);

        /* Create symbolic expression */
        auto expr = this->symbolicEngine->createSymbolicExpression(inst, node, dst, "XORPS operation");

        /* Spread taint */
        expr->isTainted = this->taintEngine->taintUnion(dst, src);

        /* Upate the symbolic control flow */
        this->controlFlow_s(inst);
      }

    }; /* x86 namespace */
  }; /* arch namespace */
}; /* triton namespace */

