#pragma warning(disable:4067)

#if not (defined REG_SPEC || defined REG_SPEC_NO_CAPSTONE)
#error REG_SPEC have to be specified before including specs
#endif

#define TT_MUTABLE_REG    true
#define TT_IMMUTABLE_REG  false

// REG_SPEC(UPPER_NAME, LOWER_NAME, ARM32_UPPER, ARM32_LOWER, ARM32_PARENT, MUTABLE)

// Thirteen general-purpose 32-bit registers, R0 to R12
REG_SPEC(R0,  r0,  DWORD_SIZE_BIT-1, 0, R0,  TT_MUTABLE_REG) // r0
REG_SPEC(R1,  r1,  DWORD_SIZE_BIT-1, 0, R1,  TT_MUTABLE_REG) // r1
REG_SPEC(R2,  r2,  DWORD_SIZE_BIT-1, 0, R2,  TT_MUTABLE_REG) // r2
REG_SPEC(R3,  r3,  DWORD_SIZE_BIT-1, 0, R3,  TT_MUTABLE_REG) // r3
REG_SPEC(R4,  r4,  DWORD_SIZE_BIT-1, 0, R4,  TT_MUTABLE_REG) // r4
REG_SPEC(R5,  r5,  DWORD_SIZE_BIT-1, 0, R5,  TT_MUTABLE_REG) // r5
REG_SPEC(R6,  r6,  DWORD_SIZE_BIT-1, 0, R6,  TT_MUTABLE_REG) // r6
REG_SPEC(R7,  r7,  DWORD_SIZE_BIT-1, 0, R7,  TT_MUTABLE_REG) // r7
REG_SPEC(R8,  r8,  DWORD_SIZE_BIT-1, 0, R8,  TT_MUTABLE_REG) // r8
REG_SPEC(R9,  r9,  DWORD_SIZE_BIT-1, 0, R9,  TT_MUTABLE_REG) // r9
REG_SPEC(R10, r10, DWORD_SIZE_BIT-1, 0, R10, TT_MUTABLE_REG) // r10
REG_SPEC(R11, r11, DWORD_SIZE_BIT-1, 0, R11, TT_MUTABLE_REG) // r11
REG_SPEC(R12, r12, DWORD_SIZE_BIT-1, 0, R12, TT_MUTABLE_REG) // r12

// Three 32-bit registers with special uses, SP, LR, and PC, that can be described as R13 to R15.
// Stack pointer register
REG_SPEC(SP, sp, DWORD_SIZE_BIT-1, 0, SP, TT_MUTABLE_REG) // SP

// Link register
REG_SPEC(R14, r14, DWORD_SIZE_BIT-1, 0, R14, TT_MUTABLE_REG) // LR (r14)

// Program counter register
REG_SPEC(PC, pc, DWORD_SIZE_BIT-1, 0, PC, TT_MUTABLE_REG) // PC

// Flag register
REG_SPEC(APSR, apsr, 31, 0, APSR, TT_MUTABLE_REG) // APSR

// Unique flag registers
REG_SPEC_NO_CAPSTONE(C, c, 0, 0, C, TT_MUTABLE_REG) // C (Carry)
REG_SPEC_NO_CAPSTONE(N, n, 0, 0, N, TT_MUTABLE_REG) // N (Negative)
REG_SPEC_NO_CAPSTONE(V, v, 0, 0, V, TT_MUTABLE_REG) // V (Overflow)
REG_SPEC_NO_CAPSTONE(Z, z, 0, 0, Z, TT_MUTABLE_REG) // Z (Zero)

#undef REG_SPEC
#undef REG_SPEC_NO_CAPSTONE
#undef TT_IMMUTABLE_REG
#undef TT_MUTABLE_REG

#pragma warning(default:4067)
