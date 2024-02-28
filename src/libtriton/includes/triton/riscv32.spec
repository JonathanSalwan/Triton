#pragma warning(disable:4067)

#if not (defined REG_SPEC || defined REG_SPEC_NO_CAPSTONE)
#error REG_SPEC have to be specified before including specs
#endif

#define TT_MUTABLE_REG    true
#define TT_IMMUTABLE_REG  false

// REG_SPEC(CS_UPPER_NAME, UPPER_NAME, LOWER_NAME, ABI_NAME, RISCV32_UPPER, RISCV32_LOWER, RISCV_PARENT, MUTABLE)

// Thirty-two 32-bit general-purpose registers
REG_SPEC(X0,  X0,  x0,  zero, triton::bitsize::dword-1, 0, TT_IMMUTABLE_REG) // x0 / zero
REG_SPEC(X1,  X1,  x1,  ra,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x1  / ra
REG_SPEC(SP,  SP,  x2,  sp,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x2  / sp
REG_SPEC(X3,  X3,  x3,  gp,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x3  / gp
REG_SPEC(X4,  X4,  x4,  tp,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x4  / tp
REG_SPEC(X5,  X5,  x5,  t0,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x5  / t0 or lr
REG_SPEC(X6,  X6,  x6,  t1,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x6  / t1
REG_SPEC(X7,  X7,  x7,  t2,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x7  / t2
REG_SPEC(X8,  X8,  x8,  s0,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x8  / s0 or fp
REG_SPEC(X9,  X9,  x9,  s1,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x9  / s1
REG_SPEC(X10, X10, x10, a0,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x10 / a0
REG_SPEC(X11, X11, x11, a1,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x11 / a1
REG_SPEC(X12, X12, x12, a2,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x12 / a2
REG_SPEC(X13, X13, x13, a3,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x13 / a3
REG_SPEC(X14, X14, x14, a4,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x14 / a4
REG_SPEC(X15, X15, x15, a5,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x15 / a5
REG_SPEC(X16, X16, x16, a6,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x16 / a6
REG_SPEC(X17, X17, x17, a7,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x17 / a7
REG_SPEC(X18, X18, x18, s2,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x18 / s2
REG_SPEC(X19, X19, x19, s3,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x19 / s3
REG_SPEC(X20, X20, x20, s4,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x20 / s4
REG_SPEC(X21, X21, x21, s5,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x21 / s5
REG_SPEC(X22, X22, x22, s6,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x22 / s6
REG_SPEC(X23, X23, x23, s7,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x23 / s7
REG_SPEC(X24, X24, x24, s8,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x24 / s8
REG_SPEC(X25, X25, x25, s9,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x25 / s9
REG_SPEC(X26, X26, x26, s10,  triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x26 / s10
REG_SPEC(X27, X27, x27, s11,  triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x27 / s11
REG_SPEC(X28, X28, x28, t3,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x28 / t3
REG_SPEC(X29, X29, x29, t4,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x29 / t4
REG_SPEC(X30, X30, x30, t5,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x30 / t5
REG_SPEC(X31, X31, x31, t6,   triton::bitsize::dword-1, 0, TT_MUTABLE_REG)   // x31 / t6

// 32-bit program counter register
REG_SPEC_NO_CAPSTONE(PC, PC, pc, pc, triton::bitsize::dword-1, 0, TT_MUTABLE_REG)  // PC

// Thirty-two 32-bit floating-point registers
REG_SPEC(F0_32,  F0,  f0,  ft0,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f0
REG_SPEC(F1_32,  F1,  f1,  ft1,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f1
REG_SPEC(F2_32,  F2,  f2,  ft2,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f2
REG_SPEC(F3_32,  F3,  f3,  ft3,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f3
REG_SPEC(F4_32,  F4,  f4,  ft4,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f4
REG_SPEC(F5_32,  F5,  f5,  ft5,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f5
REG_SPEC(F6_32,  F6,  f6,  ft6,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f6
REG_SPEC(F7_32,  F7,  f7,  ft7,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f7
REG_SPEC(F8_32,  F8,  f8,  fs0,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f8
REG_SPEC(F9_32,  F9,  f9,  fs1,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f9
REG_SPEC(F10_32, F10, f10, fa0,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f10
REG_SPEC(F11_32, F11, f11, fa1,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f11
REG_SPEC(F12_32, F12, f12, fa2,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f12
REG_SPEC(F13_32, F13, f13, fa3,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f13
REG_SPEC(F14_32, F14, f14, fa4,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f14
REG_SPEC(F15_32, F15, f15, fa5,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f15
REG_SPEC(F16_32, F16, f16, fa6,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f16
REG_SPEC(F17_32, F17, f17, fa7,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f17
REG_SPEC(F18_32, F18, f18, fs2,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f18
REG_SPEC(F19_32, F19, f19, fs3,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f19
REG_SPEC(F20_32, F20, f20, fs4,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f20
REG_SPEC(F21_32, F21, f21, fs5,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f21
REG_SPEC(F22_32, F22, f22, fs6,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f22
REG_SPEC(F23_32, F23, f23, fs7,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f23
REG_SPEC(F24_32, F24, f24, fs8,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f24
REG_SPEC(F25_32, F25, f25, fs9,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f25
REG_SPEC(F26_32, F26, f26, fs10, triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f26
REG_SPEC(F27_32, F27, f27, fs11, triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f27
REG_SPEC(F28_32, F28, f28, ft8,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f28
REG_SPEC(F29_32, F29, f29, ft9,  triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f29
REG_SPEC(F30_32, F30, f30, ft10, triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f30
REG_SPEC(F31_32, F31, f31, ft11, triton::bitsize::qword-1, 0, TT_MUTABLE_REG)   // f31

#undef REG_SPEC
#undef REG_SPEC_NO_CAPSTONE
#undef SYS_REG_SPEC
#undef TT_IMMUTABLE_REG
#undef TT_MUTABLE_REG

#pragma warning(default:4067)
