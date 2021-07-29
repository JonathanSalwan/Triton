#pragma warning(disable:4067)

#if not (defined REG_SPEC || defined REG_SPEC_NO_CAPSTONE)
#error REG_SPEC have to be specified before including specs
#endif

#define TT_MUTABLE_REG    true
#define TT_IMMUTABLE_REG  false

// REG_SPEC(UPPER_NAME, LOWER_NAME, AARCH64_UPPER, AARCH64_LOWER, AARCH64_PARENT, MUTABLE)

// Thirty-one 64-bit general-purpose registers 
REG_SPEC(X0,  x0,  triton::bitsize::qword-1, 0, X0,  TT_MUTABLE_REG) // x0
REG_SPEC(X1,  x1,  triton::bitsize::qword-1, 0, X1,  TT_MUTABLE_REG) // x1
REG_SPEC(X2,  x2,  triton::bitsize::qword-1, 0, X2,  TT_MUTABLE_REG) // x2
REG_SPEC(X3,  x3,  triton::bitsize::qword-1, 0, X3,  TT_MUTABLE_REG) // x3
REG_SPEC(X4,  x4,  triton::bitsize::qword-1, 0, X4,  TT_MUTABLE_REG) // x4
REG_SPEC(X5,  x5,  triton::bitsize::qword-1, 0, X5,  TT_MUTABLE_REG) // x5
REG_SPEC(X6,  x6,  triton::bitsize::qword-1, 0, X6,  TT_MUTABLE_REG) // x6
REG_SPEC(X7,  x7,  triton::bitsize::qword-1, 0, X7,  TT_MUTABLE_REG) // x7
REG_SPEC(X8,  x8,  triton::bitsize::qword-1, 0, X8,  TT_MUTABLE_REG) // x8
REG_SPEC(X9,  x9,  triton::bitsize::qword-1, 0, X9,  TT_MUTABLE_REG) // x9
REG_SPEC(X10, x10, triton::bitsize::qword-1, 0, X10, TT_MUTABLE_REG) // x10
REG_SPEC(X11, x11, triton::bitsize::qword-1, 0, X11, TT_MUTABLE_REG) // x11
REG_SPEC(X12, x12, triton::bitsize::qword-1, 0, X12, TT_MUTABLE_REG) // x12
REG_SPEC(X13, x13, triton::bitsize::qword-1, 0, X13, TT_MUTABLE_REG) // x13
REG_SPEC(X14, x14, triton::bitsize::qword-1, 0, X14, TT_MUTABLE_REG) // x14
REG_SPEC(X15, x15, triton::bitsize::qword-1, 0, X15, TT_MUTABLE_REG) // x15
REG_SPEC(X16, x16, triton::bitsize::qword-1, 0, X16, TT_MUTABLE_REG) // x16
REG_SPEC(X17, x17, triton::bitsize::qword-1, 0, X17, TT_MUTABLE_REG) // x17
REG_SPEC(X18, x18, triton::bitsize::qword-1, 0, X18, TT_MUTABLE_REG) // x18
REG_SPEC(X19, x19, triton::bitsize::qword-1, 0, X19, TT_MUTABLE_REG) // x19
REG_SPEC(X20, x20, triton::bitsize::qword-1, 0, X20, TT_MUTABLE_REG) // x20
REG_SPEC(X21, x21, triton::bitsize::qword-1, 0, X21, TT_MUTABLE_REG) // x21
REG_SPEC(X22, x22, triton::bitsize::qword-1, 0, X22, TT_MUTABLE_REG) // x22
REG_SPEC(X23, x23, triton::bitsize::qword-1, 0, X23, TT_MUTABLE_REG) // x23
REG_SPEC(X24, x24, triton::bitsize::qword-1, 0, X24, TT_MUTABLE_REG) // x24
REG_SPEC(X25, x25, triton::bitsize::qword-1, 0, X25, TT_MUTABLE_REG) // x25
REG_SPEC(X26, x26, triton::bitsize::qword-1, 0, X26, TT_MUTABLE_REG) // x26
REG_SPEC(X27, x27, triton::bitsize::qword-1, 0, X27, TT_MUTABLE_REG) // x27
REG_SPEC(X28, x28, triton::bitsize::qword-1, 0, X28, TT_MUTABLE_REG) // x28
REG_SPEC(X29, x29, triton::bitsize::qword-1, 0, X29, TT_MUTABLE_REG) // x29
REG_SPEC(X30, x30, triton::bitsize::qword-1, 0, X30, TT_MUTABLE_REG) // x30 (LR register)
REG_SPEC(W0,  w0,  triton::bitsize::dword-1, 0, X0,  TT_MUTABLE_REG)  // w0
REG_SPEC(W1,  w1,  triton::bitsize::dword-1, 0, X1,  TT_MUTABLE_REG)  // w1
REG_SPEC(W2,  w2,  triton::bitsize::dword-1, 0, X2,  TT_MUTABLE_REG)  // w2
REG_SPEC(W3,  w3,  triton::bitsize::dword-1, 0, X3,  TT_MUTABLE_REG)  // w3
REG_SPEC(W4,  w4,  triton::bitsize::dword-1, 0, X4,  TT_MUTABLE_REG)  // w4
REG_SPEC(W5,  w5,  triton::bitsize::dword-1, 0, X5,  TT_MUTABLE_REG)  // w5
REG_SPEC(W6,  w6,  triton::bitsize::dword-1, 0, X6,  TT_MUTABLE_REG)  // w6
REG_SPEC(W7,  w7,  triton::bitsize::dword-1, 0, X7,  TT_MUTABLE_REG)  // w7
REG_SPEC(W8,  w8,  triton::bitsize::dword-1, 0, X8,  TT_MUTABLE_REG)  // w8
REG_SPEC(W9,  w9,  triton::bitsize::dword-1, 0, X9,  TT_MUTABLE_REG)  // w9
REG_SPEC(W10, w10, triton::bitsize::dword-1, 0, X10, TT_MUTABLE_REG) // w10
REG_SPEC(W11, w11, triton::bitsize::dword-1, 0, X11, TT_MUTABLE_REG) // w11
REG_SPEC(W12, w12, triton::bitsize::dword-1, 0, X12, TT_MUTABLE_REG) // w12
REG_SPEC(W13, w13, triton::bitsize::dword-1, 0, X13, TT_MUTABLE_REG) // w13
REG_SPEC(W14, w14, triton::bitsize::dword-1, 0, X14, TT_MUTABLE_REG) // w14
REG_SPEC(W15, w15, triton::bitsize::dword-1, 0, X15, TT_MUTABLE_REG) // w15
REG_SPEC(W16, w16, triton::bitsize::dword-1, 0, X16, TT_MUTABLE_REG) // w16
REG_SPEC(W17, w17, triton::bitsize::dword-1, 0, X17, TT_MUTABLE_REG) // w17
REG_SPEC(W18, w18, triton::bitsize::dword-1, 0, X18, TT_MUTABLE_REG) // w18
REG_SPEC(W19, w19, triton::bitsize::dword-1, 0, X19, TT_MUTABLE_REG) // w19
REG_SPEC(W20, w20, triton::bitsize::dword-1, 0, X20, TT_MUTABLE_REG) // w20
REG_SPEC(W21, w21, triton::bitsize::dword-1, 0, X21, TT_MUTABLE_REG) // w21
REG_SPEC(W22, w22, triton::bitsize::dword-1, 0, X22, TT_MUTABLE_REG) // w22
REG_SPEC(W23, w23, triton::bitsize::dword-1, 0, X23, TT_MUTABLE_REG) // w23
REG_SPEC(W24, w24, triton::bitsize::dword-1, 0, X24, TT_MUTABLE_REG) // w24
REG_SPEC(W25, w25, triton::bitsize::dword-1, 0, X25, TT_MUTABLE_REG) // w25
REG_SPEC(W26, w26, triton::bitsize::dword-1, 0, X26, TT_MUTABLE_REG) // w26
REG_SPEC(W27, w27, triton::bitsize::dword-1, 0, X27, TT_MUTABLE_REG) // w27
REG_SPEC(W28, w28, triton::bitsize::dword-1, 0, X28, TT_MUTABLE_REG) // w28
REG_SPEC(W29, w29, triton::bitsize::dword-1, 0, X29, TT_MUTABLE_REG) // w29
REG_SPEC(W30, w30, triton::bitsize::dword-1, 0, X30, TT_MUTABLE_REG) // w30

// Flag register
REG_SPEC_NO_CAPSTONE(SPSR, spsr, 31, 0, SPSR, TT_MUTABLE_REG) // SPSR

// Stack pointer registers
REG_SPEC(SP,  sp,  triton::bitsize::qword-1, 0, SP, TT_MUTABLE_REG) // SP
REG_SPEC(WSP, wsp, triton::bitsize::dword-1, 0, SP, TT_MUTABLE_REG) // WSP

// Program counter register
REG_SPEC_NO_CAPSTONE(PC, pc, triton::bitsize::qword-1, 0, PC, TT_MUTABLE_REG) // PC

// Zero registers
REG_SPEC(XZR, xzr, triton::bitsize::qword-1, 0, XZR, TT_IMMUTABLE_REG) // XZR
REG_SPEC(WZR, wzr, triton::bitsize::dword-1, 0, XZR, TT_IMMUTABLE_REG) // WZR

// Unique flag registers
REG_SPEC_NO_CAPSTONE(C, c, 0, 0, C, TT_MUTABLE_REG) // C (Carry)
REG_SPEC_NO_CAPSTONE(N, n, 0, 0, N, TT_MUTABLE_REG) // N (Negative)
REG_SPEC_NO_CAPSTONE(V, v, 0, 0, V, TT_MUTABLE_REG) // V (Overflow)
REG_SPEC_NO_CAPSTONE(Z, z, 0, 0, Z, TT_MUTABLE_REG) // Z (Zero)

// Scalar Register
REG_SPEC(Q0,  q0,  triton::bitsize::dqword-1, 0, Q0,  TT_MUTABLE_REG) // q0
REG_SPEC(Q1,  q1,  triton::bitsize::dqword-1, 0, Q1,  TT_MUTABLE_REG) // q1
REG_SPEC(Q2,  q2,  triton::bitsize::dqword-1, 0, Q2,  TT_MUTABLE_REG) // q2
REG_SPEC(Q3,  q3,  triton::bitsize::dqword-1, 0, Q3,  TT_MUTABLE_REG) // q3
REG_SPEC(Q4,  q4,  triton::bitsize::dqword-1, 0, Q4,  TT_MUTABLE_REG) // q4
REG_SPEC(Q5,  q5,  triton::bitsize::dqword-1, 0, Q5,  TT_MUTABLE_REG) // q5
REG_SPEC(Q6,  q6,  triton::bitsize::dqword-1, 0, Q6,  TT_MUTABLE_REG) // q6
REG_SPEC(Q7,  q7,  triton::bitsize::dqword-1, 0, Q7,  TT_MUTABLE_REG) // q7
REG_SPEC(Q8,  q8,  triton::bitsize::dqword-1, 0, Q8,  TT_MUTABLE_REG) // q8
REG_SPEC(Q9,  q9,  triton::bitsize::dqword-1, 0, Q9,  TT_MUTABLE_REG) // q9
REG_SPEC(Q10, q10, triton::bitsize::dqword-1, 0, Q10, TT_MUTABLE_REG) // q10
REG_SPEC(Q11, q11, triton::bitsize::dqword-1, 0, Q11, TT_MUTABLE_REG) // q11
REG_SPEC(Q12, q12, triton::bitsize::dqword-1, 0, Q12, TT_MUTABLE_REG) // q12
REG_SPEC(Q13, q13, triton::bitsize::dqword-1, 0, Q13, TT_MUTABLE_REG) // q13
REG_SPEC(Q14, q14, triton::bitsize::dqword-1, 0, Q14, TT_MUTABLE_REG) // q14
REG_SPEC(Q15, q15, triton::bitsize::dqword-1, 0, Q15, TT_MUTABLE_REG) // q15
REG_SPEC(Q16, q16, triton::bitsize::dqword-1, 0, Q16, TT_MUTABLE_REG) // q16
REG_SPEC(Q17, q17, triton::bitsize::dqword-1, 0, Q17, TT_MUTABLE_REG) // q17
REG_SPEC(Q18, q18, triton::bitsize::dqword-1, 0, Q18, TT_MUTABLE_REG) // q18
REG_SPEC(Q19, q19, triton::bitsize::dqword-1, 0, Q19, TT_MUTABLE_REG) // q19
REG_SPEC(Q20, q20, triton::bitsize::dqword-1, 0, Q20, TT_MUTABLE_REG) // q20
REG_SPEC(Q21, q21, triton::bitsize::dqword-1, 0, Q21, TT_MUTABLE_REG) // q21
REG_SPEC(Q22, q22, triton::bitsize::dqword-1, 0, Q22, TT_MUTABLE_REG) // q22
REG_SPEC(Q23, q23, triton::bitsize::dqword-1, 0, Q23, TT_MUTABLE_REG) // q23
REG_SPEC(Q24, q24, triton::bitsize::dqword-1, 0, Q24, TT_MUTABLE_REG) // q24
REG_SPEC(Q25, q25, triton::bitsize::dqword-1, 0, Q25, TT_MUTABLE_REG) // q25
REG_SPEC(Q26, q26, triton::bitsize::dqword-1, 0, Q26, TT_MUTABLE_REG) // q26
REG_SPEC(Q27, q27, triton::bitsize::dqword-1, 0, Q27, TT_MUTABLE_REG) // q27
REG_SPEC(Q28, q28, triton::bitsize::dqword-1, 0, Q28, TT_MUTABLE_REG) // q28
REG_SPEC(Q29, q29, triton::bitsize::dqword-1, 0, Q29, TT_MUTABLE_REG) // q29
REG_SPEC(Q30, q30, triton::bitsize::dqword-1, 0, Q30, TT_MUTABLE_REG) // q30
REG_SPEC(Q31, q31, triton::bitsize::dqword-1, 0, Q31, TT_MUTABLE_REG) // q31

REG_SPEC(D0,  d0,  triton::bitsize::qword-1, 0, Q0,  TT_MUTABLE_REG) // d0
REG_SPEC(D1,  d1,  triton::bitsize::qword-1, 0, Q1,  TT_MUTABLE_REG) // d1
REG_SPEC(D2,  d2,  triton::bitsize::qword-1, 0, Q2,  TT_MUTABLE_REG) // d2
REG_SPEC(D3,  d3,  triton::bitsize::qword-1, 0, Q3,  TT_MUTABLE_REG) // d3
REG_SPEC(D4,  d4,  triton::bitsize::qword-1, 0, Q4,  TT_MUTABLE_REG) // d4
REG_SPEC(D5,  d5,  triton::bitsize::qword-1, 0, Q5,  TT_MUTABLE_REG) // d5
REG_SPEC(D6,  d6,  triton::bitsize::qword-1, 0, Q6,  TT_MUTABLE_REG) // d6
REG_SPEC(D7,  d7,  triton::bitsize::qword-1, 0, Q7,  TT_MUTABLE_REG) // d7
REG_SPEC(D8,  d8,  triton::bitsize::qword-1, 0, Q8,  TT_MUTABLE_REG) // d8
REG_SPEC(D9,  d9,  triton::bitsize::qword-1, 0, Q9,  TT_MUTABLE_REG) // d9
REG_SPEC(D10, d10, triton::bitsize::qword-1, 0, Q10, TT_MUTABLE_REG) // d10
REG_SPEC(D11, d11, triton::bitsize::qword-1, 0, Q11, TT_MUTABLE_REG) // d11
REG_SPEC(D12, d12, triton::bitsize::qword-1, 0, Q12, TT_MUTABLE_REG) // d12
REG_SPEC(D13, d13, triton::bitsize::qword-1, 0, Q13, TT_MUTABLE_REG) // d13
REG_SPEC(D14, d14, triton::bitsize::qword-1, 0, Q14, TT_MUTABLE_REG) // d14
REG_SPEC(D15, d15, triton::bitsize::qword-1, 0, Q15, TT_MUTABLE_REG) // d15
REG_SPEC(D16, d16, triton::bitsize::qword-1, 0, Q16, TT_MUTABLE_REG) // d16
REG_SPEC(D17, d17, triton::bitsize::qword-1, 0, Q17, TT_MUTABLE_REG) // d17
REG_SPEC(D18, d18, triton::bitsize::qword-1, 0, Q18, TT_MUTABLE_REG) // d18
REG_SPEC(D19, d19, triton::bitsize::qword-1, 0, Q19, TT_MUTABLE_REG) // d19
REG_SPEC(D20, d20, triton::bitsize::qword-1, 0, Q20, TT_MUTABLE_REG) // d20
REG_SPEC(D21, d21, triton::bitsize::qword-1, 0, Q21, TT_MUTABLE_REG) // d21
REG_SPEC(D22, d22, triton::bitsize::qword-1, 0, Q22, TT_MUTABLE_REG) // d22
REG_SPEC(D23, d23, triton::bitsize::qword-1, 0, Q23, TT_MUTABLE_REG) // d23
REG_SPEC(D24, d24, triton::bitsize::qword-1, 0, Q24, TT_MUTABLE_REG) // d24
REG_SPEC(D25, d25, triton::bitsize::qword-1, 0, Q25, TT_MUTABLE_REG) // d25
REG_SPEC(D26, d26, triton::bitsize::qword-1, 0, Q26, TT_MUTABLE_REG) // d26
REG_SPEC(D27, d27, triton::bitsize::qword-1, 0, Q27, TT_MUTABLE_REG) // d27
REG_SPEC(D28, d28, triton::bitsize::qword-1, 0, Q28, TT_MUTABLE_REG) // d28
REG_SPEC(D29, d29, triton::bitsize::qword-1, 0, Q29, TT_MUTABLE_REG) // d29
REG_SPEC(D30, d30, triton::bitsize::qword-1, 0, Q30, TT_MUTABLE_REG) // d30
REG_SPEC(D31, d31, triton::bitsize::qword-1, 0, Q31, TT_MUTABLE_REG) // d31

REG_SPEC(S0,  s0,  triton::bitsize::dword-1, 0, Q0,  TT_MUTABLE_REG) // s0
REG_SPEC(S1,  s1,  triton::bitsize::dword-1, 0, Q1,  TT_MUTABLE_REG) // s1
REG_SPEC(S2,  s2,  triton::bitsize::dword-1, 0, Q2,  TT_MUTABLE_REG) // s2
REG_SPEC(S3,  s3,  triton::bitsize::dword-1, 0, Q3,  TT_MUTABLE_REG) // s3
REG_SPEC(S4,  s4,  triton::bitsize::dword-1, 0, Q4,  TT_MUTABLE_REG) // s4
REG_SPEC(S5,  s5,  triton::bitsize::dword-1, 0, Q5,  TT_MUTABLE_REG) // s5
REG_SPEC(S6,  s6,  triton::bitsize::dword-1, 0, Q6,  TT_MUTABLE_REG) // s6
REG_SPEC(S7,  s7,  triton::bitsize::dword-1, 0, Q7,  TT_MUTABLE_REG) // s7
REG_SPEC(S8,  s8,  triton::bitsize::dword-1, 0, Q8,  TT_MUTABLE_REG) // s8
REG_SPEC(S9,  s9,  triton::bitsize::dword-1, 0, Q9,  TT_MUTABLE_REG) // s9
REG_SPEC(S10, s10, triton::bitsize::dword-1, 0, Q10, TT_MUTABLE_REG) // s10
REG_SPEC(S11, s11, triton::bitsize::dword-1, 0, Q11, TT_MUTABLE_REG) // s11
REG_SPEC(S12, s12, triton::bitsize::dword-1, 0, Q12, TT_MUTABLE_REG) // s12
REG_SPEC(S13, s13, triton::bitsize::dword-1, 0, Q13, TT_MUTABLE_REG) // s13
REG_SPEC(S14, s14, triton::bitsize::dword-1, 0, Q14, TT_MUTABLE_REG) // s14
REG_SPEC(S15, s15, triton::bitsize::dword-1, 0, Q15, TT_MUTABLE_REG) // s15
REG_SPEC(S16, s16, triton::bitsize::dword-1, 0, Q16, TT_MUTABLE_REG) // s16
REG_SPEC(S17, s17, triton::bitsize::dword-1, 0, Q17, TT_MUTABLE_REG) // s17
REG_SPEC(S18, s18, triton::bitsize::dword-1, 0, Q18, TT_MUTABLE_REG) // s18
REG_SPEC(S19, s19, triton::bitsize::dword-1, 0, Q19, TT_MUTABLE_REG) // s19
REG_SPEC(S20, s20, triton::bitsize::dword-1, 0, Q20, TT_MUTABLE_REG) // s20
REG_SPEC(S21, s21, triton::bitsize::dword-1, 0, Q21, TT_MUTABLE_REG) // s21
REG_SPEC(S22, s22, triton::bitsize::dword-1, 0, Q22, TT_MUTABLE_REG) // s22
REG_SPEC(S23, s23, triton::bitsize::dword-1, 0, Q23, TT_MUTABLE_REG) // s23
REG_SPEC(S24, s24, triton::bitsize::dword-1, 0, Q24, TT_MUTABLE_REG) // s24
REG_SPEC(S25, s25, triton::bitsize::dword-1, 0, Q25, TT_MUTABLE_REG) // s25
REG_SPEC(S26, s26, triton::bitsize::dword-1, 0, Q26, TT_MUTABLE_REG) // s26
REG_SPEC(S27, s27, triton::bitsize::dword-1, 0, Q27, TT_MUTABLE_REG) // s27
REG_SPEC(S28, s28, triton::bitsize::dword-1, 0, Q28, TT_MUTABLE_REG) // s28
REG_SPEC(S29, s29, triton::bitsize::dword-1, 0, Q29, TT_MUTABLE_REG) // s29
REG_SPEC(S30, s30, triton::bitsize::dword-1, 0, Q30, TT_MUTABLE_REG) // s30
REG_SPEC(S31, s31, triton::bitsize::dword-1, 0, Q31, TT_MUTABLE_REG) // s31

REG_SPEC(H0,  h0,  triton::bitsize::word-1, 0, Q0,  TT_MUTABLE_REG) // h0
REG_SPEC(H1,  h1,  triton::bitsize::word-1, 0, Q1,  TT_MUTABLE_REG) // h1
REG_SPEC(H2,  h2,  triton::bitsize::word-1, 0, Q2,  TT_MUTABLE_REG) // h2
REG_SPEC(H3,  h3,  triton::bitsize::word-1, 0, Q3,  TT_MUTABLE_REG) // h3
REG_SPEC(H4,  h4,  triton::bitsize::word-1, 0, Q4,  TT_MUTABLE_REG) // h4
REG_SPEC(H5,  h5,  triton::bitsize::word-1, 0, Q5,  TT_MUTABLE_REG) // h5
REG_SPEC(H6,  h6,  triton::bitsize::word-1, 0, Q6,  TT_MUTABLE_REG) // h6
REG_SPEC(H7,  h7,  triton::bitsize::word-1, 0, Q7,  TT_MUTABLE_REG) // h7
REG_SPEC(H8,  h8,  triton::bitsize::word-1, 0, Q8,  TT_MUTABLE_REG) // h8
REG_SPEC(H9,  h9,  triton::bitsize::word-1, 0, Q9,  TT_MUTABLE_REG) // h9
REG_SPEC(H10, h10, triton::bitsize::word-1, 0, Q10, TT_MUTABLE_REG) // h10
REG_SPEC(H11, h11, triton::bitsize::word-1, 0, Q11, TT_MUTABLE_REG) // h11
REG_SPEC(H12, h12, triton::bitsize::word-1, 0, Q12, TT_MUTABLE_REG) // h12
REG_SPEC(H13, h13, triton::bitsize::word-1, 0, Q13, TT_MUTABLE_REG) // h13
REG_SPEC(H14, h14, triton::bitsize::word-1, 0, Q14, TT_MUTABLE_REG) // h14
REG_SPEC(H15, h15, triton::bitsize::word-1, 0, Q15, TT_MUTABLE_REG) // h15
REG_SPEC(H16, h16, triton::bitsize::word-1, 0, Q16, TT_MUTABLE_REG) // h16
REG_SPEC(H17, h17, triton::bitsize::word-1, 0, Q17, TT_MUTABLE_REG) // h17
REG_SPEC(H18, h18, triton::bitsize::word-1, 0, Q18, TT_MUTABLE_REG) // h18
REG_SPEC(H19, h19, triton::bitsize::word-1, 0, Q19, TT_MUTABLE_REG) // h19
REG_SPEC(H20, h20, triton::bitsize::word-1, 0, Q20, TT_MUTABLE_REG) // h20
REG_SPEC(H21, h21, triton::bitsize::word-1, 0, Q21, TT_MUTABLE_REG) // h21
REG_SPEC(H22, h22, triton::bitsize::word-1, 0, Q22, TT_MUTABLE_REG) // h22
REG_SPEC(H23, h23, triton::bitsize::word-1, 0, Q23, TT_MUTABLE_REG) // h23
REG_SPEC(H24, h24, triton::bitsize::word-1, 0, Q24, TT_MUTABLE_REG) // h24
REG_SPEC(H25, h25, triton::bitsize::word-1, 0, Q25, TT_MUTABLE_REG) // h25
REG_SPEC(H26, h26, triton::bitsize::word-1, 0, Q26, TT_MUTABLE_REG) // h26
REG_SPEC(H27, h27, triton::bitsize::word-1, 0, Q27, TT_MUTABLE_REG) // h27
REG_SPEC(H28, h28, triton::bitsize::word-1, 0, Q28, TT_MUTABLE_REG) // h28
REG_SPEC(H29, h29, triton::bitsize::word-1, 0, Q29, TT_MUTABLE_REG) // h29
REG_SPEC(H30, h30, triton::bitsize::word-1, 0, Q30, TT_MUTABLE_REG) // h30
REG_SPEC(H31, h31, triton::bitsize::word-1, 0, Q31, TT_MUTABLE_REG) // h31

REG_SPEC(B0,  b0,  triton::bitsize::byte-1, 0, Q0,  TT_MUTABLE_REG) // b0
REG_SPEC(B1,  b1,  triton::bitsize::byte-1, 0, Q1,  TT_MUTABLE_REG) // b1
REG_SPEC(B2,  b2,  triton::bitsize::byte-1, 0, Q2,  TT_MUTABLE_REG) // b2
REG_SPEC(B3,  b3,  triton::bitsize::byte-1, 0, Q3,  TT_MUTABLE_REG) // b3
REG_SPEC(B4,  b4,  triton::bitsize::byte-1, 0, Q4,  TT_MUTABLE_REG) // b4
REG_SPEC(B5,  b5,  triton::bitsize::byte-1, 0, Q5,  TT_MUTABLE_REG) // b5
REG_SPEC(B6,  b6,  triton::bitsize::byte-1, 0, Q6,  TT_MUTABLE_REG) // b6
REG_SPEC(B7,  b7,  triton::bitsize::byte-1, 0, Q7,  TT_MUTABLE_REG) // b7
REG_SPEC(B8,  b8,  triton::bitsize::byte-1, 0, Q8,  TT_MUTABLE_REG) // b8
REG_SPEC(B9,  b9,  triton::bitsize::byte-1, 0, Q9,  TT_MUTABLE_REG) // b9
REG_SPEC(B10, b10, triton::bitsize::byte-1, 0, Q10, TT_MUTABLE_REG) // b10
REG_SPEC(B11, b11, triton::bitsize::byte-1, 0, Q11, TT_MUTABLE_REG) // b11
REG_SPEC(B12, b12, triton::bitsize::byte-1, 0, Q12, TT_MUTABLE_REG) // b12
REG_SPEC(B13, b13, triton::bitsize::byte-1, 0, Q13, TT_MUTABLE_REG) // b13
REG_SPEC(B14, b14, triton::bitsize::byte-1, 0, Q14, TT_MUTABLE_REG) // b14
REG_SPEC(B15, b15, triton::bitsize::byte-1, 0, Q15, TT_MUTABLE_REG) // b15
REG_SPEC(B16, b16, triton::bitsize::byte-1, 0, Q16, TT_MUTABLE_REG) // b16
REG_SPEC(B17, b17, triton::bitsize::byte-1, 0, Q17, TT_MUTABLE_REG) // b17
REG_SPEC(B18, b18, triton::bitsize::byte-1, 0, Q18, TT_MUTABLE_REG) // b18
REG_SPEC(B19, b19, triton::bitsize::byte-1, 0, Q19, TT_MUTABLE_REG) // b19
REG_SPEC(B20, b20, triton::bitsize::byte-1, 0, Q20, TT_MUTABLE_REG) // b20
REG_SPEC(B21, b21, triton::bitsize::byte-1, 0, Q21, TT_MUTABLE_REG) // b21
REG_SPEC(B22, b22, triton::bitsize::byte-1, 0, Q22, TT_MUTABLE_REG) // b22
REG_SPEC(B23, b23, triton::bitsize::byte-1, 0, Q23, TT_MUTABLE_REG) // b23
REG_SPEC(B24, b24, triton::bitsize::byte-1, 0, Q24, TT_MUTABLE_REG) // b24
REG_SPEC(B25, b25, triton::bitsize::byte-1, 0, Q25, TT_MUTABLE_REG) // b25
REG_SPEC(B26, b26, triton::bitsize::byte-1, 0, Q26, TT_MUTABLE_REG) // b26
REG_SPEC(B27, b27, triton::bitsize::byte-1, 0, Q27, TT_MUTABLE_REG) // b27
REG_SPEC(B28, b28, triton::bitsize::byte-1, 0, Q28, TT_MUTABLE_REG) // b28
REG_SPEC(B29, b29, triton::bitsize::byte-1, 0, Q29, TT_MUTABLE_REG) // b29
REG_SPEC(B30, b30, triton::bitsize::byte-1, 0, Q30, TT_MUTABLE_REG) // b30
REG_SPEC(B31, b31, triton::bitsize::byte-1, 0, Q31, TT_MUTABLE_REG) // b31

#undef REG_SPEC
#undef REG_SPEC_NO_CAPSTONE
#undef TT_IMMUTABLE_REG
#undef TT_MUTABLE_REG

#pragma warning(default:4067)
