#pragma warning(disable:4067)

#if not (defined REG_SPEC || defined REG_SPEC_NO_CAPSTONE)
#error REG_SPEC have to be specified before including specs
#endif

// REG_SPEC(UPPER_NAME, LOWER_NAME, X86_64_UPPER, X84_84_LOWER, x86_64_PARENT, X86_UPPER, X86_LOWER, X86_PARENT, X86_AVAIL)

/* GPR 64-bits. */

REG_SPEC(RAX, rax, triton::bitsize::qword-1, 0, RAX, 0, 0, RAX, false) // rax
REG_SPEC(RBX, rbx, triton::bitsize::qword-1, 0, RBX, 0, 0, RBX, false) // rbx
REG_SPEC(RCX, rcx, triton::bitsize::qword-1, 0, RCX, 0, 0, RCX, false) // rcx
REG_SPEC(RDX, rdx, triton::bitsize::qword-1, 0, RDX, 0, 0, RDX, false) // rdx
REG_SPEC(RDI, rdi, triton::bitsize::qword-1, 0, RDI, 0, 0, RDI, false) // rdi
REG_SPEC(RSI, rsi, triton::bitsize::qword-1, 0, RSI, 0, 0, RSI, false) // rsi
REG_SPEC(RBP, rbp, triton::bitsize::qword-1, 0, RBP, 0, 0, RBP, false) // rbp
REG_SPEC(RSP, rsp, triton::bitsize::qword-1, 0, RSP, 0, 0, RSP, false) // rsp
REG_SPEC(RIP, rip, triton::bitsize::qword-1, 0, RIP, 0, 0, RIP, false) // rip

REG_SPEC(R8,  r8,  triton::bitsize::qword-1, 0, R8, 0, 0, R8, false)   // r8
REG_SPEC(R8D, r8d, triton::bitsize::dword-1, 0, R8, 0, 0, R8, false)   // r8d
REG_SPEC(R8W, r8w, triton::bitsize::word-1,  0, R8, 0, 0, R8, false)   // r8w
REG_SPEC(R8B, r8b, triton::bitsize::byte-1,  0, R8, 0, 0, R8, false)   // r8b

REG_SPEC(R9,  r9,  triton::bitsize::qword-1, 0, R9, 0, 0, R9, false)   // r9
REG_SPEC(R9D, r9d, triton::bitsize::dword-1, 0, R9, 0, 0, R9, false)   // r9d
REG_SPEC(R9W, r9w, triton::bitsize::word-1,  0, R9, 0, 0, R9, false)   // r9w
REG_SPEC(R9B, r9b, triton::bitsize::byte-1,  0, R9, 0, 0, R9, false)   // r9b

REG_SPEC(R10,  r10,  triton::bitsize::qword-1, 0, R10, 0, 0, R10, false)  // r10
REG_SPEC(R10D, r10d, triton::bitsize::dword-1, 0, R10, 0, 0, R10, false)  // r10d
REG_SPEC(R10W, r10w, triton::bitsize::word-1,  0, R10, 0, 0, R10, false)  // r10w
REG_SPEC(R10B, r10b, triton::bitsize::byte-1,  0, R10, 0, 0, R10, false)  // r10b

REG_SPEC(R11,  r11,  triton::bitsize::qword-1, 0, R11, 0, 0, R11, false)  // r11
REG_SPEC(R11D, r11d, triton::bitsize::dword-1, 0, R11, 0, 0, R11, false)  // r11d
REG_SPEC(R11W, r11w, triton::bitsize::word-1,  0, R11, 0, 0, R11, false)  // r11w
REG_SPEC(R11B, r11b, triton::bitsize::byte-1,  0, R11, 0, 0, R11, false)  // r11b

REG_SPEC(R12,  r12,  triton::bitsize::qword-1, 0, R12, 0, 0, R12, false)  // r12
REG_SPEC(R12D, r12d, triton::bitsize::dword-1, 0, R12, 0, 0, R12, false)  // r12d
REG_SPEC(R12W, r12w, triton::bitsize::word-1,  0, R12, 0, 0, R12, false)  // r12w
REG_SPEC(R12B, r12b, triton::bitsize::byte-1,  0, R12, 0, 0, R12, false)  // r12b

REG_SPEC(R13,  r13,  triton::bitsize::qword-1, 0, R13, 0, 0, R13, false)  // r13
REG_SPEC(R13D, r13d, triton::bitsize::dword-1, 0, R13, 0, 0, R13, false)  // r13d
REG_SPEC(R13W, r13w, triton::bitsize::word-1,  0, R13, 0, 0, R13, false)  // r13w
REG_SPEC(R13B, r13b, triton::bitsize::byte-1,  0, R13, 0, 0, R13, false)  // r13b

REG_SPEC(R14,  r14,  triton::bitsize::qword-1, 0, R14, 0, 0, R14, false)  // r14
REG_SPEC(R14D, r14d, triton::bitsize::dword-1, 0, R14, 0, 0, R14, false)  // r14d
REG_SPEC(R14W, r14w, triton::bitsize::word-1,  0, R14, 0, 0, R14, false)  // r14w
REG_SPEC(R14B, r14b, triton::bitsize::byte-1,  0, R14, 0, 0, R14, false)  // r14b

REG_SPEC(R15,  r15,  triton::bitsize::qword-1, 0, R15, 0, 0, R15, false)  // r15
REG_SPEC(R15D, r15d, triton::bitsize::dword-1, 0, R15, 0, 0, R15, false)  // r15d
REG_SPEC(R15W, r15w, triton::bitsize::word-1,  0, R15, 0, 0, R15, false)  // r15w
REG_SPEC(R15B, r15b, triton::bitsize::byte-1,  0, R15, 0, 0, R15, false)  // r15b

/* GPR 32-bits */

REG_SPEC(EAX, eax, triton::bitsize::dword-1, 0,                     RAX, triton::bitsize::dword-1, 0,                     EAX, true)  // eax
REG_SPEC(AX,  ax,  triton::bitsize::word-1,  0,                     RAX, triton::bitsize::word-1,  0,                     EAX, true)  // ax
REG_SPEC(AH,  ah,  triton::bitsize::word-1,  triton::bitsize::byte, RAX, triton::bitsize::word-1,  triton::bitsize::byte, EAX, true)  // ah
REG_SPEC(AL,  al,  triton::bitsize::byte-1,  0,                     RAX, triton::bitsize::byte-1,  0,                     EAX, true)  // al

REG_SPEC(EBX, ebx, triton::bitsize::dword-1, 0,                     RBX, triton::bitsize::dword-1, 0,                     EBX, true)  // ebx
REG_SPEC(BX,  bx,  triton::bitsize::word-1,  0,                     RBX, triton::bitsize::word-1,  0,                     EBX, true)  // bx
REG_SPEC(BH,  bh,  triton::bitsize::word-1,  triton::bitsize::byte, RBX, triton::bitsize::word-1,  triton::bitsize::byte, EBX, true)  // bh
REG_SPEC(BL,  bl,  triton::bitsize::byte-1,  0,                     RBX, triton::bitsize::byte-1,  0,                     EBX, true)  // bl

REG_SPEC(ECX, ecx, triton::bitsize::dword-1, 0,                     RCX, triton::bitsize::dword-1, 0,                     ECX, true)  // ecx
REG_SPEC(CX,  cx,  triton::bitsize::word-1,  0,                     RCX, triton::bitsize::word-1,  0,                     ECX, true)  // cx
REG_SPEC(CH,  ch,  triton::bitsize::word-1,  triton::bitsize::byte, RCX, triton::bitsize::word-1,  triton::bitsize::byte, ECX, true)  // ch
REG_SPEC(CL,  cl,  triton::bitsize::byte-1,  0,                     RCX, triton::bitsize::byte-1,  0,                     ECX, true)  // cl

REG_SPEC(EDX, edx, triton::bitsize::dword-1, 0,                     RDX, triton::bitsize::dword-1, 0,                     EDX, true)  // edx
REG_SPEC(DX,  dx,  triton::bitsize::word-1,  0,                     RDX, triton::bitsize::word-1,  0,                     EDX, true)  // dx
REG_SPEC(DH,  dh,  triton::bitsize::word-1,  triton::bitsize::byte, RDX, triton::bitsize::word-1,  triton::bitsize::byte, EDX, true)  // dh
REG_SPEC(DL,  dl,  triton::bitsize::byte-1,  0,                     RDX, triton::bitsize::byte-1,  0,                     EDX, true)  // dl

REG_SPEC(EDI, edi, triton::bitsize::dword-1, 0, RDI, triton::bitsize::dword-1, 0, EDI, true)  // edi
REG_SPEC(DI,  di,  triton::bitsize::word-1,  0, RDI, triton::bitsize::word-1,  0, EDI, true)  // di
REG_SPEC(DIL, dil, triton::bitsize::byte-1,  0, RDI, triton::bitsize::byte-1,  0, EDI, true)  // dil

REG_SPEC(ESI, esi, triton::bitsize::dword-1, 0, RSI, triton::bitsize::dword-1, 0, ESI, true)  // esi
REG_SPEC(SI,  si,  triton::bitsize::word-1,  0, RSI, triton::bitsize::word-1,  0, ESI, true)  // si
REG_SPEC(SIL, sil, triton::bitsize::byte-1,  0, RSI, triton::bitsize::byte-1,  0, ESI, true)  // sil

REG_SPEC(EBP, ebp, triton::bitsize::dword-1, 0, RBP, triton::bitsize::dword-1, 0, EBP, true)  // ebp
REG_SPEC(BP,  bp,  triton::bitsize::word-1,  0, RBP, triton::bitsize::word-1,  0, EBP, true)  // bp
REG_SPEC(BPL, bpl, triton::bitsize::byte-1,  0, RBP, triton::bitsize::byte-1,  0, EBP, true)  // bpl

REG_SPEC(ESP, esp, triton::bitsize::dword-1, 0, RSP, triton::bitsize::dword-1, 0, ESP, true)  // esp
REG_SPEC(SP,  sp,  triton::bitsize::word-1,  0, RSP, triton::bitsize::word-1,  0, ESP, true)  // sp
REG_SPEC(SPL, spl, triton::bitsize::byte-1,  0, RSP, triton::bitsize::byte-1,  0, ESP, true)  // spl

REG_SPEC(EIP, eip, triton::bitsize::dword-1, 0, RIP, triton::bitsize::dword-1, 0, EIP, true)  // eip
REG_SPEC(IP,  ip,  triton::bitsize::word-1,  0, RIP, triton::bitsize::word-1,  0, EIP, true)  // ip

REG_SPEC(EFLAGS, eflags, triton::bitsize::qword-1, 0, EFLAGS, triton::bitsize::dword-1, 0, EFLAGS, true) // eflags

/* MMX */

REG_SPEC(MM0, mm0, triton::bitsize::qword-1, 0, ST0, triton::bitsize::qword-1, 0, ST0, true) // mm0
REG_SPEC(MM1, mm1, triton::bitsize::qword-1, 0, ST1, triton::bitsize::qword-1, 0, ST1, true) // mm1
REG_SPEC(MM2, mm2, triton::bitsize::qword-1, 0, ST2, triton::bitsize::qword-1, 0, ST2, true) // mm2
REG_SPEC(MM3, mm3, triton::bitsize::qword-1, 0, ST3, triton::bitsize::qword-1, 0, ST3, true) // mm3
REG_SPEC(MM4, mm4, triton::bitsize::qword-1, 0, ST4, triton::bitsize::qword-1, 0, ST4, true) // mm4
REG_SPEC(MM5, mm5, triton::bitsize::qword-1, 0, ST5, triton::bitsize::qword-1, 0, ST5, true) // mm5
REG_SPEC(MM6, mm6, triton::bitsize::qword-1, 0, ST6, triton::bitsize::qword-1, 0, ST6, true) // mm6
REG_SPEC(MM7, mm7, triton::bitsize::qword-1, 0, ST7, triton::bitsize::qword-1, 0, ST7, true) // mm7

/* STX */

REG_SPEC(ST0, st0, triton::bitsize::fword-1, 0, ST0, triton::bitsize::fword-1, 0, ST0, true) // st0
REG_SPEC(ST1, st1, triton::bitsize::fword-1, 0, ST1, triton::bitsize::fword-1, 0, ST1, true) // st1
REG_SPEC(ST2, st2, triton::bitsize::fword-1, 0, ST2, triton::bitsize::fword-1, 0, ST2, true) // st2
REG_SPEC(ST3, st3, triton::bitsize::fword-1, 0, ST3, triton::bitsize::fword-1, 0, ST3, true) // st3
REG_SPEC(ST4, st4, triton::bitsize::fword-1, 0, ST4, triton::bitsize::fword-1, 0, ST4, true) // st4
REG_SPEC(ST5, st5, triton::bitsize::fword-1, 0, ST5, triton::bitsize::fword-1, 0, ST5, true) // st5
REG_SPEC(ST6, st6, triton::bitsize::fword-1, 0, ST6, triton::bitsize::fword-1, 0, ST6, true) // st6
REG_SPEC(ST7, st7, triton::bitsize::fword-1, 0, ST7, triton::bitsize::fword-1, 0, ST7, true) // st7

/* FPU */

REG_SPEC_NO_CAPSTONE(FTW, ftw, triton::bitsize::word-1,  0, FTW, triton::bitsize::word-1,  0, FTW, true) // ftw
REG_SPEC_NO_CAPSTONE(FCW, fcw, triton::bitsize::word-1,  0, FCW, triton::bitsize::word-1,  0, FCW, true) // fcw
REG_SPEC_NO_CAPSTONE(FSW, fsw, triton::bitsize::word-1,  0, FSW, triton::bitsize::word-1,  0, FSW, true) // fsw
REG_SPEC_NO_CAPSTONE(FOP, fop, triton::bitsize::word-1,  0, FOP, triton::bitsize::word-1,  0, FOP, true) // fop
REG_SPEC_NO_CAPSTONE(FCS, fcs, triton::bitsize::word-1,  0, FCS, triton::bitsize::word-1,  0, FCS, true) // fcs
REG_SPEC_NO_CAPSTONE(FDS, fds, triton::bitsize::word-1,  0, FDS, triton::bitsize::word-1,  0, FDS, true) // fds
REG_SPEC_NO_CAPSTONE(FIP, fip, triton::bitsize::qword-1, 0, FIP, triton::bitsize::qword-1, 0, FIP, true) // fip
REG_SPEC_NO_CAPSTONE(FDP, fdp, triton::bitsize::qword-1, 0, FDP, triton::bitsize::qword-1, 0, FDP, true) // fdp

/* SSE */

REG_SPEC_NO_CAPSTONE(MXCSR,      mxcsr,      triton::bitsize::dword-1, 0, MXCSR,      triton::bitsize::dword-1, 0, MXCSR,      true) // mxcsr
REG_SPEC_NO_CAPSTONE(MXCSR_MASK, mxcsr_mask, triton::bitsize::dword-1, 0, MXCSR_MASK, triton::bitsize::dword-1, 0, MXCSR_MASK, true) // mxcsr mask

REG_SPEC(XMM0,  xmm0,  triton::bitsize::dqword-1, 0, ZMM0,  triton::bitsize::dqword-1, 0, YMM0,  true)  // xmm0
REG_SPEC(XMM1,  xmm1,  triton::bitsize::dqword-1, 0, ZMM1,  triton::bitsize::dqword-1, 0, YMM1,  true)  // xmm1
REG_SPEC(XMM2,  xmm2,  triton::bitsize::dqword-1, 0, ZMM2,  triton::bitsize::dqword-1, 0, YMM2,  true)  // xmm2
REG_SPEC(XMM3,  xmm3,  triton::bitsize::dqword-1, 0, ZMM3,  triton::bitsize::dqword-1, 0, YMM3,  true)  // xmm3
REG_SPEC(XMM4,  xmm4,  triton::bitsize::dqword-1, 0, ZMM4,  triton::bitsize::dqword-1, 0, YMM4,  true)  // xmm4
REG_SPEC(XMM5,  xmm5,  triton::bitsize::dqword-1, 0, ZMM5,  triton::bitsize::dqword-1, 0, YMM5,  true)  // xmm5
REG_SPEC(XMM6,  xmm6,  triton::bitsize::dqword-1, 0, ZMM6,  triton::bitsize::dqword-1, 0, YMM6,  true)  // xmm6
REG_SPEC(XMM7,  xmm7,  triton::bitsize::dqword-1, 0, ZMM7,  triton::bitsize::dqword-1, 0, YMM7,  true)  // xmm7
REG_SPEC(XMM8,  xmm8,  triton::bitsize::dqword-1, 0, ZMM8,  0,                         0, XMM8,  false) // xmm8
REG_SPEC(XMM9,  xmm9,  triton::bitsize::dqword-1, 0, ZMM9,  0,                         0, XMM9,  false) // xmm9
REG_SPEC(XMM10, xmm10, triton::bitsize::dqword-1, 0, ZMM10, 0,                         0, XMM10, false) // xmm10
REG_SPEC(XMM11, xmm11, triton::bitsize::dqword-1, 0, ZMM11, 0,                         0, XMM11, false) // xmm11
REG_SPEC(XMM12, xmm12, triton::bitsize::dqword-1, 0, ZMM12, 0,                         0, XMM12, false) // xmm12
REG_SPEC(XMM13, xmm13, triton::bitsize::dqword-1, 0, ZMM13, 0,                         0, XMM13, false) // xmm13
REG_SPEC(XMM14, xmm14, triton::bitsize::dqword-1, 0, ZMM14, 0,                         0, XMM14, false) // xmm14
REG_SPEC(XMM15, xmm15, triton::bitsize::dqword-1, 0, ZMM15, 0,                         0, XMM15, false) // xmm15

/* AVX-256 */

REG_SPEC(YMM0,  ymm0,  triton::bitsize::qqword-1, 0, ZMM0,  triton::bitsize::qqword-1, 0, YMM0,  true)  // ymm0
REG_SPEC(YMM1,  ymm1,  triton::bitsize::qqword-1, 0, ZMM1,  triton::bitsize::qqword-1, 0, YMM1,  true)  // ymm1
REG_SPEC(YMM2,  ymm2,  triton::bitsize::qqword-1, 0, ZMM2,  triton::bitsize::qqword-1, 0, YMM2,  true)  // ymm2
REG_SPEC(YMM3,  ymm3,  triton::bitsize::qqword-1, 0, ZMM3,  triton::bitsize::qqword-1, 0, YMM3,  true)  // ymm3
REG_SPEC(YMM4,  ymm4,  triton::bitsize::qqword-1, 0, ZMM4,  triton::bitsize::qqword-1, 0, YMM4,  true)  // ymm4
REG_SPEC(YMM5,  ymm5,  triton::bitsize::qqword-1, 0, ZMM5,  triton::bitsize::qqword-1, 0, YMM5,  true)  // ymm5
REG_SPEC(YMM6,  ymm6,  triton::bitsize::qqword-1, 0, ZMM6,  triton::bitsize::qqword-1, 0, YMM6,  true)  // ymm6
REG_SPEC(YMM7,  ymm7,  triton::bitsize::qqword-1, 0, ZMM7,  triton::bitsize::qqword-1, 0, YMM7,  true)  // ymm7
REG_SPEC(YMM8,  ymm8,  triton::bitsize::qqword-1, 0, ZMM8,  0,                         0, YMM8,  false) // ymm8
REG_SPEC(YMM9,  ymm9,  triton::bitsize::qqword-1, 0, ZMM9,  0,                         0, YMM9,  false) // ymm9
REG_SPEC(YMM10, ymm10, triton::bitsize::qqword-1, 0, ZMM10, 0,                         0, YMM10, false) // ymm10
REG_SPEC(YMM11, ymm11, triton::bitsize::qqword-1, 0, ZMM11, 0,                         0, YMM11, false) // ymm11
REG_SPEC(YMM12, ymm12, triton::bitsize::qqword-1, 0, ZMM12, 0,                         0, YMM12, false) // ymm12
REG_SPEC(YMM13, ymm13, triton::bitsize::qqword-1, 0, ZMM13, 0,                         0, YMM13, false) // ymm13
REG_SPEC(YMM14, ymm14, triton::bitsize::qqword-1, 0, ZMM14, 0,                         0, YMM14, false) // ymm14
REG_SPEC(YMM15, ymm15, triton::bitsize::qqword-1, 0, ZMM15, 0,                         0, YMM15, false) // ymm15

/* AVX-512 */

REG_SPEC(ZMM0,  zmm0,  triton::bitsize::dqqword-1, 0, ZMM0,  0, 0, ZMM0,  false)  // zmm0
REG_SPEC(ZMM1,  zmm1,  triton::bitsize::dqqword-1, 0, ZMM1,  0, 0, ZMM1,  false)  // zmm1
REG_SPEC(ZMM2,  zmm2,  triton::bitsize::dqqword-1, 0, ZMM2,  0, 0, ZMM2,  false)  // zmm2
REG_SPEC(ZMM3,  zmm3,  triton::bitsize::dqqword-1, 0, ZMM3,  0, 0, ZMM3,  false)  // zmm3
REG_SPEC(ZMM4,  zmm4,  triton::bitsize::dqqword-1, 0, ZMM4,  0, 0, ZMM4,  false)  // zmm4
REG_SPEC(ZMM5,  zmm5,  triton::bitsize::dqqword-1, 0, ZMM5,  0, 0, ZMM5,  false)  // zmm5
REG_SPEC(ZMM6,  zmm6,  triton::bitsize::dqqword-1, 0, ZMM6,  0, 0, ZMM6,  false)  // zmm6
REG_SPEC(ZMM7,  zmm7,  triton::bitsize::dqqword-1, 0, ZMM7,  0, 0, ZMM7,  false)  // zmm7
REG_SPEC(ZMM8,  zmm8,  triton::bitsize::dqqword-1, 0, ZMM8,  0, 0, ZMM8,  false)  // zmm8
REG_SPEC(ZMM9,  zmm9,  triton::bitsize::dqqword-1, 0, ZMM9,  0, 0, ZMM9,  false)  // zmm9
REG_SPEC(ZMM10, zmm10, triton::bitsize::dqqword-1, 0, ZMM10, 0, 0, ZMM10, false)  // zmm10
REG_SPEC(ZMM11, zmm11, triton::bitsize::dqqword-1, 0, ZMM11, 0, 0, ZMM11, false)  // zmm11
REG_SPEC(ZMM12, zmm12, triton::bitsize::dqqword-1, 0, ZMM12, 0, 0, ZMM12, false)  // zmm12
REG_SPEC(ZMM13, zmm13, triton::bitsize::dqqword-1, 0, ZMM13, 0, 0, ZMM13, false)  // zmm13
REG_SPEC(ZMM14, zmm14, triton::bitsize::dqqword-1, 0, ZMM14, 0, 0, ZMM14, false)  // zmm14
REG_SPEC(ZMM15, zmm15, triton::bitsize::dqqword-1, 0, ZMM15, 0, 0, ZMM15, false)  // zmm15
REG_SPEC(ZMM16, zmm16, triton::bitsize::dqqword-1, 0, ZMM16, 0, 0, ZMM16, false)  // zmm16
REG_SPEC(ZMM17, zmm17, triton::bitsize::dqqword-1, 0, ZMM17, 0, 0, ZMM17, false)  // zmm17
REG_SPEC(ZMM18, zmm18, triton::bitsize::dqqword-1, 0, ZMM18, 0, 0, ZMM18, false)  // zmm18
REG_SPEC(ZMM19, zmm19, triton::bitsize::dqqword-1, 0, ZMM19, 0, 0, ZMM19, false)  // zmm19
REG_SPEC(ZMM20, zmm20, triton::bitsize::dqqword-1, 0, ZMM20, 0, 0, ZMM20, false)  // zmm20
REG_SPEC(ZMM21, zmm21, triton::bitsize::dqqword-1, 0, ZMM21, 0, 0, ZMM21, false)  // zmm21
REG_SPEC(ZMM22, zmm22, triton::bitsize::dqqword-1, 0, ZMM22, 0, 0, ZMM22, false)  // zmm22
REG_SPEC(ZMM23, zmm23, triton::bitsize::dqqword-1, 0, ZMM23, 0, 0, ZMM23, false)  // zmm23
REG_SPEC(ZMM24, zmm24, triton::bitsize::dqqword-1, 0, ZMM24, 0, 0, ZMM24, false)  // zmm24
REG_SPEC(ZMM25, zmm25, triton::bitsize::dqqword-1, 0, ZMM25, 0, 0, ZMM25, false)  // zmm25
REG_SPEC(ZMM26, zmm26, triton::bitsize::dqqword-1, 0, ZMM26, 0, 0, ZMM26, false)  // zmm26
REG_SPEC(ZMM27, zmm27, triton::bitsize::dqqword-1, 0, ZMM27, 0, 0, ZMM27, false)  // zmm27
REG_SPEC(ZMM28, zmm28, triton::bitsize::dqqword-1, 0, ZMM28, 0, 0, ZMM28, false)  // zmm28
REG_SPEC(ZMM29, zmm29, triton::bitsize::dqqword-1, 0, ZMM29, 0, 0, ZMM29, false)  // zmm29
REG_SPEC(ZMM30, zmm30, triton::bitsize::dqqword-1, 0, ZMM30, 0, 0, ZMM30, false)  // zmm30
REG_SPEC(ZMM31, zmm31, triton::bitsize::dqqword-1, 0, ZMM31, 0, 0, ZMM31, false)  // zmm31

/* Control */

REG_SPEC(CR0,  cr0,  triton::bitsize::qword-1, 0, CR0,  triton::bitsize::dword-1, 0, CR0,  true)  // cr0
REG_SPEC(CR1,  cr1,  triton::bitsize::qword-1, 0, CR1,  triton::bitsize::dword-1, 0, CR1,  true)  // cr1
REG_SPEC(CR2,  cr2,  triton::bitsize::qword-1, 0, CR2,  triton::bitsize::dword-1, 0, CR2,  true)  // cr2
REG_SPEC(CR3,  cr3,  triton::bitsize::qword-1, 0, CR3,  triton::bitsize::dword-1, 0, CR3,  true)  // cr3
REG_SPEC(CR4,  cr4,  triton::bitsize::qword-1, 0, CR4,  triton::bitsize::dword-1, 0, CR4,  true)  // cr4
REG_SPEC(CR5,  cr5,  triton::bitsize::qword-1, 0, CR5,  triton::bitsize::dword-1, 0, CR5,  true)  // cr5
REG_SPEC(CR6,  cr6,  triton::bitsize::qword-1, 0, CR6,  triton::bitsize::dword-1, 0, CR6,  true)  // cr6
REG_SPEC(CR7,  cr7,  triton::bitsize::qword-1, 0, CR7,  triton::bitsize::dword-1, 0, CR7,  true)  // cr7
REG_SPEC(CR8,  cr8,  triton::bitsize::qword-1, 0, CR8,  triton::bitsize::dword-1, 0, CR8,  true)  // cr8
REG_SPEC(CR9,  cr9,  triton::bitsize::qword-1, 0, CR9,  triton::bitsize::dword-1, 0, CR9,  true)  // cr9
REG_SPEC(CR10, cr10, triton::bitsize::qword-1, 0, CR10, triton::bitsize::dword-1, 0, CR10, true)  // cr10
REG_SPEC(CR11, cr11, triton::bitsize::qword-1, 0, CR11, triton::bitsize::dword-1, 0, CR11, true)  // cr11
REG_SPEC(CR12, cr12, triton::bitsize::qword-1, 0, CR12, triton::bitsize::dword-1, 0, CR12, true)  // cr12
REG_SPEC(CR13, cr13, triton::bitsize::qword-1, 0, CR13, triton::bitsize::dword-1, 0, CR13, true)  // cr13
REG_SPEC(CR14, cr14, triton::bitsize::qword-1, 0, CR14, triton::bitsize::dword-1, 0, CR14, true)  // cr14
REG_SPEC(CR15, cr15, triton::bitsize::qword-1, 0, CR15, triton::bitsize::dword-1, 0, CR15, true)  // cr15

/* Debug */

REG_SPEC(DR0,  dr0,  triton::bitsize::qword-1, 0, DR0,  triton::bitsize::dword-1, 0, DR0,  true)  // dr0
REG_SPEC(DR1,  dr1,  triton::bitsize::qword-1, 0, DR1,  triton::bitsize::dword-1, 0, DR1,  true)  // dr1
REG_SPEC(DR2,  dr2,  triton::bitsize::qword-1, 0, DR2,  triton::bitsize::dword-1, 0, DR2,  true)  // dr2
REG_SPEC(DR3,  dr3,  triton::bitsize::qword-1, 0, DR3,  triton::bitsize::dword-1, 0, DR3,  true)  // dr3
REG_SPEC(DR6,  dr6,  triton::bitsize::qword-1, 0, DR6,  triton::bitsize::dword-1, 0, DR6,  true)  // dr6
REG_SPEC(DR7,  dr7,  triton::bitsize::qword-1, 0, DR7,  triton::bitsize::dword-1, 0, DR7,  true)  // dr7

/* Flags ID used in the Taint and Symbolic Engines */

REG_SPEC_NO_CAPSTONE(AC,  ac,  0, 0, AC,  0, 0, AC,  true)  // ac
REG_SPEC_NO_CAPSTONE(AF,  af,  0, 0, AF,  0, 0, AF,  true)  // af
REG_SPEC_NO_CAPSTONE(CF,  cf,  0, 0, CF,  0, 0, CF,  true)  // cf
REG_SPEC_NO_CAPSTONE(DF,  df,  0, 0, DF,  0, 0, DF,  true)  // df
REG_SPEC_NO_CAPSTONE(ID,  id,  0, 0, ID,  0, 0, ID,  true)  // id
REG_SPEC_NO_CAPSTONE(IF,  if,  0, 0, IF,  0, 0, IF,  true)  // if
REG_SPEC_NO_CAPSTONE(NT,  nt,  0, 0, NT,  0, 0, NT,  true)  // nt
REG_SPEC_NO_CAPSTONE(OF,  of,  0, 0, OF,  0, 0, OF,  true)  // of
REG_SPEC_NO_CAPSTONE(PF,  pf,  0, 0, PF,  0, 0, PF,  true)  // pf
REG_SPEC_NO_CAPSTONE(RF,  rf,  0, 0, RF,  0, 0, RF,  true)  // rf
REG_SPEC_NO_CAPSTONE(SF,  sf,  0, 0, SF,  0, 0, SF,  true)  // sf
REG_SPEC_NO_CAPSTONE(TF,  tf,  0, 0, TF,  0, 0, TF,  true)  // tf
REG_SPEC_NO_CAPSTONE(VIF, vif, 0, 0, VIF, 0, 0, VIF, true)  // vif
REG_SPEC_NO_CAPSTONE(VIP, vip, 0, 0, VIP, 0, 0, VIP, true)  // vip
REG_SPEC_NO_CAPSTONE(VM,  vm,  0, 0, VM,  0, 0, VM,  true)  // vm
REG_SPEC_NO_CAPSTONE(ZF,  zf,  0, 0, ZF,  0, 0, ZF,  true)  // zf

/* SSE flags */

REG_SPEC_NO_CAPSTONE(SSE_IE,  sse_ie,  0, 0, SSE_IE,  0, 0, SSE_IE,  true)  // ie (Invalid Operation Flag)
REG_SPEC_NO_CAPSTONE(SSE_DE,  sse_de,  0, 0, SSE_DE,  0, 0, SSE_DE,  true)  // de (Denormal Flag)
REG_SPEC_NO_CAPSTONE(SSE_ZE,  sse_ze,  0, 0, SSE_ZE,  0, 0, SSE_ZE,  true)  // ze (Divide By Zero Flag)
REG_SPEC_NO_CAPSTONE(SSE_OE,  sse_oe,  0, 0, SSE_OE,  0, 0, SSE_OE,  true)  // oe (Overflow Flag)
REG_SPEC_NO_CAPSTONE(SSE_UE,  sse_ue,  0, 0, SSE_UE,  0, 0, SSE_UE,  true)  // ue (Underflow Flag)
REG_SPEC_NO_CAPSTONE(SSE_PE,  sse_pe,  0, 0, SSE_PE,  0, 0, SSE_PE,  true)  // pe (Precision Flag)
REG_SPEC_NO_CAPSTONE(SSE_DAZ, sse_daz, 0, 0, SSE_DAZ, 0, 0, SSE_DAZ, true)  // daz (Invalid Operation Flag)
REG_SPEC_NO_CAPSTONE(SSE_IM,  sse_im,  0, 0, SSE_IM,  0, 0, SSE_IM,  true)  // im (Invalid Operation Mask)
REG_SPEC_NO_CAPSTONE(SSE_DM,  sse_dm,  0, 0, SSE_DM,  0, 0, SSE_DM,  true)  // dm (Denormal Mask)
REG_SPEC_NO_CAPSTONE(SSE_ZM,  sse_zm,  0, 0, SSE_ZM,  0, 0, SSE_ZM,  true)  // zm (Divide By Zero Mask)
REG_SPEC_NO_CAPSTONE(SSE_OM,  sse_om,  0, 0, SSE_OM,  0, 0, SSE_OM,  true)  // om (Overflow Mask)
REG_SPEC_NO_CAPSTONE(SSE_UM,  sse_um,  0, 0, SSE_UM,  0, 0, SSE_UM,  true)  // um (Underflow Mask)
REG_SPEC_NO_CAPSTONE(SSE_PM,  sse_pm,  0, 0, SSE_PM,  0, 0, SSE_PM,  true)  // pm (Precision Mask)
REG_SPEC_NO_CAPSTONE(SSE_RL,  sse_rl,  0, 0, SSE_RL,  0, 0, SSE_RL,  true)  // rl (Round Negative)
REG_SPEC_NO_CAPSTONE(SSE_RH,  sse_rh,  0, 0, SSE_RH,  0, 0, SSE_RH,  true)  // rh (Round Positive)
REG_SPEC_NO_CAPSTONE(SSE_FZ,  sse_fz,  0, 0, SSE_FZ,  0, 0, SSE_FZ,  true)  // fz (Flush To Zero)

/* FPU flags */

REG_SPEC_NO_CAPSTONE(FCW_IM,  fcw_im,  0, 0, FCW_IM,  0, 0, FCW_IM,  true)  // im (Invalid Operation Mask)
REG_SPEC_NO_CAPSTONE(FCW_DM,  fcw_dm,  0, 0, FCW_DM,  0, 0, FCW_DM,  true)  // dm (Denormal Mask)
REG_SPEC_NO_CAPSTONE(FCW_ZM,  fcw_zm,  0, 0, FCW_ZM,  0, 0, FCW_ZM,  true)  // zm (Divide By Zero Mask)
REG_SPEC_NO_CAPSTONE(FCW_OM,  fcw_om,  0, 0, FCW_OM,  0, 0, FCW_OM,  true)  // om (Overflow Mask)
REG_SPEC_NO_CAPSTONE(FCW_UM,  fcw_um,  0, 0, FCW_UM,  0, 0, FCW_UM,  true)  // um (Underflow Mask)
REG_SPEC_NO_CAPSTONE(FCW_PM,  fcw_pm,  0, 0, FCW_PM,  0, 0, FCW_PM,  true)  // pm (Precision Mask)
REG_SPEC_NO_CAPSTONE(FCW_PC,  fcw_pc,  1, 0, FCW_PC,  1, 0, FCW_PC,  true)  // pc (Precision Control)
REG_SPEC_NO_CAPSTONE(FCW_RC,  fcw_rc,  1, 0, FCW_RC,  1, 0, FCW_RC,  true)  // rc (Rounding Control)
REG_SPEC_NO_CAPSTONE(FCW_X,   fcw_x,   0, 0, FCW_X,   0, 0, FCW_X,   true)  // x  (Infinity Control)

REG_SPEC_NO_CAPSTONE(FSW_IE,  fsw_ie,  0, 0, FSW_IE,  0, 0, FSW_IE,  true)  // ie (Invalid Operation Mask)
REG_SPEC_NO_CAPSTONE(FSW_DE,  fsw_de,  0, 0, FSW_DE,  0, 0, FSW_DE,  true)  // de (Denormal Mask)
REG_SPEC_NO_CAPSTONE(FSW_ZE,  fsw_ze,  0, 0, FSW_ZE,  0, 0, FSW_ZE,  true)  // ze (Divide By Zero Mask)
REG_SPEC_NO_CAPSTONE(FSW_OE,  fsw_oe,  0, 0, FSW_OE,  0, 0, FSW_OE,  true)  // oe (Overflow Mask)
REG_SPEC_NO_CAPSTONE(FSW_UE,  fsw_ue,  0, 0, FSW_UE,  0, 0, FSW_UE,  true)  // ue (Underflow Mask)
REG_SPEC_NO_CAPSTONE(FSW_PE,  fsw_pe,  0, 0, FSW_PE,  0, 0, FSW_PE,  true)  // pe (Precision Mask)
REG_SPEC_NO_CAPSTONE(FSW_SF,  fsw_sf,  0, 0, FSW_SF,  0, 0, FSW_SF,  true)  // sf (Stack Fault)
REG_SPEC_NO_CAPSTONE(FSW_ES,  fsw_es,  0, 0, FSW_ES,  0, 0, FSW_ES,  true)  // ef (Error Summary Status)
REG_SPEC_NO_CAPSTONE(FSW_C0,  fsw_c0,  0, 0, FSW_C0,  0, 0, FSW_C0,  true)  // c0 (Condition Code 0)
REG_SPEC_NO_CAPSTONE(FSW_C1,  fsw_c1,  0, 0, FSW_C1,  0, 0, FSW_C1,  true)  // c1 (Condition Code 1)
REG_SPEC_NO_CAPSTONE(FSW_C2,  fsw_c2,  0, 0, FSW_C2,  0, 0, FSW_C2,  true)  // c2 (Condition Code 2)
REG_SPEC_NO_CAPSTONE(FSW_TOP, fsw_top, 2, 0, FSW_TOP, 2, 0, FSW_TOP, true)  // top (Top of Stack Pointer)
REG_SPEC_NO_CAPSTONE(FSW_C3,  fsw_c3,  0, 0, FSW_C3,  0, 0, FSW_C3,  true)  // c3 (Condition Code 3)
REG_SPEC_NO_CAPSTONE(FSW_B,   fsw_b,   0, 0, FSW_B,   0, 0, FSW_B,   true)  // b (FPU Busy)

/* EFER */

REG_SPEC_NO_CAPSTONE(EFER, efer, triton::bitsize::qword-1, 0, EFER, triton::bitsize::qword-1, 0, EFER, true) // efer

REG_SPEC_NO_CAPSTONE(EFER_TCE,   efer_tce,   0, 0, EFER_TCE,   0, 0, EFER_TCE,   true) // efer_tce
REG_SPEC_NO_CAPSTONE(EFER_FFXSR, efer_ffxsr, 0, 0, EFER_FFXSR, 0, 0, EFER_FFXSR, true) // efer_ffxsr
REG_SPEC_NO_CAPSTONE(EFER_LMSLE, efer_lmsle, 0, 0, EFER_LMSLE, 0, 0, EFER_LMSLE, true) // efer_lmsle
REG_SPEC_NO_CAPSTONE(EFER_SVME,  efer_svme,  0, 0, EFER_SVME,  0, 0, EFER_SVME,  true) // efer_svme
REG_SPEC_NO_CAPSTONE(EFER_NXE,   efer_nxe,   0, 0, EFER_NXE,   0, 0, EFER_NXE,   true) // efer_nxe
REG_SPEC_NO_CAPSTONE(EFER_LMA,   efer_lma,   0, 0, EFER_LMA,   0, 0, EFER_LMA,   true) // efer_lma
REG_SPEC_NO_CAPSTONE(EFER_LME,   efer_lme,   0, 0, EFER_LME,   0, 0, EFER_LME,   true) // efer_lme
REG_SPEC_NO_CAPSTONE(EFER_SCE,   efer_sce,   0, 0, EFER_SCE,   0, 0, EFER_SCE,   true) // efer_sce

/* Segments */

REG_SPEC(CS, cs, triton::bitsize::qword-1, 0, CS, triton::bitsize::dword-1, 0, CS, true) // Code Segment
REG_SPEC(DS, ds, triton::bitsize::qword-1, 0, DS, triton::bitsize::dword-1, 0, DS, true) // Data Segment
REG_SPEC(ES, es, triton::bitsize::qword-1, 0, ES, triton::bitsize::dword-1, 0, ES, true) // Extra Segment
REG_SPEC(FS, fs, triton::bitsize::qword-1, 0, FS, triton::bitsize::dword-1, 0, FS, true) // FS Segment
REG_SPEC(GS, gs, triton::bitsize::qword-1, 0, GS, triton::bitsize::dword-1, 0, GS, true) // GS Segment
REG_SPEC(SS, ss, triton::bitsize::qword-1, 0, SS, triton::bitsize::dword-1, 0, SS, true) // Stack Segment

#undef REG_SPEC
#undef REG_SPEC_NO_CAPSTONE

#pragma warning(default:4067)
