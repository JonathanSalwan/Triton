#pragma warning(disable:4067)

#if not (defined REG_SPEC || defined REG_SPEC_NO_CAPSTONE)
#error REG_SPEC have to be specified before including specs
#endif

// REG_SPEC(UPPER_NAME, LOWER_NAME, X86_64_UPPER, X84_84_LOWER, x86_64_PARENT, X86_UPPER, X86_LOWER, X86_PARENT, X86_AVAIL)

/* GPR 64-bits. */
REG_SPEC(RAX, rax, QWORD_SIZE_BIT-1, 0, RAX, 0, 0, RAX, false) //!< rax
REG_SPEC(RBX, rbx, QWORD_SIZE_BIT-1, 0, RBX, 0, 0, RBX, false) //!< rbx
REG_SPEC(RCX, rcx, QWORD_SIZE_BIT-1, 0, RCX, 0, 0, RCX, false) //!< rcx
REG_SPEC(RDX, rdx, QWORD_SIZE_BIT-1, 0, RDX, 0, 0, RDX, false) //!< rdx
REG_SPEC(RDI, rdi, QWORD_SIZE_BIT-1, 0, RDI, 0, 0, RDI, false) //!< rdi
REG_SPEC(RSI, rsi, QWORD_SIZE_BIT-1, 0, RSI, 0, 0, RSI, false) //!< rsi
REG_SPEC(RBP, rbp, QWORD_SIZE_BIT-1, 0, RBP, 0, 0, RBP, false) //!< rbp
REG_SPEC(RSP, rsp, QWORD_SIZE_BIT-1, 0, RSP, 0, 0, RSP, false) //!< rsp
REG_SPEC(RIP, rip, QWORD_SIZE_BIT-1, 0, RIP, 0, 0, RIP, false) //!< rip

REG_SPEC(R8, r8, QWORD_SIZE_BIT-1, 0, R8, 0, 0, R8, false)    //!< r8
REG_SPEC(R8D, r8d, DWORD_SIZE_BIT-1, 0, R8, 0, 0, R8, false)  //!< r8d
REG_SPEC(R8W, r8w, WORD_SIZE_BIT-1, 0, R8, 0, 0, R8, false)   //!< r8w
REG_SPEC(R8B, r8b, BYTE_SIZE_BIT-1, 0, R8, 0, 0, R8, false)   //!< r8b

REG_SPEC(R9, r9, QWORD_SIZE_BIT-1, 0, R9, 0, 0, R9, false)    //!< r9
REG_SPEC(R9D, r9d, DWORD_SIZE_BIT-1, 0, R9, 0, 0, R9, false)  //!< r9d
REG_SPEC(R9W, r9w, WORD_SIZE_BIT-1, 0, R9, 0, 0, R9, false)   //!< r9w
REG_SPEC(R9B, r9b, BYTE_SIZE_BIT-1, 0, R9, 0, 0, R9, false)   //!< r9b

REG_SPEC(R10, r10, QWORD_SIZE_BIT-1, 0, R10, 0, 0, R10, false)    //!< r10
REG_SPEC(R10D, r10d, DWORD_SIZE_BIT-1, 0, R10, 0, 0, R10, false)  //!< r10d
REG_SPEC(R10W, r10w, WORD_SIZE_BIT-1, 0, R10, 0, 0, R10, false)   //!< r10w
REG_SPEC(R10B, r10b, BYTE_SIZE_BIT-1, 0, R10, 0, 0, R10, false)   //!< r10b

REG_SPEC(R11, r11, QWORD_SIZE_BIT-1, 0, R11, 0, 0, R11, false)    //!< r11
REG_SPEC(R11D, r11d, DWORD_SIZE_BIT-1, 0, R11, 0, 0, R11, false)  //!< r11d
REG_SPEC(R11W, r11w, WORD_SIZE_BIT-1, 0, R11, 0, 0, R11, false)   //!< r11w
REG_SPEC(R11B, r11b, BYTE_SIZE_BIT-1, 0, R11, 0, 0, R11, false)   //!< r11b

REG_SPEC(R12, r12, QWORD_SIZE_BIT-1, 0, R12, 0, 0, R12, false)    //!< r12
REG_SPEC(R12D, r12d, DWORD_SIZE_BIT-1, 0, R12, 0, 0, R12, false)  //!< r12d
REG_SPEC(R12W, r12w, WORD_SIZE_BIT-1, 0, R12, 0, 0, R12, false)   //!< r12w
REG_SPEC(R12B, r12b, BYTE_SIZE_BIT-1, 0, R12, 0, 0, R12, false)   //!< r12b

REG_SPEC(R13, r13, QWORD_SIZE_BIT-1, 0, R13, 0, 0, R13, false)    //!< r13
REG_SPEC(R13D, r13d, DWORD_SIZE_BIT-1, 0, R13, 0, 0, R13, false)  //!< r13d
REG_SPEC(R13W, r13w, WORD_SIZE_BIT-1, 0, R13, 0, 0, R13, false)   //!< r13w
REG_SPEC(R13B, r13b, BYTE_SIZE_BIT-1, 0, R13, 0, 0, R13, false)   //!< r13b

REG_SPEC(R14, r14, QWORD_SIZE_BIT-1, 0, R14, 0, 0, R14, false)    //!< r14
REG_SPEC(R14D, r14d, DWORD_SIZE_BIT-1, 0, R14, 0, 0, R14, false)  //!< r14d
REG_SPEC(R14W, r14w, WORD_SIZE_BIT-1, 0, R14, 0, 0, R14, false)   //!< r14w
REG_SPEC(R14B, r14b, BYTE_SIZE_BIT-1, 0, R14, 0, 0, R14, false)   //!< r14b

REG_SPEC(R15, r15, QWORD_SIZE_BIT-1, 0, R15, 0, 0, R15, false)    //!< r15
REG_SPEC(R15D, r15d, DWORD_SIZE_BIT-1, 0, R15, 0, 0, R15, false)  //!< r15d
REG_SPEC(R15W, r15w, WORD_SIZE_BIT-1, 0, R15, 0, 0, R15, false)   //!< r15w
REG_SPEC(R15B, r15b, BYTE_SIZE_BIT-1, 0, R15, 0, 0, R15, false)   //!< r15b

/* GPR 32-bits */
REG_SPEC(EAX, eax, DWORD_SIZE_BIT-1, 0, RAX, DWORD_SIZE_BIT-1, 0, EAX, true)                      //!< eax
REG_SPEC(AX, ax, WORD_SIZE_BIT-1, 0, RAX, WORD_SIZE_BIT-1, 0, EAX, true)                          //!< ax
REG_SPEC(AH, ah, WORD_SIZE_BIT-1, BYTE_SIZE_BIT, RAX, WORD_SIZE_BIT-1, BYTE_SIZE_BIT, EAX, true)  //!< ah
REG_SPEC(AL, al, BYTE_SIZE_BIT-1, 0, RAX, BYTE_SIZE_BIT-1, 0, EAX, true)                          //!< al

REG_SPEC(EBX, ebx, DWORD_SIZE_BIT-1, 0, RBX, DWORD_SIZE_BIT-1, 0, EBX, true)                      //!< ebx
REG_SPEC(BX, bx, WORD_SIZE_BIT-1, 0, RBX, WORD_SIZE_BIT-1, 0, EBX, true)                          //!< bx
REG_SPEC(BH, bh, WORD_SIZE_BIT-1, BYTE_SIZE_BIT, RBX, WORD_SIZE_BIT-1, BYTE_SIZE_BIT, EBX, true)  //!< bh
REG_SPEC(BL, bl, BYTE_SIZE_BIT-1, 0, RBX, BYTE_SIZE_BIT-1, 0, EBX, true)                          //!< bl

REG_SPEC(ECX, ecx, DWORD_SIZE_BIT-1, 0, RCX, DWORD_SIZE_BIT-1, 0, ECX, true)                      //!< ecx
REG_SPEC(CX, cx, WORD_SIZE_BIT-1, 0, RCX, WORD_SIZE_BIT-1, 0, ECX, true)                          //!< cx
REG_SPEC(CH, ch, WORD_SIZE_BIT-1, BYTE_SIZE_BIT, RCX, WORD_SIZE_BIT-1, BYTE_SIZE_BIT, ECX, true)  //!< ch
REG_SPEC(CL, cl, BYTE_SIZE_BIT-1, 0, RCX, BYTE_SIZE_BIT-1, 0, ECX, true)                          //!< cl

REG_SPEC(EDX, edx, DWORD_SIZE_BIT-1, 0, RDX, DWORD_SIZE_BIT-1, 0, EDX, true)                      //!< edx
REG_SPEC(DX, dx, WORD_SIZE_BIT-1, 0, RDX, WORD_SIZE_BIT-1, 0, EDX, true)                          //!< dx
REG_SPEC(DH, dh, WORD_SIZE_BIT-1, BYTE_SIZE_BIT, RDX, WORD_SIZE_BIT-1, BYTE_SIZE_BIT, EDX, true)  //!< dh
REG_SPEC(DL, dl, BYTE_SIZE_BIT-1, 0, RDX, BYTE_SIZE_BIT-1, 0, EDX, true)                          //!< dl

REG_SPEC(EDI, edi, DWORD_SIZE_BIT-1, 0, RDI, DWORD_SIZE_BIT-1, 0, EDI, true)  //!< edi
REG_SPEC(DI, di, WORD_SIZE_BIT-1, 0, RDI, WORD_SIZE_BIT-1, 0, EDI, true)      //!< di
REG_SPEC(DIL, dil, BYTE_SIZE_BIT-1, 0, RDI, BYTE_SIZE_BIT-1, 0, EDI, true)    //!< dil

REG_SPEC(ESI, esi, DWORD_SIZE_BIT-1, 0, RSI, DWORD_SIZE_BIT-1, 0, ESI, true)  //!< esi
REG_SPEC(SI, si, WORD_SIZE_BIT-1, 0, RSI, WORD_SIZE_BIT-1, 0, ESI, true)      //!< si
REG_SPEC(SIL, sil, BYTE_SIZE_BIT-1, 0, RSI, BYTE_SIZE_BIT-1, 0, ESI, true)    //!< sil

REG_SPEC(EBP, ebp, DWORD_SIZE_BIT-1, 0, RBP, DWORD_SIZE_BIT-1, 0, EBP, true)  //!< ebp
REG_SPEC(BP, bp, WORD_SIZE_BIT-1, 0, RBP, WORD_SIZE_BIT-1, 0, EBP, true)      //!< bp
REG_SPEC(BPL, bpl, BYTE_SIZE_BIT-1, 0, RBP, BYTE_SIZE_BIT-1, 0, EBP, true)    //!< bpl

REG_SPEC(ESP, esp, DWORD_SIZE_BIT-1, 0, RSP, DWORD_SIZE_BIT-1, 0, ESP, true)  //!< esp
REG_SPEC(SP, sp, WORD_SIZE_BIT-1, 0, RSP, WORD_SIZE_BIT-1, 0, ESP, true)      //!< sp
REG_SPEC(SPL, spl, BYTE_SIZE_BIT-1, 0, RSP, BYTE_SIZE_BIT-1, 0, ESP, true)    //!< spl

REG_SPEC(EIP, eip, DWORD_SIZE_BIT-1, 0, RIP, DWORD_SIZE_BIT-1, 0, EIP, true)  //!< eip
REG_SPEC(IP, ip, WORD_SIZE_BIT-1, 0, RIP, WORD_SIZE_BIT-1, 0, EIP, true)      //!< ip

REG_SPEC(EFLAGS, eflags, QWORD_SIZE_BIT-1, 0, EFLAGS, DWORD_SIZE_BIT-1, 0, EFLAGS, true) //!< eflags

/* MMX */
REG_SPEC(MM0, mm0, QWORD_SIZE_BIT-1, 0, MM0, QWORD_SIZE_BIT-1, 0, MM0, true) //!< mm0
REG_SPEC(MM1, mm1, QWORD_SIZE_BIT-1, 0, MM1, QWORD_SIZE_BIT-1, 0, MM1, true) //!< mm1
REG_SPEC(MM2, mm2, QWORD_SIZE_BIT-1, 0, MM2, QWORD_SIZE_BIT-1, 0, MM2, true) //!< mm2
REG_SPEC(MM3, mm3, QWORD_SIZE_BIT-1, 0, MM3, QWORD_SIZE_BIT-1, 0, MM3, true) //!< mm3
REG_SPEC(MM4, mm4, QWORD_SIZE_BIT-1, 0, MM4, QWORD_SIZE_BIT-1, 0, MM4, true) //!< mm4
REG_SPEC(MM5, mm5, QWORD_SIZE_BIT-1, 0, MM5, QWORD_SIZE_BIT-1, 0, MM5, true) //!< mm5
REG_SPEC(MM6, mm6, QWORD_SIZE_BIT-1, 0, MM6, QWORD_SIZE_BIT-1, 0, MM6, true) //!< mm6
REG_SPEC(MM7, mm7, QWORD_SIZE_BIT-1, 0, MM7, QWORD_SIZE_BIT-1, 0, MM7, true) //!< mm7

/* SSE */
REG_SPEC_NO_CAPSTONE(MXCSR, mxcsr, QWORD_SIZE_BIT-1, 0, MXCSR, DWORD_SIZE_BIT-1, 0, MXCSR, true) //!< mxcsr

REG_SPEC(XMM0, xmm0, DQWORD_SIZE_BIT-1, 0, XMM0, DQWORD_SIZE_BIT-1, 0, XMM0, true)      //!< xmm0
REG_SPEC(XMM1, xmm1, DQWORD_SIZE_BIT-1, 0, XMM1, DQWORD_SIZE_BIT-1, 0, XMM1, true)      //!< xmm1
REG_SPEC(XMM2, xmm2, DQWORD_SIZE_BIT-1, 0, XMM2, DQWORD_SIZE_BIT-1, 0, XMM2, true)      //!< xmm2
REG_SPEC(XMM3, xmm3, DQWORD_SIZE_BIT-1, 0, XMM3, DQWORD_SIZE_BIT-1, 0, XMM3, true)      //!< xmm3
REG_SPEC(XMM4, xmm4, DQWORD_SIZE_BIT-1, 0, XMM4, DQWORD_SIZE_BIT-1, 0, XMM4, true)      //!< xmm4
REG_SPEC(XMM5, xmm5, DQWORD_SIZE_BIT-1, 0, XMM5, DQWORD_SIZE_BIT-1, 0, XMM5, true)      //!< xmm5
REG_SPEC(XMM6, xmm6, DQWORD_SIZE_BIT-1, 0, XMM6, DQWORD_SIZE_BIT-1, 0, XMM6, true)      //!< xmm6
REG_SPEC(XMM7, xmm7, DQWORD_SIZE_BIT-1, 0, XMM7, DQWORD_SIZE_BIT-1, 0, XMM7, true)      //!< xmm7
REG_SPEC(XMM8, xmm8, DQWORD_SIZE_BIT-1, 0, XMM8, DQWORD_SIZE_BIT-1, 0, XMM8, false)     //!< xmm8
REG_SPEC(XMM9, xmm9, DQWORD_SIZE_BIT-1, 0, XMM9, DQWORD_SIZE_BIT-1, 0, XMM9, false)     //!< xmm9
REG_SPEC(XMM10, xmm10, DQWORD_SIZE_BIT-1, 0, XMM10, DQWORD_SIZE_BIT-1, 0, XMM10, false) //!< xmm10
REG_SPEC(XMM11, xmm11, DQWORD_SIZE_BIT-1, 0, XMM11, DQWORD_SIZE_BIT-1, 0, XMM11, false) //!< xmm11
REG_SPEC(XMM12, xmm12, DQWORD_SIZE_BIT-1, 0, XMM12, DQWORD_SIZE_BIT-1, 0, XMM12, false) //!< xmm12
REG_SPEC(XMM13, xmm13, DQWORD_SIZE_BIT-1, 0, XMM13, DQWORD_SIZE_BIT-1, 0, XMM13, false) //!< xmm13
REG_SPEC(XMM14, xmm14, DQWORD_SIZE_BIT-1, 0, XMM14, DQWORD_SIZE_BIT-1, 0, XMM14, false) //!< xmm14
REG_SPEC(XMM15, xmm15, DQWORD_SIZE_BIT-1, 0, XMM15, DQWORD_SIZE_BIT-1, 0, XMM15, false) //!< xmm15

/* AVX-256 */
REG_SPEC(YMM0, ymm0, QQWORD_SIZE_BIT-1, 0, YMM0, QQWORD_SIZE_BIT-1, 0, YMM0, true)      //!< ymm0
REG_SPEC(YMM1, ymm1, QQWORD_SIZE_BIT-1, 0, YMM1, QQWORD_SIZE_BIT-1, 0, YMM1, true)      //!< ymm1
REG_SPEC(YMM2, ymm2, QQWORD_SIZE_BIT-1, 0, YMM2, QQWORD_SIZE_BIT-1, 0, YMM2, true)      //!< ymm2
REG_SPEC(YMM3, ymm3, QQWORD_SIZE_BIT-1, 0, YMM3, QQWORD_SIZE_BIT-1, 0, YMM3, true)      //!< ymm3
REG_SPEC(YMM4, ymm4, QQWORD_SIZE_BIT-1, 0, YMM4, QQWORD_SIZE_BIT-1, 0, YMM4, true)      //!< ymm4
REG_SPEC(YMM5, ymm5, QQWORD_SIZE_BIT-1, 0, YMM5, QQWORD_SIZE_BIT-1, 0, YMM5, true)      //!< ymm5
REG_SPEC(YMM6, ymm6, QQWORD_SIZE_BIT-1, 0, YMM6, QQWORD_SIZE_BIT-1, 0, YMM6, true)      //!< ymm6
REG_SPEC(YMM7, ymm7, QQWORD_SIZE_BIT-1, 0, YMM7, QQWORD_SIZE_BIT-1, 0, YMM7, true)      //!< ymm7
REG_SPEC(YMM8, ymm8, QQWORD_SIZE_BIT-1, 0, YMM8, QQWORD_SIZE_BIT-1, 0, YMM8, false)     //!< ymm8
REG_SPEC(YMM9, ymm9, QQWORD_SIZE_BIT-1, 0, YMM9, QQWORD_SIZE_BIT-1, 0, YMM9, false)     //!< ymm9
REG_SPEC(YMM10, ymm10, QQWORD_SIZE_BIT-1, 0, YMM10, QQWORD_SIZE_BIT-1, 0, YMM10, false) //!< ymm10
REG_SPEC(YMM11, ymm11, QQWORD_SIZE_BIT-1, 0, YMM11, QQWORD_SIZE_BIT-1, 0, YMM11, false) //!< ymm11
REG_SPEC(YMM12, ymm12, QQWORD_SIZE_BIT-1, 0, YMM12, QQWORD_SIZE_BIT-1, 0, YMM12, false) //!< ymm12
REG_SPEC(YMM13, ymm13, QQWORD_SIZE_BIT-1, 0, YMM13, QQWORD_SIZE_BIT-1, 0, YMM13, false) //!< ymm13
REG_SPEC(YMM14, ymm14, QQWORD_SIZE_BIT-1, 0, YMM14, QQWORD_SIZE_BIT-1, 0, YMM14, false) //!< ymm14
REG_SPEC(YMM15, ymm15, QQWORD_SIZE_BIT-1, 0, YMM15, QQWORD_SIZE_BIT-1, 0, YMM15, false) //!< ymm15

/* AVX-512 */
REG_SPEC(ZMM0, zmm0, DQQWORD_SIZE_BIT-1, 0, ZMM0, 0, 0, ZMM0, false)      //!< zmm0
REG_SPEC(ZMM1, zmm1, DQQWORD_SIZE_BIT-1, 0, ZMM1, 0, 0, ZMM1, false)      //!< zmm1
REG_SPEC(ZMM2, zmm2, DQQWORD_SIZE_BIT-1, 0, ZMM2, 0, 0, ZMM2, false)      //!< zmm2
REG_SPEC(ZMM3, zmm3, DQQWORD_SIZE_BIT-1, 0, ZMM3, 0, 0, ZMM3, false)      //!< zmm3
REG_SPEC(ZMM4, zmm4, DQQWORD_SIZE_BIT-1, 0, ZMM4, 0, 0, ZMM4, false)      //!< zmm4
REG_SPEC(ZMM5, zmm5, DQQWORD_SIZE_BIT-1, 0, ZMM5, 0, 0, ZMM5, false)      //!< zmm5
REG_SPEC(ZMM6, zmm6, DQQWORD_SIZE_BIT-1, 0, ZMM6, 0, 0, ZMM6, false)      //!< zmm6
REG_SPEC(ZMM7, zmm7, DQQWORD_SIZE_BIT-1, 0, ZMM7, 0, 0, ZMM7, false)      //!< zmm7
REG_SPEC(ZMM8, zmm8, DQQWORD_SIZE_BIT-1, 0, ZMM8, 0, 0, ZMM8, false)      //!< zmm8
REG_SPEC(ZMM9, zmm9, DQQWORD_SIZE_BIT-1, 0, ZMM9, 0, 0, ZMM9, false)      //!< zmm9
REG_SPEC(ZMM10, zmm10, DQQWORD_SIZE_BIT-1, 0, ZMM10, 0, 0, ZMM10, false)  //!< zmm10
REG_SPEC(ZMM11, zmm11, DQQWORD_SIZE_BIT-1, 0, ZMM11, 0, 0, ZMM11, false)  //!< zmm11
REG_SPEC(ZMM12, zmm12, DQQWORD_SIZE_BIT-1, 0, ZMM12, 0, 0, ZMM12, false)  //!< zmm12
REG_SPEC(ZMM13, zmm13, DQQWORD_SIZE_BIT-1, 0, ZMM13, 0, 0, ZMM13, false)  //!< zmm13
REG_SPEC(ZMM14, zmm14, DQQWORD_SIZE_BIT-1, 0, ZMM14, 0, 0, ZMM14, false)  //!< zmm14
REG_SPEC(ZMM15, zmm15, DQQWORD_SIZE_BIT-1, 0, ZMM15, 0, 0, ZMM15, false)  //!< zmm15
REG_SPEC(ZMM16, zmm16, DQQWORD_SIZE_BIT-1, 0, ZMM16, 0, 0, ZMM16, false)  //!< zmm16
REG_SPEC(ZMM17, zmm17, DQQWORD_SIZE_BIT-1, 0, ZMM17, 0, 0, ZMM17, false)  //!< zmm17
REG_SPEC(ZMM18, zmm18, DQQWORD_SIZE_BIT-1, 0, ZMM18, 0, 0, ZMM18, false)  //!< zmm18
REG_SPEC(ZMM19, zmm19, DQQWORD_SIZE_BIT-1, 0, ZMM19, 0, 0, ZMM19, false)  //!< zmm19
REG_SPEC(ZMM20, zmm20, DQQWORD_SIZE_BIT-1, 0, ZMM20, 0, 0, ZMM20, false)  //!< zmm20
REG_SPEC(ZMM21, zmm21, DQQWORD_SIZE_BIT-1, 0, ZMM21, 0, 0, ZMM21, false)  //!< zmm21
REG_SPEC(ZMM22, zmm22, DQQWORD_SIZE_BIT-1, 0, ZMM22, 0, 0, ZMM22, false)  //!< zmm22
REG_SPEC(ZMM23, zmm23, DQQWORD_SIZE_BIT-1, 0, ZMM23, 0, 0, ZMM23, false)  //!< zmm23
REG_SPEC(ZMM24, zmm24, DQQWORD_SIZE_BIT-1, 0, ZMM24, 0, 0, ZMM24, false)  //!< zmm24
REG_SPEC(ZMM25, zmm25, DQQWORD_SIZE_BIT-1, 0, ZMM25, 0, 0, ZMM25, false)  //!< zmm25
REG_SPEC(ZMM26, zmm26, DQQWORD_SIZE_BIT-1, 0, ZMM26, 0, 0, ZMM26, false)  //!< zmm26
REG_SPEC(ZMM27, zmm27, DQQWORD_SIZE_BIT-1, 0, ZMM27, 0, 0, ZMM27, false)  //!< zmm27
REG_SPEC(ZMM28, zmm28, DQQWORD_SIZE_BIT-1, 0, ZMM28, 0, 0, ZMM28, false)  //!< zmm28
REG_SPEC(ZMM29, zmm29, DQQWORD_SIZE_BIT-1, 0, ZMM29, 0, 0, ZMM29, false)  //!< zmm29
REG_SPEC(ZMM30, zmm30, DQQWORD_SIZE_BIT-1, 0, ZMM30, 0, 0, ZMM30, false)  //!< zmm30
REG_SPEC(ZMM31, zmm31, DQQWORD_SIZE_BIT-1, 0, ZMM31, 0, 0, ZMM31, false)  //!< zmm31

/* Control */
REG_SPEC(CR0, cr0, QWORD_SIZE_BIT-1, 0, CR0, DWORD_SIZE_BIT-1, 0, CR0, true)        //!< cr0
REG_SPEC(CR1, cr1, QWORD_SIZE_BIT-1, 0, CR1, DWORD_SIZE_BIT-1, 0, CR1, true)        //!< cr1
REG_SPEC(CR2, cr2, QWORD_SIZE_BIT-1, 0, CR2, DWORD_SIZE_BIT-1, 0, CR2, true)        //!< cr2
REG_SPEC(CR3, cr3, QWORD_SIZE_BIT-1, 0, CR3, DWORD_SIZE_BIT-1, 0, CR3, true)        //!< cr3
REG_SPEC(CR4, cr4, QWORD_SIZE_BIT-1, 0, CR4, DWORD_SIZE_BIT-1, 0, CR4, true)        //!< cr4
REG_SPEC(CR5, cr5, QWORD_SIZE_BIT-1, 0, CR5, DWORD_SIZE_BIT-1, 0, CR5, true)        //!< cr5
REG_SPEC(CR6, cr6, QWORD_SIZE_BIT-1, 0, CR6, DWORD_SIZE_BIT-1, 0, CR6, true)        //!< cr6
REG_SPEC(CR7, cr7, QWORD_SIZE_BIT-1, 0, CR7, DWORD_SIZE_BIT-1, 0, CR7, true)        //!< cr7
REG_SPEC(CR8, cr8, QWORD_SIZE_BIT-1, 0, CR8, DWORD_SIZE_BIT-1, 0, CR8, true)        //!< cr8
REG_SPEC(CR9, cr9, QWORD_SIZE_BIT-1, 0, CR9, DWORD_SIZE_BIT-1, 0, CR9, true)        //!< cr9
REG_SPEC(CR10, cr10, QWORD_SIZE_BIT-1, 0, CR10, DWORD_SIZE_BIT-1, 0, CR10, true)    //!< cr10
REG_SPEC(CR11, cr11, QWORD_SIZE_BIT-1, 0, CR11, DWORD_SIZE_BIT-1, 0, CR11, true)    //!< cr11
REG_SPEC(CR12, cr12, QWORD_SIZE_BIT-1, 0, CR12, DWORD_SIZE_BIT-1, 0, CR12, true)    //!< cr12
REG_SPEC(CR13, cr13, QWORD_SIZE_BIT-1, 0, CR13, DWORD_SIZE_BIT-1, 0, CR13, true)    //!< cr13
REG_SPEC(CR14, cr14, QWORD_SIZE_BIT-1, 0, CR14, DWORD_SIZE_BIT-1, 0, CR14, true)    //!< cr14
REG_SPEC(CR15, cr15, QWORD_SIZE_BIT-1, 0, CR15, DWORD_SIZE_BIT-1, 0, CR15, true)    //!< cr15

/* Flags ID used in the Taint and Symbolic Engines */
REG_SPEC_NO_CAPSTONE(AF, af, 0, 0, AF, 0, 0, AF, true) //!< af
REG_SPEC_NO_CAPSTONE(CF, cf, 0, 0, CF, 0, 0, CF, true) //!< cf
REG_SPEC_NO_CAPSTONE(DF, df, 0, 0, DF, 0, 0, DF, true) //!< df
REG_SPEC_NO_CAPSTONE(IF, if, 0, 0, IF, 0, 0, IF, true) //!< if
REG_SPEC_NO_CAPSTONE(OF, of, 0, 0, OF, 0, 0, OF, true) //!< of
REG_SPEC_NO_CAPSTONE(PF, pf, 0, 0, PF, 0, 0, PF, true) //!< pf
REG_SPEC_NO_CAPSTONE(SF, sf, 0, 0, SF, 0, 0, SF, true) //!< sf
REG_SPEC_NO_CAPSTONE(TF, tf, 0, 0, TF, 0, 0, TF, true) //!< tf
REG_SPEC_NO_CAPSTONE(ZF, zf, 0, 0, ZF, 0, 0, ZF, true) //!< zf

/* SSE flags */
REG_SPEC_NO_CAPSTONE(IE, ie, 0, 0, IE, 0, 0, IE, true)      //!< ie (Invalid Operation Flag)
REG_SPEC_NO_CAPSTONE(DE, de, 0, 0, DE, 0, 0, DE, true)      //!< de (Denormal Flag)
REG_SPEC_NO_CAPSTONE(ZE, ze, 0, 0, ZE, 0, 0, ZE, true)      //!< ze (Divide By Zero Flag)
REG_SPEC_NO_CAPSTONE(OE, oe, 0, 0, OE, 0, 0, OE, true)      //!< oe (Overflow Flag)
REG_SPEC_NO_CAPSTONE(UE, ue, 0, 0, UE, 0, 0, UE, true)      //!< ue (Underflow Flag)
REG_SPEC_NO_CAPSTONE(PE, pe, 0, 0, PE, 0, 0, PE, true)      //!< pe (Precision Flag)
REG_SPEC_NO_CAPSTONE(DAZ, daz, 0, 0, DAZ, 0, 0, DAZ, true)  //!< daz (Invalid Operation Flag)
REG_SPEC_NO_CAPSTONE(IM, im, 0, 0, IM, 0, 0, IM, true)      //!< im (Invalid Operation Mask)
REG_SPEC_NO_CAPSTONE(DM, dm, 0, 0, DM, 0, 0, DM, true)      //!< dm (Denormal Mask)
REG_SPEC_NO_CAPSTONE(ZM, zm, 0, 0, ZM, 0, 0, ZM, true)      //!< zm (Divide By Zero Mask)
REG_SPEC_NO_CAPSTONE(OM, om, 0, 0, OM, 0, 0, OM, true)      //!< om (Overflow Mask)
REG_SPEC_NO_CAPSTONE(UM, um, 0, 0, UM, 0, 0, UM, true)      //!< um (Underflow Mask)
REG_SPEC_NO_CAPSTONE(PM, pm, 0, 0, PM, 0, 0, PM, true)      //!< pm (Precision Mask)
REG_SPEC_NO_CAPSTONE(RL, rl, 0, 0, RL, 0, 0, RL, true)      //!< rl (Round Negative)
REG_SPEC_NO_CAPSTONE(RH, rh, 0, 0, RH, 0, 0, RH, true)      //!< rh (Round Positive)
REG_SPEC_NO_CAPSTONE(FZ, fz, 0, 0, FZ, 0, 0, FZ, true)      //!< fz (Flush To Zero)

/* Segments */
REG_SPEC(CS, cs, QWORD_SIZE_BIT-1, 0, CS, DWORD_SIZE_BIT-1, 0, CS, true) //!< Code Segment
REG_SPEC(DS, ds, QWORD_SIZE_BIT-1, 0, DS, DWORD_SIZE_BIT-1, 0, DS, true) //!< Data Segment
REG_SPEC(ES, es, QWORD_SIZE_BIT-1, 0, ES, DWORD_SIZE_BIT-1, 0, ES, true) //!< Extra Segment
REG_SPEC(FS, fs, QWORD_SIZE_BIT-1, 0, FS, DWORD_SIZE_BIT-1, 0, FS, true) //!< F Segment
REG_SPEC(GS, gs, QWORD_SIZE_BIT-1, 0, GS, DWORD_SIZE_BIT-1, 0, GS, true) //!< G Segment
REG_SPEC(SS, ss, QWORD_SIZE_BIT-1, 0, SS, DWORD_SIZE_BIT-1, 0, SS, true) //!< Stack Segment

#undef REG_SPEC
#undef REG_SPEC_NO_CAPSTONE

#pragma warning(default:4067)
