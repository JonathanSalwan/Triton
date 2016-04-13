
// gcc -masm=intel ./ir.c -o ir

void check(void)
{
  int tab1[4] = {0x11111111, 0x22222222, 0x33333333, 0x44444444};
  int tab2[4] = {0xd1d1d1d1, 0xffffffff, 0x55555555, 0x44444444};
  int tab3[4] = {0xd1d1d1d1, 0x12345678, 0x55909055, 0x44111144};
  int tab4[4] = {0x8aaaaaaa, 0x8bbbbbbb, 0x12345678, 0xfedcba98};

  // Check concat symbolic expression
  asm("mov sil, 0x99");
  asm("cmp rsi, 0xffffffffffffff99");

  asm("mov rax, -1");
  asm("push rax");
  asm("pop rbx");
  asm("mov al, 0x99");
  asm("mov ax, 0x99");
  asm("mov eax, 0x99");

  asm("mov rdx, 4");
  asm("mov rcx, 5");
  asm("xadd rdx, rcx");

  asm("mov rsi, %0" :: "r"(tab1));
  asm("mov rcx, 5");
  asm("rep lodsb");

  asm("mov rsi, %0" :: "r"(tab1));
  asm("mov rcx, 5");
  asm("rep lodsd");

  asm("mov rsi, %0" :: "r"(tab1));
  asm("mov rcx, 5");
  asm("rep lodsq");

  asm("mov rdi, %0" :: "r"(tab1));
  asm("mov rcx, 2");
  asm("rep stosb");

  asm("mov rdi, %0" :: "r"(tab1));
  asm("mov rcx, 2");
  asm("rep stosd");

  asm("mov rdi, %0" :: "r"(tab1));
  asm("mov rcx, 2");
  asm("rep stosq");

  asm("mov rdi, %0" :: "r"(tab1));
  asm("mov rcx, 2");
  asm("rep scasb");

  asm("mov rdi, %0" :: "r"(tab1));
  asm("mov rcx, 2");
  asm("rep scasd");

  asm("mov rdi, %0" :: "r"(tab1));
  asm("mov rcx, 2");
  asm("rep scasq");

  asm("mov rdi, %0" :: "r"(tab1));
  asm("mov rsi, %0" :: "r"(tab2));
  asm("mov rcx, 3");
  asm("rep cmpsb");

  asm("mov rdi, %0" :: "r"(tab2));
  asm("mov rsi, %0" :: "r"(tab3));
  asm("mov rcx, 3");
  asm("rep cmpsd");

  asm("mov rdi, %0" :: "r"(tab2));
  asm("mov rsi, %0" :: "r"(tab2));
  asm("mov rcx, 3");
  asm("rep cmpsq");

  asm("mov rdi, %0" :: "r"(tab2));
  asm("mov rsi, %0" :: "r"(tab2));
  asm("mov rcx, 3");
  asm("rep movsq");

  asm("mov rax, -1");
  asm("xor al, 0x99");
  asm("xor ax, 0x99");
  asm("xor eax, 0x99");

  asm("mov rdx, 18446744073709551615");
  asm("shr rdx, 0x1");

  asm("xor rdx, rdx");
  asm("mov rcx, 1024");
  asm("div rcx");

  asm("mov rax, -1");
  asm("or ah, 0x8");
  asm("mov rax, 12345");
  asm("or ah, 0x8");
  asm("mov rax, 4222427780");
  asm("or ah, 0x8");
  asm("or al, byte ptr [rsp+0xf]");

  asm("mov rax, 0x99");
  asm("mov rbx, 0xaa");
  asm("mov rcx, 0xdd");
  asm("cmpxchg rbx, rcx");

  asm("mov rbx, 0x99");
  asm("cmpxchg rbx, rcx");

  asm("mov rax, 0x1");
  asm("mov rbx, 0x0");
  asm("bsf rbx, rax");
  asm("mov rax, 0x2");
  asm("bsf rbx, rax");
  asm("mov rax, 0x40");
  asm("bsf rbx, rax");
  asm("mov rax, 0x1000");
  asm("bsf rbx, rax");
  asm("bsf bx, ax");
  asm("mov rax, 0x0");
  asm("bsf rbx, rax");
  asm("mov rax, 0x8000000000000000");
  asm("bsf rbx, rax");

  asm("mov rax, 0x1");
  asm("mov rbx, 0x0");
  asm("bsr rbx, rax");
  asm("mov rax, 0x2");
  asm("bsr rbx, rax");
  asm("mov rax, 0x40");
  asm("bsr rbx, rax");
  asm("mov rax, 0x1000");
  asm("bsr rbx, rax");
  asm("bsr bx, ax");
  asm("mov rax, 0x0");
  asm("bsr rbx, rax");

  asm("mov rax, 0x1111111111111111");
  asm("mov rbx, 0xffffffffffffffff");
  asm("mov rcx, 0x9090909090909090");
  asm("cmpxchg rbx, rcx");
  asm("cmpxchg qword ptr [%0], rbx" :: "r"(tab1));

  asm("mov rax, 0x1111111122222222");
  asm("cmpxchg qword ptr [%0], rcx" :: "r"(tab1));

  asm("mov rax, 0x2222222211111111");
  asm("cmpxchg qword ptr [%0], rbx" :: "r"(tab1));

  asm("mov eax, 0x99");
  asm("mov ebx, 0xaa");
  asm("mov ecx, 0xdd");
  asm("cmpxchg ebx, ebx");

  asm("mov eax, 0xffffffff");
  asm("mov ebx, 0xaa");
  asm("mov ecx, 0x12345678");
  asm("cmpxchg ecx, ebx");

  asm("mov eax, 0x99");
  asm("mov ebx, 0x99");
  asm("mov ecx, 0xdd");
  asm("cmpxchg ebx, ecx");

  asm("mov rbx, 0x99");
  asm("cmpxchg ebx, ecx");

  asm("cmpxchg8b qword ptr [%0]" :: "r"(tab1));

  asm("mov edx, dword ptr [%0]" :: "r"(tab1));
  asm("mov eax, dword ptr [%0]" :: "r"(tab1+4));
  asm("cmpxchg8b qword ptr [%0]" :: "r"(tab1));

  asm("clc");
  asm("cld");
  asm("cmc");

  asm("mov eax, 32");
  asm("cbw");

  asm("mov ecx, 1");
  asm("mov ebx, eax");
  asm("mov rbx, qword ptr [rsp-0x2]");
  asm("mov rax, 2");
  asm("mov rcx, qword ptr [rsp+rax*1]");
  asm("mov qword ptr [rsp+rax*1], rcx");

  asm("clc");
  asm("add ecx, ebx");
  asm("stc");

  asm("add ecx, ebx");
  asm("adc eax, ecx");
  asm("inc eax");
  asm("test eax, eax");
  asm("sbb eax, ecx");

  asm("mov rax, 27577336");
  asm("sbb eax, eax");
  asm("cmp ecx, eax");

  asm("mov ecx, 3");
  asm("mov ebx, 5");
  asm("cmp ecx, 3");

  asm("cmovb eax, ebx");
  asm("cmovl eax, ebx");
  asm("cmovno eax, ebx");
  asm("cmovnp eax, ebx");
  asm("cmovns eax, ebx");
  asm("cmovnz eax, ebx");
  asm("cmovo eax, ebx");
  asm("cmovp eax, ebx");
  asm("cmovs eax, ebx");
  asm("cmovz eax, ebx");

  asm("mov al, -1");
  asm("movsx eax, al");
  asm("movzx ecx, al");
  asm("movzx rcx, al");
  asm("movzx rdx, word ptr [rsp-0x2]");
  asm("movsx rax, word ptr [rsp-0x2]");

  asm("setz al");
  asm("mov rax, 3");
  asm("neg rax");
  asm("mov rax, 3");
  asm("mov rbx, 5");
  asm("xchg rax, rbx");
  asm("xchg [rsp-0x2], rax");

  asm("mov rbx, 9");
  asm("mov rax, 8");
  asm("lea rsi, [rbx]");
  asm("lea rsi, [rbx+8]");
  asm("lea rsi, [rip+8]");
  asm("lea rsi, [rbx+8*rax]");
  asm("lea rsi, [rbx+8*rax+4]");
  asm("lea rsi, [rbx+8+4*rax]");
  asm("lea rsi, [r12*4+0x8]");

  asm("cqo");

  // Check concat symbolic expression
  asm("mov rsi, 0xffffffffffffffff");
  asm("mov sil, 0x99");
  asm("cmp rsi, 0xffffffffffffff99");

  asm("shl rax, 3");
  asm("shl rax, 0");
  asm("shl rax, cl");
  asm("shl rax");
  asm("shr rax, 3");
  asm("shr rax, 0");
  asm("shr rax, cl");
  asm("shr rax");

  asm("idiv cl");
  asm("idiv cx");
  asm("idiv ecx");
  asm("idiv rcx");
  asm("idiv rcx");

  asm("xor rdx, rdx");
  asm("mov rcx, 1024");
  asm("div rcx");
  asm("mov rbx, 16");
  asm("div rbx");

  asm("mov rax, 1");
  asm("mov rcx, 2");
  asm("mov rdx, 3");
  asm("mov rsi, 4");

  asm("imul sil");
  asm("imul cx");
  asm("mov rcx, 0xffffffffffffffff");
  asm("imul rcx");
  asm("imul ecx, 1");
  asm("imul ecx, edx");
  asm("imul rdx, rcx, 4");

  asm("mul cl");
  asm("mul cx");
  asm("mul ecx");
  asm("mul rcx");

  asm("bswap ecx");
  asm("bswap rdx");

  asm("xor rcx, rcx");
  asm("mov cl, 3");
  asm("rol rdx, cl");
  asm("rol rdx, 4");
  asm("rol rdx, 1");
  asm("ror rdx, cl");
  asm("ror rdx, 4");
  asm("ror rdx, 1");

  asm("xor rcx, rcx");
  asm("mov cl, 3");
  asm("rcl rdx, cl");
  asm("rcl rdx, 4");
  asm("rcl rdx, 1");

  asm("xor rcx, rcx");
  asm("mov cl, 3");
  asm("rcr rdx, cl");
  asm("rcr rdx, 4");
  asm("rcr rdx, 1");

  // SSE
  asm("movapd xmm0, xmmword ptr [%0]" :: "r"(tab1));
  asm("movapd xmm1, xmm2");
  asm("movapd xmm3, xmm0");
  asm("movaps xmm0, xmmword ptr [%0]" :: "r"(tab2));
  asm("movaps xmm1, xmm2");
  asm("movaps xmm3, xmm0");
  asm("movdqa xmm4, xmm2");
  asm("movdqu xmm5, xmm0");
  asm("movhlps xmm6, xmm4");
  asm("movlhps xmm7, xmm5");

  asm("movddup xmm1, qword ptr [%0]" :: "r"(tab1));
  asm("movddup xmm2, xmm0");
  asm("movddup xmm3, xmm2");

  asm("mov esi, 0x11223344");
  asm("movd xmm1, esi");
  asm("movapd xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("movd esi, xmm1");

  asm("orpd xmm0, xmm1");
  asm("orps xmm1, xmm3");

  asm("xorpd xmm0, xmm1");
  asm("xorps xmm1, xmm3");

  asm("andpd xmm1, xmm3");
  asm("andps xmm1, xmm3");
  asm("andnpd xmm1, xmm3");
  asm("andnps xmm1, xmm3");

  asm("pxor xmm1, xmm2");
  asm("pxor xmm2, xmm3");

  asm("movaps xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("movaps xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("movaps xmm3, xmmword ptr [%0]" :: "r"(tab1));
  asm("movaps xmm4, xmmword ptr [%0]" :: "r"(tab2));
  asm("pmovmskb edx, xmm1");
  asm("pmovmskb eax, xmm2");
  asm("pmovmskb esi, xmm3");
  asm("pmovmskb r9d, xmm4");

  asm("movaps xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("movaps xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("movaps xmm3, xmmword ptr [%0]" :: "r"(tab1));
  asm("movaps xmm4, xmmword ptr [%0]" :: "r"(tab1));
  asm("movaps xmm5, xmmword ptr [%0]" :: "r"(tab2));
  asm("movaps xmm6, xmmword ptr [%0]" :: "r"(tab3));
  asm("pcmpeqb xmm1, xmm2");
  asm("pcmpeqb xmm3, xmm4");
  asm("pcmpeqb xmm5, xmm6");

  asm("movaps xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("movaps xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("movaps xmm3, xmmword ptr [%0]" :: "r"(tab1));
  asm("movaps xmm4, xmmword ptr [%0]" :: "r"(tab1));
  asm("movaps xmm5, xmmword ptr [%0]" :: "r"(tab2));
  asm("movaps xmm6, xmmword ptr [%0]" :: "r"(tab3));
  asm("pcmpeqw xmm1, xmm2");
  asm("pcmpeqw xmm3, xmm4");
  asm("pcmpeqw xmm5, xmm6");

  asm("movaps xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("movaps xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("movaps xmm3, xmmword ptr [%0]" :: "r"(tab1));
  asm("movaps xmm4, xmmword ptr [%0]" :: "r"(tab1));
  asm("movaps xmm5, xmmword ptr [%0]" :: "r"(tab2));
  asm("movaps xmm6, xmmword ptr [%0]" :: "r"(tab3));
  asm("pcmpeqd xmm1, xmm2");
  asm("pcmpeqd xmm3, xmm4");
  asm("pcmpeqd xmm5, xmm6");

  asm("movaps xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("movaps xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("movaps xmm3, xmmword ptr [%0]" :: "r"(tab1));
  asm("movaps xmm4, xmmword ptr [%0]" :: "r"(tab1));
  asm("movaps xmm5, xmmword ptr [%0]" :: "r"(tab2));
  asm("movaps xmm6, xmmword ptr [%0]" :: "r"(tab3));
  asm("pcmpgtb xmm1, xmm2");
  asm("pcmpgtb xmm3, xmm4");
  asm("pcmpgtb xmm5, xmm6");

  asm("movaps xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("movaps xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("movaps xmm3, xmmword ptr [%0]" :: "r"(tab1));
  asm("movaps xmm4, xmmword ptr [%0]" :: "r"(tab1));
  asm("movaps xmm5, xmmword ptr [%0]" :: "r"(tab2));
  asm("movaps xmm6, xmmword ptr [%0]" :: "r"(tab3));
  asm("pcmpgtw xmm1, xmm2");
  asm("pcmpgtw xmm3, xmm4");
  asm("pcmpgtw xmm5, xmm6");

  asm("movaps xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("movaps xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("movaps xmm3, xmmword ptr [%0]" :: "r"(tab1));
  asm("movaps xmm4, xmmword ptr [%0]" :: "r"(tab1));
  asm("movaps xmm5, xmmword ptr [%0]" :: "r"(tab2));
  asm("movaps xmm6, xmmword ptr [%0]" :: "r"(tab3));
  asm("pcmpgtd xmm1, xmm2");
  asm("pcmpgtd xmm3, xmm4");
  asm("pcmpgtd xmm5, xmm6");

  asm("movaps xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("movaps xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("movaps xmm3, xmmword ptr [%0]" :: "r"(tab3));
  asm("movaps xmm4, xmmword ptr [%0]" :: "r"(tab4));
  asm("movmskpd rax, xmm1");
  asm("movmskpd rax, xmm2");
  asm("movmskpd rax, xmm3");
  asm("movmskpd rax, xmm4");
  asm("movmskps rbx, xmm1");
  asm("movmskps rbx, xmm2");
  asm("movmskps rbx, xmm3");
  asm("movmskps rbx, xmm4");

  asm("movshdup xmm5, xmm1");
  asm("movshdup xmm6, xmm2");
  asm("movshdup xmm7, xmm3");
  asm("movshdup xmm8, xmm4");

  asm("movsldup xmm5, xmm1");
  asm("movsldup xmm6, xmm2");
  asm("movsldup xmm7, xmm3");
  asm("movsldup xmm8, xmm4");

  asm("movupd xmm5, xmm1");
  asm("movupd xmm6, xmm2");
  asm("movupd xmm7, xmm3");
  asm("movupd xmm8, xmm4");

  asm("movups xmm5, xmm1");
  asm("movups xmm6, xmm2");
  asm("movups xmm7, xmm3");
  asm("movups xmm8, xmm4");

  asm("lddqu xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("lddqu xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("lddqu xmm3, xmmword ptr [%0]" :: "r"(tab3));
  asm("lddqu xmm4, xmmword ptr [%0]" :: "r"(tab4));

  asm("pslldq xmm1, 1");
  asm("pslldq xmm2, 2");
  asm("pslldq xmm3, 3");
  asm("pslldq xmm4, 4");

  asm("lddqu xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("lddqu xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("lddqu xmm3, xmmword ptr [%0]" :: "r"(tab3));
  asm("lddqu xmm4, xmmword ptr [%0]" :: "r"(tab4));

  asm("pslldq xmm1, 5");
  asm("pslldq xmm2, 6");
  asm("pslldq xmm3, 7");
  asm("pslldq xmm4, 8");

  asm("lddqu xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("lddqu xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("lddqu xmm3, xmmword ptr [%0]" :: "r"(tab3));
  asm("lddqu xmm4, xmmword ptr [%0]" :: "r"(tab4));

  asm("pslldq xmm1, 15");
  asm("pslldq xmm2, 16");
  asm("pslldq xmm3, 17");
  asm("pslldq xmm4, 18");

  asm("lddqu xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("lddqu xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("lddqu xmm3, xmmword ptr [%0]" :: "r"(tab3));
  asm("lddqu xmm4, xmmword ptr [%0]" :: "r"(tab4));

  asm("psrldq xmm1, 1");
  asm("psrldq xmm2, 2");
  asm("psrldq xmm3, 3");
  asm("psrldq xmm4, 4");

  asm("lddqu xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("lddqu xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("lddqu xmm3, xmmword ptr [%0]" :: "r"(tab3));
  asm("lddqu xmm4, xmmword ptr [%0]" :: "r"(tab4));

  asm("psrldq xmm1, 5");
  asm("psrldq xmm2, 6");
  asm("psrldq xmm3, 7");
  asm("psrldq xmm4, 8");

  asm("lddqu xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("lddqu xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("lddqu xmm3, xmmword ptr [%0]" :: "r"(tab3));
  asm("lddqu xmm4, xmmword ptr [%0]" :: "r"(tab4));

  asm("psrldq xmm1, 15");
  asm("psrldq xmm2, 16");
  asm("psrldq xmm3, 17");
  asm("psrldq xmm4, 18");

  asm("lddqu xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("lddqu xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("lddqu xmm3, xmmword ptr [%0]" :: "r"(tab3));
  asm("lddqu xmm4, xmmword ptr [%0]" :: "r"(tab4));

  asm("unpckhpd xmm1, xmm2");
  asm("unpckhpd xmm3, xmm4");
  asm("unpckhps xmm1, xmm4");
  asm("unpckhps xmm2, xmm3");
  asm("unpcklpd xmm1, xmm2");
  asm("unpcklpd xmm3, xmm4");
  asm("unpcklps xmm1, xmm4");
  asm("unpcklps xmm2, xmm3");

  asm("lddqu xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("lddqu xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("lddqu xmm3, xmmword ptr [%0]" :: "r"(tab3));
  asm("lddqu xmm4, xmmword ptr [%0]" :: "r"(tab4));

  asm("ptest xmm1, xmm1");
  asm("ptest xmm2, xmm3");
  asm("ptest xmm3, xmm4");
  asm("ptest xmm4, xmm1");

  asm("vptest xmm1, xmm1");
  asm("vptest xmm2, xmm3");
  asm("vptest xmm3, xmm4");
  asm("vptest xmm4, xmm1");

  asm("punpckhbw xmm1, xmm2");
  asm("punpckhbw xmm2, xmm3");
  asm("punpckhbw xmm3, xmm4");

  asm("punpckhwd xmm1, xmm2");
  asm("punpckhwd xmm2, xmm3");
  asm("punpckhwd xmm3, xmm4");

  asm("punpckhdq xmm1, xmm2");
  asm("punpckhdq xmm2, xmm3");
  asm("punpckhdq xmm3, xmm4");

  asm("punpckhqdq xmm1, xmm2");
  asm("punpckhqdq xmm2, xmm3");
  asm("punpckhqdq xmm3, xmm4");

  asm("punpcklbw xmm1, xmm2");
  asm("punpcklbw xmm2, xmm3");
  asm("punpcklbw xmm3, xmm4");

  asm("punpcklwd xmm1, xmm2");
  asm("punpcklwd xmm2, xmm3");
  asm("punpcklwd xmm3, xmm4");

  asm("punpckldq xmm1, xmm2");
  asm("punpckldq xmm2, xmm3");
  asm("punpckldq xmm3, xmm4");

  asm("punpcklqdq xmm1, xmm2");
  asm("punpcklqdq xmm2, xmm3");
  asm("punpcklqdq xmm3, xmm4");

  asm("psubb xmm3, xmm4");
  asm("psubb xmm1, xmm2");
  asm("psubb xmm2, xmm4");

  asm("psubw xmm3, xmm4");
  asm("psubw xmm1, xmm2");
  asm("psubw xmm2, xmm4");

  asm("psubd xmm3, xmm4");
  asm("psubd xmm1, xmm2");
  asm("psubd xmm2, xmm4");

  asm("psubq xmm3, xmm4");
  asm("psubq xmm1, xmm2");
  asm("psubq xmm2, xmm4");

  asm("paddb xmm3, xmm4");
  asm("paddb xmm1, xmm2");
  asm("paddb xmm2, xmm4");

  asm("paddw xmm3, xmm4");
  asm("paddw xmm1, xmm2");
  asm("paddw xmm2, xmm4");

  asm("paddd xmm3, xmm4");
  asm("paddd xmm1, xmm2");
  asm("paddd xmm2, xmm4");

  asm("paddq xmm3, xmm4");
  asm("paddq xmm1, xmm2");
  asm("paddq xmm2, xmm4");
}

int main(){
  check();
}

