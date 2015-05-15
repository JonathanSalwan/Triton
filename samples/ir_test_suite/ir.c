
// gcc -masm=intel ./ir.c -o ir

void check(void)
{
  int tab[4] = {1, 2, 3, 4};

  asm("clc");
  asm("cld");
  asm("cmc");
  asm("mov eax, 32");
  asm("mov ecx, 1");
  asm("mov ebx, eax");
  asm("mov rbx, qword ptr [rsp-0x2]");
  asm("mov rax, 2");
  asm("mov rcx, qword ptr [rsp+rax*1]");
  asm("mov qword ptr [rsp+rax*1], rcx");
  asm("add ecx, ebx");
  asm("adc eax, ecx");
  asm("inc eax");
  asm("test eax, eax");
  asm("sbb eax, ecx");
  asm("cmp ecx, eax");
  asm("cmp ecx, 3");
  asm("mov al, -1");
  asm("movsx eax, al");
  asm("movzx ecx, al");
  asm("movzx rdx, word ptr [rsp-0x2]");
  asm("movsx rax, word ptr [rsp-0x2]");
  asm("movapd xmm0, xmmword ptr [rbp-0x10]");
  asm("movapd xmm1, xmm2");
  asm("movapd xmm3, xmm0");
  asm("movaps xmm0, xmmword ptr [rbp-0x10]");
  asm("movaps xmm1, xmm2");
  asm("movaps xmm3, xmm0");
}

int main(){
  check();
}

