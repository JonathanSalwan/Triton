
// gcc -masm=intel ./ir.c -o ir

void check(void)
{
  short x = -1;

  asm("clc");
  asm("cld");
  asm("cmc");
  asm("mov eax, 32");
  asm("mov ecx, 1");
  asm("mov ebx, eax");
  asm("mov rbx, word ptr [rsp-0x2]");
  asm("mov rax, 2");
  asm("mov rcx, word ptr [rsp+rax*1]");
  asm("mov word ptr [rsp+rax*1], rcx");
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
  asm("movapd xmm0, xmmword ptr [rsp+112]");
  asm("movapd xmm1, xmm2");
  asm("movapd xmm3, xmm0");
  asm("movaps xmm0, xmmword ptr [rsp+112]");
  asm("movaps xmm1, xmm2");
  asm("movaps xmm3, xmm0");
}

int main(){
  check();
}

