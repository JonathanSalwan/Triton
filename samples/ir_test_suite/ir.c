
// gcc -masm=intel ./test.c -o test

void check(void)
{
  asm("clc");
  asm("cld");
  asm("cmc");
  asm("mov eax, 32");
  asm("mov ecx, 1");
  asm("mov ebx, eax");
  asm("add ecx, ebx");
  asm("adc eax, ecx");
  asm("inc eax");
  asm("sbb eax, ecx");
  asm("cmp ecx, eax");
  asm("cmp ecx, 3");
}

int main(){
  check();
}
