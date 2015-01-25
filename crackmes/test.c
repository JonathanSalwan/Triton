/*
**  Jonathan Salwan - 2015-01-24
** 
**  http://shell-storm.org
**  http://twitter.com/JonathanSalwan
** 
**  This program is free software: you can redistribute it and/or modify
**  it under the terms of the GNU General Public License as published by
**  the Free Software  Foundation, either  version 3 of  the License, or
**  (at your option) any later version.
*/

// gcc -masm=intel ./test.c -o test
int main(){
  asm("mov eax, 32");
  asm("mov ecx, 1");
  asm("mov ebx, eax");
  asm("add ecx, ebx");
  asm("cmp ecx, eax");
  asm("cmp ecx, 3");
}
