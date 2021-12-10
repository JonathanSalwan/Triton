// Test cases for Triton
// gcc -O0 -masm=intel ./ir.c -o ir

void init(int *tab1, int *tab2, int *tab3, int *tab4, int *tab5, int *tab6, int *tab7, int *tab8) {
  tab1[0] = 0x11111111;
  tab1[1] = 0x22222222;
  tab1[2] = 0x33333333;
  tab1[3] = 0x44444444;

  tab2[0] = 0xd1d1d1d1;
  tab2[1] = 0xffffffff;
  tab2[2] = 0x00005555;
  tab2[3] = 0x80008000;

  tab3[0] = 0xd1d1d1d1;
  tab3[1] = 0x12345678;
  tab3[2] = 0x55909055;
  tab3[3] = 0x44111144;

  tab4[0] = 0x8aaaaaaa;
  tab4[1] = 0x8bbbbbbb;
  tab4[2] = 0x12345678;
  tab4[3] = 0xfedcba98;

  tab5[0] = 0x00050001;
  tab5[1] = 0x000b000a;
  tab5[2] = 0x00fe0016;
  tab5[3] = 0x010000ff;

  tab6[0] = 0x11111111;
  tab6[1] = 0x22222222;
  tab6[2] = 0x33333333;
  tab6[3] = 0x80008000;
  tab6[4] = 0x00000001;
  tab6[5] = 0x66666666;
  tab6[6] = 0x77777777;
  tab6[7] = 0x88888888;

  tab7[0] = 0x12010001;
  tab7[1] = 0x00007ffe;
  tab7[2] = 0x12345678;
  tab7[3] = 0x00001111;
  tab7[4] = 0x010100dd;
  tab7[5] = 0x88885555;
  tab7[6] = 0x905588b2;
  tab7[7] = 0x00002222;

  tab8[0] = 0x00000000;
  tab8[1] = 0x00000000;
  tab8[2] = 0x00000000;
  tab8[3] = 0x00000000;
}

void check(void)
{
  int tab1[4];
  int tab2[4];
  int tab3[4];
  int tab4[4];
  int tab5[4];
  int tab6[8];
  int tab7[8];
  int tab8[4];

  int _utab1[5];
  int _utab2[5];
  int _utab3[5];
  int _utab4[5];

  int* utab1 = (int*)((char*)_utab1 + 1);
  int* utab2 = (int*)((char*)_utab2 + 1);
  int* utab3 = (int*)((char*)_utab3 + 1);
  int* utab4 = (int*)((char*)_utab4 + 1);

  init(tab1, tab2, tab3, tab4, tab5, tab6, tab7, tab8);

  // Check concat symbolic expression
  asm("mov sil, 0x99");
  asm("cmp rsi, 0xffffffffffffff99");

  asm("mov rax, -1");
  asm("push rax");
  asm("pop rbx");
  asm("mov al, 0x99");
  asm("mov ax, 0x99");
  asm("mov eax, 0x99");

  asm("mov rax, 0x1234567890abcdef");
  asm("mov rbx, 0x1111111111111111");
  asm("push rax");
  asm("pop bx");
  asm("push ax");
  asm("pop rbx");

  asm("push rsp");
  asm("pop rax");
  asm("push rsp");
  asm("pop rbx");
  asm("cmp rax, rsp");
  asm("cmp rbx, rsp");
  asm("push rbx");
  asm("pop rsp");
  asm("cmp rbx, rsp");

  asm("push 0");
  asm("push 0x11");
  asm("push 0x1122");
  asm("push 0x11223344");

  asm("mov rdx, 4");
  asm("mov rcx, 5");
  asm("xadd rdx, rcx");

  asm("mov rdx, 0xffffffff11223344");
  asm("mov rcx, 0x11223344ffffffff");
  asm("xadd rdx, rcx");
  asm("xadd rdx, rcx");
  asm("xadd rdx, rcx");
  asm("xadd rdx, rcx");
  asm("xadd rdx, rcx");
  asm("xadd rdx, rcx");
  asm("mov rsi, %0" :: "r"(tab1));
  asm("xadd [rsi], rcx");
  asm("xadd [rsi], rcx");
  asm("xadd [rsi], rcx");
  asm("mov rsi, %0" :: "r"(tab2));
  asm("xadd [rsi], rcx");
  asm("xadd [rsi], rcx");
  asm("xadd [rsi], rcx");
  asm("mov rsi, %0" :: "r"(tab3));
  asm("xadd [rsi], rcx");
  asm("xadd [rsi], rcx");
  asm("xadd [rsi], rcx");
  asm("mov rsi, %0" :: "r"(tab4));
  asm("xadd [rsi], rcx");
  asm("xadd [rsi], rcx");
  asm("xadd [rsi], rcx");

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

  asm("mov rdi, %0" :: "r"(tab2));
  asm("mov rsi, %0" :: "r"(tab2));
  asm("mov rcx, 0");
  asm("rep movsq");

  asm("mov rdi, %0" :: "r"(tab2));
  asm("mov rsi, %0" :: "r"(tab2));
  asm("mov rcx, 5");
  asm("rep movsq");

  asm("mov rdi, %0" :: "r"(tab3));
  asm("mov rsi, %0" :: "r"(tab1));
  asm("mov rcx, 5");
  asm("rep movsq");

  asm("mov rdi, %0" :: "r"(tab1));
  asm("mov rsi, %0" :: "r"(tab2));
  asm("mov rcx, 0");
  asm("rep cmpsb");

  asm("mov rdi, %0" :: "r"(tab2));
  asm("mov rsi, %0" :: "r"(tab3));
  asm("mov rcx, 0");
  asm("rep cmpsd");

  asm("mov rdi, %0" :: "r"(tab2));
  asm("mov rsi, %0" :: "r"(tab2));
  asm("mov rcx, 0");
  asm("rep cmpsq");

  asm("mov rdi, %0" :: "r"(tab2));
  asm("mov rsi, %0" :: "r"(tab2));
  asm("mov rcx, 0");
  asm("rep movsq");

  asm("mov rdi, %0" :: "r"(tab3));
  asm("mov rsi, %0" :: "r"(tab1));
  asm("mov rcx, 4");
  asm("rep movsq");

  asm("mov rdi, %0" :: "r"(tab3));
  asm("mov rsi, %0" :: "r"(tab1));
  asm("mov rcx, 4");
  asm("rep cmpsb");

  asm("mov rdi, %0" :: "r"(tab1));
  asm("mov rsi, %0" :: "r"(tab2));
  asm("mov rcx, 4");
  asm("rep movsq");

  asm("mov rdi, %0" :: "r"(tab1));
  asm("mov rsi, %0" :: "r"(tab2));
  asm("mov rcx, 0");
  asm("rep cmpsb");

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

  init(tab1, tab2, tab3, tab4, tab5, tab6, tab7, tab8);

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

  asm("mov rax, 0x0");
  asm("mov rbx, 0x0");
  asm("tzcnt rbx, rax");
  asm("mov rax, 0x0");
  asm("mov rbx, 0x1");
  asm("tzcnt rbx, rax");
  asm("mov rax, 0x1");
  asm("mov rbx, 0x0");
  asm("tzcnt rbx, rax");
  asm("mov rax, 0x2");
  asm("tzcnt rbx, rax");
  asm("mov rax, 0x40");
  asm("tzcnt rbx, rax");
  asm("mov rax, 0x1000");
  asm("tzcnt rbx, rax");
  asm("tzcnt bx, ax");
  asm("mov rax, 0x0");
  asm("tzcnt rbx, rax");
  asm("mov rax, 0x8000000000000000");
  asm("tzcnt rbx, rax");
  asm("mov rax, 0xffffffffffffffff");
  asm("mov rbx, 0x0");
  asm("tzcnt rbx, rax");

  asm("mov rax, 0x0");
  asm("mov rbx, 0x0");
  asm("tzcnt ebx, eax");
  asm("mov rax, 0x0");
  asm("mov rbx, 0x1");
  asm("tzcnt ebx, eax");
  asm("mov rax, 0x1");
  asm("mov rbx, 0x0");
  asm("tzcnt ebx, eax");
  asm("mov rax, 0x2");
  asm("tzcnt ebx, eax");
  asm("mov rax, 0x40");
  asm("tzcnt ebx, eax");
  asm("mov rax, 0x1000");
  asm("tzcnt ebx, eax");
  asm("tzcnt bx, ax");
  asm("mov rax, 0x0");
  asm("tzcnt ebx, eax");
  asm("mov rax, 0x8000000000000000");
  asm("tzcnt ebx, eax");

  init(tab1, tab2, tab3, tab4, tab5, tab6, tab7, tab8);

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

  init(tab1, tab2, tab3, tab4, tab5, tab6, tab7, tab8);

  asm("cmpxchg8b qword ptr [%0]" :: "r"(tab1));

  asm("mov edx, dword ptr [%0]" :: "r"(tab1));
  asm("mov eax, dword ptr [%0]" :: "r"(tab1+4));
  asm("cmpxchg8b qword ptr [%0]" :: "r"(tab1));

  asm("cmpxchg16b oword ptr [%0]" :: "r"(tab1));

  asm("mov edx, dword ptr [%0]" :: "r"(tab1));
  asm("mov eax, dword ptr [%0]" :: "r"(tab1+4));
  asm("cmpxchg16b oword ptr [%0]" :: "r"(tab1));

  asm("mov edx, dword ptr [%0]" :: "r"(tab1+4));
  asm("mov eax, dword ptr [%0]" :: "r"(tab1));
  asm("cmpxchg16b oword ptr [%0]" :: "r"(tab1));

  asm("mov rdx, qword ptr [%0]" :: "r"(tab1));
  asm("mov rax, qword ptr [%0]" :: "r"(tab1+8));
  asm("cmpxchg16b oword ptr [%0]" :: "r"(tab1));

  asm("mov rdx, qword ptr [%0]" :: "r"(tab1+8));
  asm("mov rax, qword ptr [%0]" :: "r"(tab1));
  asm("cmpxchg16b oword ptr [%0]" :: "r"(tab1));

  asm("clc");
  asm("cld");
  asm("cmc");

  asm("mov rbx, 0b00000001");
  asm("bt rbx, 0");
  asm("bt rbx, 1");
  asm("bt rbx, 4");
  asm("bt rbx, 64");
  asm("bt rbx, 65");
  asm("bt rbx, 66");
  asm("mov rbx, 0b1101010111010110101011010100110101010101110010101010101101011010");
  asm("bt rbx, 0");
  asm("bt rbx, 1");
  asm("bt rbx, 2");
  asm("bt rbx, 3");
  asm("bt rbx, 4");
  asm("bt rbx, 5");
  asm("bt rbx, 6");
  asm("bt rbx, 7");
  asm("bt rbx, 8");
  asm("bt rbx, 9");
  asm("bt rbx, 10");
  asm("bt rbx, 62");
  asm("bt rbx, 63");
  asm("bt rbx, 64");
  asm("bt rbx, 65");
  asm("bt rbx, 66");
  asm("bt rbx, 67");
  asm("bt rbx, 68");
  asm("bt rbx, 69");
  asm("bt rbx, 70");
  asm("bt rbx, 120");
  asm("bt rbx, 121");
  asm("bt rbx, 122");
  asm("bt rbx, 123");
  asm("bt rbx, 124");
  asm("bt rbx, 125");
  asm("bt rbx, 126");
  asm("bt rbx, 127");
  asm("bt rbx, 231");
  asm("bt rbx, 232");
  asm("bt rbx, 233");
  asm("bt rbx, 234");
  asm("bt rbx, 253");
  asm("bt rbx, 254");
  asm("bt rbx, 255");
  asm("mov rax, 8");
  asm("bt rbx, rax");
  asm("mov rax, 43");
  asm("bt rbx, rax");
  asm("mov rax, 65");
  asm("bt rbx, rax");
  asm("mov rax, 125");
  asm("bt rbx, rax");
  asm("mov rax, 126");
  asm("bt rbx, rax");
  asm("mov rax, 127");
  asm("bt rbx, rax");
  asm("mov rax, 128");
  asm("bt rbx, rax");
  asm("mov rax, 129");
  asm("bt rbx, rax");

  asm("mov rbx, 0b00000001");
  asm("bts rbx, 0");
  asm("bts rbx, 1");
  asm("bts rbx, 4");
  asm("bts rbx, 64");
  asm("bts rbx, 65");
  asm("bts rbx, 66");
  asm("mov rbx, 0b1101010111010110101011010100110101010101110010101010101101011010");
  asm("bts rbx, 0");
  asm("bts rbx, 1");
  asm("bts rbx, 2");
  asm("bts rbx, 3");
  asm("bts rbx, 4");
  asm("bts rbx, 5");
  asm("bts rbx, 6");
  asm("bts rbx, 7");
  asm("bts rbx, 8");
  asm("bts rbx, 9");
  asm("bts rbx, 10");
  asm("bts rbx, 62");
  asm("bts rbx, 63");
  asm("bts rbx, 64");
  asm("bts rbx, 65");
  asm("bts rbx, 66");
  asm("bts rbx, 67");
  asm("bts rbx, 68");
  asm("bts rbx, 69");
  asm("bts rbx, 70");
  asm("bts rbx, 120");
  asm("bts rbx, 121");
  asm("bts rbx, 122");
  asm("bts rbx, 123");
  asm("bts rbx, 124");
  asm("bts rbx, 125");
  asm("bts rbx, 126");
  asm("bts rbx, 127");
  asm("bts rbx, 231");
  asm("bts rbx, 232");
  asm("bts rbx, 233");
  asm("bts rbx, 234");
  asm("bts rbx, 253");
  asm("bts rbx, 254");
  asm("bts rbx, 255");
  asm("mov rax, 8");
  asm("bts rbx, rax");
  asm("mov rax, 43");
  asm("bts rbx, rax");
  asm("mov rax, 65");
  asm("bts rbx, rax");
  asm("mov rax, 125");
  asm("bts rbx, rax");
  asm("mov rax, 126");
  asm("bts rbx, rax");
  asm("mov rax, 127");
  asm("bts rbx, rax");
  asm("mov rax, 128");
  asm("bts rbx, rax");
  asm("mov rax, 129");
  asm("bts rbx, rax");

  asm("mov rbx, 0b00000001");
  asm("btr rbx, 0");
  asm("btr rbx, 1");
  asm("btr rbx, 4");
  asm("btr rbx, 64");
  asm("btr rbx, 65");
  asm("btr rbx, 66");
  asm("mov rbx, 0b1101010111010110101011010100110101010101110010101010101101011010");
  asm("btr rbx, 0");
  asm("btr rbx, 1");
  asm("btr rbx, 2");
  asm("btr rbx, 3");
  asm("btr rbx, 4");
  asm("btr rbx, 5");
  asm("btr rbx, 6");
  asm("btr rbx, 7");
  asm("btr rbx, 8");
  asm("btr rbx, 9");
  asm("btr rbx, 10");
  asm("btr rbx, 62");
  asm("btr rbx, 63");
  asm("btr rbx, 64");
  asm("btr rbx, 65");
  asm("btr rbx, 66");
  asm("btr rbx, 67");
  asm("btr rbx, 68");
  asm("btr rbx, 69");
  asm("btr rbx, 70");
  asm("btr rbx, 120");
  asm("btr rbx, 121");
  asm("btr rbx, 122");
  asm("btr rbx, 123");
  asm("btr rbx, 124");
  asm("btr rbx, 125");
  asm("btr rbx, 126");
  asm("btr rbx, 127");
  asm("btr rbx, 231");
  asm("btr rbx, 232");
  asm("btr rbx, 233");
  asm("btr rbx, 234");
  asm("btr rbx, 253");
  asm("btr rbx, 254");
  asm("btr rbx, 255");
  asm("mov rax, 8");
  asm("btr rbx, rax");
  asm("mov rax, 43");
  asm("btr rbx, rax");
  asm("mov rax, 65");
  asm("btr rbx, rax");
  asm("mov rax, 125");
  asm("btr rbx, rax");
  asm("mov rax, 126");
  asm("btr rbx, rax");
  asm("mov rax, 127");
  asm("btr rbx, rax");
  asm("mov rax, 128");
  asm("btr rbx, rax");
  asm("mov rax, 129");
  asm("btr rbx, rax");

  asm("mov rbx, 0b00000001");
  asm("btc rbx, 0");
  asm("btc rbx, 1");
  asm("btc rbx, 4");
  asm("btc rbx, 64");
  asm("btc rbx, 65");
  asm("btc rbx, 66");
  asm("mov rbx, 0b1101010111010110101011010100110101010101110010101010101101011010");
  asm("btc rbx, 0");
  asm("btc rbx, 1");
  asm("btc rbx, 2");
  asm("btc rbx, 3");
  asm("btc rbx, 4");
  asm("btc rbx, 5");
  asm("btc rbx, 6");
  asm("btc rbx, 7");
  asm("btc rbx, 8");
  asm("btc rbx, 9");
  asm("btc rbx, 10");
  asm("btc rbx, 62");
  asm("btc rbx, 63");
  asm("btc rbx, 64");
  asm("btc rbx, 65");
  asm("btc rbx, 66");
  asm("btc rbx, 67");
  asm("btc rbx, 68");
  asm("btc rbx, 69");
  asm("btc rbx, 70");
  asm("btc rbx, 120");
  asm("btc rbx, 121");
  asm("btc rbx, 122");
  asm("btc rbx, 123");
  asm("btc rbx, 124");
  asm("btc rbx, 125");
  asm("btc rbx, 126");
  asm("btc rbx, 127");
  asm("btc rbx, 231");
  asm("btc rbx, 232");
  asm("btc rbx, 233");
  asm("btc rbx, 234");
  asm("btc rbx, 253");
  asm("btc rbx, 254");
  asm("btc rbx, 255");
  asm("mov rax, 8");
  asm("btc rbx, rax");
  asm("mov rax, 43");
  asm("btc rbx, rax");
  asm("mov rax, 65");
  asm("btc rbx, rax");
  asm("mov rax, 125");
  asm("btc rbx, rax");
  asm("mov rax, 126");
  asm("btc rbx, rax");
  asm("mov rax, 127");
  asm("btc rbx, rax");
  asm("mov rax, 128");
  asm("btc rbx, rax");
  asm("mov rax, 129");
  asm("btc rbx, rax");

  asm("mov eax, 32");
  asm("cbw");
  asm("mov ax, 0x32");
  asm("cwd");
  asm("mov ax, 0x8000");
  asm("cwd");
  asm("mov ax, 0x8001");
  asm("cwd");
  asm("mov eax, 0x32");
  asm("cdq");
  asm("mov eax, 0x8000");
  asm("cdq");
  asm("mov eax, 0x8001");
  asm("cdq");
  asm("mov eax, 0x800000");
  asm("cdq");
  asm("mov eax, 0x800001");
  asm("cdq");

  asm("mov ecx, 1");
  asm("mov ebx, eax");
  asm("mov rbx, qword ptr [rsp-0x2]");
  asm("mov rax, 2");
  asm("mov rcx, qword ptr [rsp+rax*1]");
  asm("mov qword ptr [rsp+rax*1], rcx");

  asm("clc");
  asm("add ecx, ebx");
  asm("stc");

  asm("pushfq");
  asm("add ecx, ebx");
  asm("popfq");
  asm("pushfq");
  asm("adc eax, ecx");
  asm("popfq");
  asm("pushfq");
  asm("inc eax");
  asm("popfq");
  asm("pushfq");
  asm("test eax, eax");
  asm("popfq");
  asm("pushfq");
  asm("sbb eax, ecx");
  asm("popfq");

  asm("mov rax, 27577336");
  asm("sbb eax, eax");
  asm("cmp ecx, eax");

  asm("mov ecx, 3");
  asm("mov ebx, 5");
  asm("cmp ecx, 3");

  asm("mov ah, 0xff");
  asm("sahf");
  asm("lahf");
  asm("mov ah, 0x00");
  asm("sahf");
  asm("lahf");
  asm("mov ah, 0x11");
  asm("sahf");
  asm("lahf");
  asm("mov ah, 0x22");
  asm("sahf");
  asm("lahf");
  asm("mov ah, 0x33");
  asm("sahf");
  asm("lahf");
  asm("mov ah, 0x44");
  asm("sahf");
  asm("lahf");
  asm("mov ah, 0x55");
  asm("sahf");
  asm("lahf");

  asm("pushfq");
  asm("pushfq");
  asm("pushfq");
  asm("popfq");
  asm("popfq");
  asm("popfq");
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
  asm("mov rax, 0x1122334455667788");
  asm("neg rax");
  asm("mov rax, 0x2233445566778811");
  asm("neg rax");
  asm("mov rax, 0x3344556677881122");
  asm("neg rax");
  asm("mov rax, 0x4455667788112233");
  asm("neg rax");
  asm("mov rax, 0x8811223344556677");
  asm("neg rax");
  asm("mov rax, 0xffffffffffffffff");
  asm("neg rax");
  asm("mov rax, 0");
  asm("neg rax");
  asm("mov rax, 0x8000000000000000");
  asm("neg rax");
  asm("mov rax, 0x1122334455667788");
  asm("neg eax");
  asm("mov rax, 0x2233445566778811");
  asm("neg eax");
  asm("mov rax, 0x3344556677881122");
  asm("neg eax");
  asm("mov rax, 0x4455667788112233");
  asm("neg eax");
  asm("mov rax, 0x8811223344556677");
  asm("neg eax");
  asm("mov rax, 0xffffffffffffffff");
  asm("neg eax");
  asm("mov rax, 0");
  asm("neg eax");
  asm("mov rax, 0x0000000080000000");
  asm("neg eax");
  asm("mov rax, 0x1122334455667788");
  asm("neg ax");
  asm("mov rax, 0x2233445566778811");
  asm("neg ax");
  asm("mov rax, 0x3344556677881122");
  asm("neg ax");
  asm("mov rax, 0x4455667788112233");
  asm("neg ax");
  asm("mov rax, 0x8811223344556677");
  asm("neg ax");
  asm("mov rax, 0xffffffffffffffff");
  asm("neg ax");
  asm("mov rax, 0");
  asm("neg ax");
  asm("mov rax, 0x0000000000008000");
  asm("neg ax");

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

  asm("xor rdx, rdx");
  asm("mov rcx, 1024");
  asm("div rcx");
  asm("mov rbx, 16");
  asm("div rbx");

  asm("mov rdx, 0x12345678");
  asm("shl rdx, 0");
  asm("mov rdx, 0x12345678");
  asm("shl rdx, cl");
  asm("mov rdx, 0x12345678");
  asm("shl rdx");
  asm("mov rdx, 0x12345678");
  asm("shl rdx, 63");
  asm("mov rdx, 0x12345678");
  asm("shl rdx, 64");
  asm("mov rdx, 0x12345678");
  asm("shl rdx, 65");
  asm("mov rdx, 0x12345678");
  asm("mov cl, 63");
  asm("shl rdx, cl");
  asm("mov rdx, 0x12345678");
  asm("mov cl, 64");
  asm("shl rdx, cl");
  asm("mov rdx, 0x12345678");
  asm("mov cl, 65");
  asm("shl rdx, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("shl edx, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shl edx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shl edx");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shl edx, 31");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shl edx, 32");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shl edx, 33");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 31");
  asm("shl edx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 32");
  asm("shl edx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 33");
  asm("shl edx, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("shl dx, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shl dx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shl dx");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shl dx, 15");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shl dx, 16");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shl dx, 17");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 15");
  asm("shl dx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 16");
  asm("shl dx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 17");
  asm("shl dx, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("shl dh, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shl dh, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shl dh");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shl dh, 7");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shl dh, 8");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shl dh, 9");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 7");
  asm("shl dh, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 8");
  asm("shl dh, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 9");
  asm("shl dh, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("shl dl, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shl dl, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shl dl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shl dl, 7");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shl dl, 8");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shl dl, 9");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 7");
  asm("shl dl, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 8");
  asm("shl dl, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 9");
  asm("shl dl, cl");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld rax, rbx, 0");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld rax, rbx, 1");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld rax, rbx, 2");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld rax, rbx, 3");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld rax, rbx, 4");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld rax, rbx, 5");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld rax, rbx, 15");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld rax, rbx, 16");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld rax, rbx, 17");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld rax, rbx, 31");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld rax, rbx, 32");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld rax, rbx, 33");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld rax, rbx, 63");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld rax, rbx, 64");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld rax, rbx, 65");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld rax, rbx, 80");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld rax, rbx, 81");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld rax, rbx, 126");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld rax, rbx, 127");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld rax, rbx, 128");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld rax, rbx, 255");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld eax, ebx, 0");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld eax, ebx, 1");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld eax, ebx, 2");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld eax, ebx, 3");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld eax, ebx, 4");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld eax, ebx, 5");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld eax, ebx, 15");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld eax, ebx, 16");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld eax, ebx, 17");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld eax, ebx, 31");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld eax, ebx, 32");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld eax, ebx, 33");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld eax, ebx, 63");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld eax, ebx, 64");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld eax, ebx, 65");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld eax, ebx, 80");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld eax, ebx, 81");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld eax, ebx, 126");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld eax, ebx, 127");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld eax, ebx, 128");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld eax, ebx, 255");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld ax, bx, 0");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld ax, bx, 1");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld ax, bx, 2");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld ax, bx, 3");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld ax, bx, 4");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld ax, bx, 5");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld ax, bx, 15");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld ax, bx, 16");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld ax, bx, 17");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld ax, bx, 31");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld ax, bx, 32");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld ax, bx, 33");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld ax, bx, 63");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld ax, bx, 64");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld ax, bx, 65");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld ax, bx, 80");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld ax, bx, 81");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld ax, bx, 126");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld ax, bx, 127");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld ax, bx, 128");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shld ax, bx, 255");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd rax, rbx, 0");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd rax, rbx, 1");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd rax, rbx, 2");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd rax, rbx, 3");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd rax, rbx, 4");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd rax, rbx, 5");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd rax, rbx, 15");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd rax, rbx, 16");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd rax, rbx, 17");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd rax, rbx, 31");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd rax, rbx, 32");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd rax, rbx, 33");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd rax, rbx, 63");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd rax, rbx, 64");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd rax, rbx, 65");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd rax, rbx, 80");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd rax, rbx, 81");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd rax, rbx, 126");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd rax, rbx, 127");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd rax, rbx, 128");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd rax, rbx, 255");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd eax, ebx, 0");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd eax, ebx, 1");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd eax, ebx, 2");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd eax, ebx, 3");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd eax, ebx, 4");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd eax, ebx, 5");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd eax, ebx, 15");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd eax, ebx, 16");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd eax, ebx, 17");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd eax, ebx, 31");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd eax, ebx, 32");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd eax, ebx, 33");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd eax, ebx, 63");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd eax, ebx, 64");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd eax, ebx, 65");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd eax, ebx, 80");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd eax, ebx, 81");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd eax, ebx, 126");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd eax, ebx, 127");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd eax, ebx, 128");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd eax, ebx, 255");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd ax, bx, 0");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd ax, bx, 1");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd ax, bx, 2");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd ax, bx, 3");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd ax, bx, 4");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd ax, bx, 5");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd ax, bx, 15");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd ax, bx, 16");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd ax, bx, 17");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd ax, bx, 31");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd ax, bx, 32");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd ax, bx, 33");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd ax, bx, 63");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd ax, bx, 64");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd ax, bx, 65");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd ax, bx, 80");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd ax, bx, 81");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd ax, bx, 126");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd ax, bx, 127");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd ax, bx, 128");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("shrd ax, bx, 255");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 0");
  asm("shrx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 1");
  asm("shrx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 2");
  asm("shrx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 3");
  asm("shrx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 30");
  asm("shrx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 31");
  asm("shrx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 32");
  asm("shrx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 33");
  asm("shrx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 34");
  asm("shrx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 63");
  asm("shrx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 64");
  asm("shrx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 65");
  asm("shrx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 66");
  asm("shrx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 255");
  asm("shrx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 0");
  asm("shrx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 1");
  asm("shrx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 2");
  asm("shrx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 3");
  asm("shrx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 30");
  asm("shrx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 31");
  asm("shrx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 32");
  asm("shrx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 33");
  asm("shrx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 34");
  asm("shrx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 63");
  asm("shrx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 64");
  asm("shrx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 65");
  asm("shrx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 66");
  asm("shrx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 255");
  asm("shrx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 0");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 1");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 2");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 3");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 30");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 31");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 32");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 33");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 34");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 63");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 64");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 65");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 66");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 255");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 0");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 1");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 2");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 3");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 30");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 31");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 32");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 33");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 34");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 63");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 64");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 65");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 66");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 255");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 0");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 1");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 2");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 3");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 30");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 31");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 32");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 33");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 34");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 63");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 64");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 65");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 66");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 255");
  asm("sarx rax, rbx, rcx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 0");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 1");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 2");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 3");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 30");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 31");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 32");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 33");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 34");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 63");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 64");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 65");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 66");
  asm("sarx eax, ebx, ecx");

  asm("mov rax, 0x8123456789abcdef");
  asm("mov rbx, 0x8123456789abcdef");
  asm("mov rcx, 255");
  asm("sarx eax, ebx, ecx");

  asm("mov rdx, 0x0123456789abcdef");
  asm("mov rcx, 0x9828375823742870");
  asm("mulx rax, rbx, rcx");

  asm("mov rdx, 0x1975823253642738");
  asm("mov rcx, 0xffffffffffffffff");
  asm("mulx rax, rbx, rcx");

  asm("mov rdx, 0x8975823253642738");
  asm("mov rcx, 0xffffffffffffffff");
  asm("mulx rax, rbx, rcx");

  asm("mov rdx, 0xffffffffffffffff");
  asm("mov rcx, 0xffffffffffffffff");
  asm("mulx rax, rbx, rcx");

  asm("mov rdx, 0x0");
  asm("mov rcx, 0xffffffffffffffff");
  asm("mulx rax, rbx, rcx");

  asm("mov rdx, 0xffffffffffffffff");
  asm("mov rcx, 0x0");
  asm("mulx rax, rbx, rcx");

  asm("mov rdx, 0x0123456789abcdef");
  asm("mov rcx, 0x9828375823742870");
  asm("mulx eax, ebx, ecx");

  asm("mov rdx, 0x1975823253642738");
  asm("mov rcx, 0xffffffffffffffff");
  asm("mulx eax, ebx, ecx");

  asm("mov rdx, 0x8975823253642738");
  asm("mov rcx, 0xffffffffffffffff");
  asm("mulx eax, ebx, ecx");

  asm("mov rdx, 0xffffffffffffffff");
  asm("mov rcx, 0xffffffffffffffff");
  asm("mulx eax, ebx, ecx");

  asm("mov rdx, 0x0");
  asm("mov rcx, 0xffffffffffffffff");
  asm("mulx eax, ebx, ecx");

  asm("mov rdx, 0xffffffffffffffff");
  asm("mov rcx, 0x0");
  asm("mulx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 0");
  asm("shlx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 1");
  asm("shlx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 2");
  asm("shlx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 3");
  asm("shlx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 30");
  asm("shlx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 31");
  asm("shlx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 32");
  asm("shlx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 33");
  asm("shlx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 34");
  asm("shlx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 63");
  asm("shlx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 64");
  asm("shlx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 65");
  asm("shlx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 66");
  asm("shlx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 255");
  asm("shlx rax, rbx, rcx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 0");
  asm("shlx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 1");
  asm("shlx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 2");
  asm("shlx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 3");
  asm("shlx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 30");
  asm("shlx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 31");
  asm("shlx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 32");
  asm("shlx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 33");
  asm("shlx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 34");
  asm("shlx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 63");
  asm("shlx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 64");
  asm("shlx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 65");
  asm("shlx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 66");
  asm("shlx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("mov rcx, 255");
  asm("shlx eax, ebx, ecx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx rax, rbx, 0");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx rax, rbx, 1");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx rax, rbx, 2");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx rax, rbx, 3");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx rax, rbx, 30");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx rax, rbx, 31");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx rax, rbx, 32");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx rax, rbx, 33");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx rax, rbx, 34");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx rax, rbx, 63");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx rax, rbx, 64");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx rax, rbx, 65");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx rax, rbx, 66");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx rax, rbx, 255");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx eax, ebx, 0");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx eax, ebx, 1");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx eax, ebx, 2");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx eax, ebx, 3");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx eax, ebx, 30");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx eax, ebx, 31");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx eax, ebx, 32");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx eax, ebx, 33");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx eax, ebx, 34");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx eax, ebx, 63");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx eax, ebx, 64");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx eax, ebx, 65");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx eax, ebx, 66");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("rorx eax, ebx, 255");

  asm("mov rdx, 0x0123456789abcdef");
  asm("shr edx, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shr edx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shr edx");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shr edx, 31");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shr edx, 32");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shr edx, 33");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 31");
  asm("shr edx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 32");
  asm("shr edx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 33");
  asm("shr edx, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("shr dx, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shr dx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shr dx");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shr dx, 15");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shr dx, 16");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shr dx, 17");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 15");
  asm("shr dx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 16");
  asm("shr dx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 17");
  asm("shr dx, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("shr dh, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shr dh, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shr dh");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shr dh, 7");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shr dh, 8");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shr dh, 9");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 7");
  asm("shr dh, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 8");
  asm("shr dh, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 9");
  asm("shr dh, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("shr dl, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shr dl, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shr dl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shr dl, 7");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shr dl, 8");
  asm("mov rdx, 0x0123456789abcdef");
  asm("shr dl, 9");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 7");
  asm("shr dl, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 8");
  asm("shr dl, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 9");
  asm("shr dl, cl");

  asm("mov rdx, 0x1234567800000000");
  asm("sar rdx, 0");
  asm("mov rdx, 0x1234567800000000");
  asm("sar rdx, cl");
  asm("mov rdx, 0x1234567800000000");
  asm("sar rdx");
  asm("mov rdx, 0x1234567800000000");
  asm("sar rdx, 63");
  asm("mov rdx, 0x1234567800000000");
  asm("sar rdx, 64");
  asm("mov rdx, 0x1234567800000000");
  asm("sar rdx, 65");
  asm("mov cl, 63");
  asm("sar rdx, cl");
  asm("mov rdx, 0x1234567800000000");
  asm("mov cl, 64");
  asm("sar rdx, cl");
  asm("mov rdx, 0x1234567800000000");
  asm("mov cl, 65");
  asm("sar rdx, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("sar edx, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("sar edx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("sar edx");
  asm("mov rdx, 0x0123456789abcdef");
  asm("sar edx, 31");
  asm("mov rdx, 0x0123456789abcdef");
  asm("sar edx, 32");
  asm("mov rdx, 0x0123456789abcdef");
  asm("sar edx, 33");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 31");
  asm("sar edx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 32");
  asm("sar edx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 33");
  asm("sar edx, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("sar dx, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("sar dx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("sar dx");
  asm("mov rdx, 0x0123456789abcdef");
  asm("sar dx, 15");
  asm("mov rdx, 0x0123456789abcdef");
  asm("sar dx, 16");
  asm("mov rdx, 0x0123456789abcdef");
  asm("sar dx, 17");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 15");
  asm("sar dx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 16");
  asm("sar dx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 17");
  asm("sar dx, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("sar dh, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("sar dh, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("sar dh");
  asm("mov rdx, 0x0123456789abcdef");
  asm("sar dh, 7");
  asm("mov rdx, 0x0123456789abcdef");
  asm("sar dh, 8");
  asm("mov rdx, 0x0123456789abcdef");
  asm("sar dh, 9");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 7");
  asm("sar dh, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 8");
  asm("sar dh, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 9");
  asm("sar dh, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("sar dl, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("sar dl, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("sar dl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("sar dl, 7");
  asm("mov rdx, 0x0123456789abcdef");
  asm("sar dl, 8");
  asm("mov rdx, 0x0123456789abcdef");
  asm("sar dl, 9");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 7");
  asm("sar dl, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 8");
  asm("sar dl, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 9");
  asm("sar dl, cl");

  asm("mov rdx, 0x12345678");
  asm("rcl rdx, 0");
  asm("mov rdx, 0x12345678");
  asm("rcl rdx, cl");
  asm("mov rdx, 0x12345678");
  asm("rcl rdx");
  asm("mov rdx, 0x12345678");
  asm("rcl rdx, 63");
  asm("mov rdx, 0x12345678");
  asm("rcl rdx, 64");
  asm("mov rdx, 0x12345678");
  asm("rcl rdx, 65");
  asm("mov rdx, 0x12345678");
  asm("mov cl, 63");
  asm("rcl rdx, cl");
  asm("mov rdx, 0x12345678");
  asm("mov cl, 64");
  asm("rcl rdx, cl");
  asm("mov rdx, 0x12345678");
  asm("mov cl, 65");
  asm("rcl rdx, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("rcl edx, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcl edx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcl edx");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcl edx, 31");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcl edx, 32");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcl edx, 33");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 31");
  asm("rcl edx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 32");
  asm("rcl edx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 33");
  asm("rcl edx, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("rcl dx, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcl dx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcl dx");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcl dx, 15");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcl dx, 16");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcl dx, 17");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 15");
  asm("rcl dx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 16");
  asm("rcl dx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 17");
  asm("rcl dx, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("rcl dh, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcl dh, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcl dh");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcl dh, 7");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcl dh, 8");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcl dh, 9");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 7");
  asm("rcl dh, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 8");
  asm("rcl dh, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 9");
  asm("rcl dh, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("rcl dl, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcl dl, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcl dl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcl dl, 7");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcl dl, 8");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcl dl, 9");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 7");
  asm("rcl dl, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 8");
  asm("rcl dl, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 9");
  asm("rcl dl, cl");

  asm("mov rdx, 0x12345678");
  asm("rcr rdx, 0");
  asm("mov rdx, 0x12345678");
  asm("rcr rdx, cl");
  asm("mov rdx, 0x12345678");
  asm("rcr rdx");
  asm("mov rdx, 0x12345678");
  asm("rcr rdx, 63");
  asm("mov rdx, 0x12345678");
  asm("rcr rdx, 64");
  asm("mov rdx, 0x12345678");
  asm("rcr rdx, 65");
  asm("mov rdx, 0x12345678");
  asm("mov cl, 63");
  asm("rcr rdx, cl");
  asm("mov rdx, 0x12345678");
  asm("mov cl, 64");
  asm("rcr rdx, cl");
  asm("mov rdx, 0x12345678");
  asm("mov cl, 65");
  asm("rcr rdx, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("rcr edx, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcr edx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcr edx");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcr edx, 31");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcr edx, 32");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcr edx, 33");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 31");
  asm("rcr edx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 32");
  asm("rcr edx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 33");
  asm("rcr edx, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("rcr dx, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcr dx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcr dx");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcr dx, 15");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcr dx, 16");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcr dx, 17");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 15");
  asm("rcr dx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 16");
  asm("rcr dx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 17");
  asm("rcr dx, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("rcr dh, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcr dh, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcr dh");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcr dh, 7");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcr dh, 8");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcr dh, 9");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 7");
  asm("rcr dh, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 8");
  asm("rcr dh, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 9");
  asm("rcr dh, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("rcr dl, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcr dl, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcr dl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcr dl, 7");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcr dl, 8");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rcr dl, 9");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 7");
  asm("rcr dl, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 8");
  asm("rcr dl, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 9");
  asm("rcr dl, cl");

  asm("mov rdx, 0x12345678");
  asm("rol rdx, 0");
  asm("mov rdx, 0x12345678");
  asm("rol rdx, cl");
  asm("mov rdx, 0x12345678");
  asm("rol rdx");
  asm("mov rdx, 0x12345678");
  asm("rol rdx, 63");
  asm("mov rdx, 0x12345678");
  asm("rol rdx, 64");
  asm("mov rdx, 0x12345678");
  asm("rol rdx, 65");
  asm("mov rdx, 0x12345678");
  asm("mov cl, 63");
  asm("rol rdx, cl");
  asm("mov rdx, 0x12345678");
  asm("mov cl, 64");
  asm("rol rdx, cl");
  asm("mov rdx, 0x12345678");
  asm("mov cl, 65");
  asm("rol rdx, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("rol edx, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rol edx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rol edx");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rol edx, 31");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rol edx, 32");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rol edx, 33");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 31");
  asm("rol edx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 32");
  asm("rol edx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 33");
  asm("rol edx, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("rol dx, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rol dx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rol dx");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rol dx, 15");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rol dx, 16");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rol dx, 17");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 15");
  asm("rol dx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 16");
  asm("rol dx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 17");
  asm("rol dx, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("rol dh, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rol dh, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rol dh");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rol dh, 7");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rol dh, 8");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rol dh, 9");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 7");
  asm("rol dh, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 8");
  asm("rol dh, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 9");
  asm("rol dh, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("rol dl, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rol dl, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rol dl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rol dl, 7");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rol dl, 8");
  asm("mov rdx, 0x0123456789abcdef");
  asm("rol dl, 9");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 7");
  asm("rol dl, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 8");
  asm("rol dl, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 9");
  asm("rol dl, cl");

  asm("mov rdx, 0x12345678");
  asm("ror rdx, 0");
  asm("mov rdx, 0x12345678");
  asm("ror rdx, cl");
  asm("mov rdx, 0x12345678");
  asm("ror rdx");
  asm("mov rdx, 0x12345678");
  asm("ror rdx, 63");
  asm("mov rdx, 0x12345678");
  asm("ror rdx, 64");
  asm("mov rdx, 0x12345678");
  asm("ror rdx, 65");
  asm("mov rdx, 0x12345678");
  asm("mov cl, 63");
  asm("ror rdx, cl");
  asm("mov rdx, 0x12345678");
  asm("mov cl, 64");
  asm("ror rdx, cl");
  asm("mov rdx, 0x12345678");
  asm("mov cl, 65");
  asm("ror rdx, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("ror edx, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("ror edx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("ror edx");
  asm("mov rdx, 0x0123456789abcdef");
  asm("ror edx, 31");
  asm("mov rdx, 0x0123456789abcdef");
  asm("ror edx, 32");
  asm("mov rdx, 0x0123456789abcdef");
  asm("ror edx, 33");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 31");
  asm("ror edx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 32");
  asm("ror edx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 33");
  asm("ror edx, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("ror dx, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("ror dx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("ror dx");
  asm("mov rdx, 0x0123456789abcdef");
  asm("ror dx, 15");
  asm("mov rdx, 0x0123456789abcdef");
  asm("ror dx, 16");
  asm("mov rdx, 0x0123456789abcdef");
  asm("ror dx, 17");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 15");
  asm("ror dx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 16");
  asm("ror dx, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 17");
  asm("ror dx, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("ror dh, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("ror dh, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("ror dh");
  asm("mov rdx, 0x0123456789abcdef");
  asm("ror dh, 7");
  asm("mov rdx, 0x0123456789abcdef");
  asm("ror dh, 8");
  asm("mov rdx, 0x0123456789abcdef");
  asm("ror dh, 9");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 7");
  asm("ror dh, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 8");
  asm("ror dh, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 9");
  asm("ror dh, cl");

  asm("mov rdx, 0x0123456789abcdef");
  asm("ror dl, 0");
  asm("mov rdx, 0x0123456789abcdef");
  asm("ror dl, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("ror dl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("ror dl, 7");
  asm("mov rdx, 0x0123456789abcdef");
  asm("ror dl, 8");
  asm("mov rdx, 0x0123456789abcdef");
  asm("ror dl, 9");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 7");
  asm("ror dl, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 8");
  asm("ror dl, cl");
  asm("mov rdx, 0x0123456789abcdef");
  asm("mov cl, 9");
  asm("ror dl, cl");

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

  asm("adcx rax, rbx");
  asm("adcx rcx, rax");
  asm("adcx rdx, rcx");
  asm("adcx rdi, rdx");

  asm("adcx eax, ebx");
  asm("adcx ecx, eax");
  asm("adcx edx, ecx");
  asm("adcx edi, edx");

  asm("adcx rax, rbx");
  asm("adcx rcx, rax");
  asm("adcx rdx, rcx");
  asm("adcx rdi, rdx");
  asm("adcx rbx, rdi");

  asm("adcx rax, rbx");
  asm("adcx rcx, rax");
  asm("adcx rdx, rcx");
  asm("adcx rdi, rdx");
  asm("adcx rbx, rdi");

  asm("adcx rax, rbx");
  asm("adcx rcx, rax");
  asm("adcx rdx, rcx");
  asm("adcx rdi, rdx");
  asm("adcx rbx, rdi");

  asm("adcx rax, rbx");
  asm("adcx rcx, rax");
  asm("adcx rdx, rcx");
  asm("adcx rdi, rdx");
  asm("adcx rbx, rdi");

  init(tab1, tab2, tab3, tab4, tab5, tab6, tab7, tab8);

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

  asm("movlpd xmm1, qword ptr [%0]" :: "r"(tab1));
  asm("movlps xmm2, qword ptr [%0]" :: "r"(tab2));
  asm("movhpd xmm3, qword ptr [%0]" :: "r"(tab3));
  asm("movhps xmm4, qword ptr [%0]" :: "r"(tab4));

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

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("andn rcx, rax, rbx");

  asm("mov rax, 0x1824671246812731");
  asm("mov rbx, 0x7162738189475322");
  asm("andn rcx, rax, rbx");

  asm("mov rax, 0x8236543983945734");
  asm("mov rbx, 0x9894568734758341");
  asm("andn rcx, rax, rbx");

  asm("mov rax, 0x0000000000000000");
  asm("mov rbx, 0x0000000000000000");
  asm("andn rcx, rax, rbx");

  asm("mov rax, 0x0000000000000001");
  asm("mov rbx, 0x0000000000000000");
  asm("andn rcx, rax, rbx");

  asm("mov rax, 0x0000000000000000");
  asm("mov rbx, 0x0000000000000001");
  asm("andn rcx, rax, rbx");

  asm("mov rax, 0x7fffffffffffffff");
  asm("mov rbx, 0x0000000000000001");
  asm("andn rcx, rax, rbx");

  asm("mov rax, 0x0000000000000001");
  asm("mov rbx, 0x7fffffffffffffff");
  asm("andn rcx, rax, rbx");

  asm("mov rax, 0x0000000000000000");
  asm("mov rbx, 0x7fffffffffffffff");
  asm("andn rcx, rax, rbx");

  asm("mov rax, 0x8000000000000000");
  asm("mov rbx, 0x7fffffffffffffff");
  asm("andn rcx, rax, rbx");

  asm("mov rax, 0x0123456789abcdef");
  asm("mov rbx, 0x0123456789abcdef");
  asm("bextr rcx, rax, rbx");

  asm("mov rax, 0x1824671246812731");
  asm("mov rbx, 0x7162738189475322");
  asm("bextr rcx, rax, rbx");

  asm("mov rax, 0x8236543983945734");
  asm("mov rbx, 0x9894568734758341");
  asm("bextr rcx, rax, rbx");

  asm("mov rax, 0x0000000000000000");
  asm("mov rbx, 0x0000000000000000");
  asm("bextr rcx, rax, rbx");

  asm("mov rax, 0x0000000000000001");
  asm("mov rbx, 0x0000000000000000");
  asm("bextr rcx, rax, rbx");

  asm("mov rax, 0x0000000000000000");
  asm("mov rbx, 0x0000000000000001");
  asm("bextr rcx, rax, rbx");

  asm("mov rax, 0x7fffffffffffffff");
  asm("mov rbx, 0x0000000000000001");
  asm("bextr rcx, rax, rbx");

  asm("mov rax, 0x0000000000000001");
  asm("mov rbx, 0x7fffffffffffffff");
  asm("bextr rcx, rax, rbx");

  asm("mov rax, 0x0000000000000000");
  asm("mov rbx, 0x7fffffffffffffff");
  asm("bextr rcx, rax, rbx");

  asm("mov rax, 0x8000000000000000");
  asm("mov rbx, 0x7fffffffffffffff");
  asm("bextr rcx, rax, rbx");

  asm("mov rax, 0x8236543983945734");
  asm("mov rbx, 0x0000000000000005");
  asm("bextr rcx, rax, rbx");

  asm("mov rax, 0x8236543983945734");
  asm("mov rbx, 0x0000000000000055");
  asm("bextr rcx, rax, rbx");

  asm("mov rax, 0x8236543983945734");
  asm("mov rbx, 0x0000000000000555");
  asm("bextr rcx, rax, rbx");

  asm("mov rax, 0x8236543983945734");
  asm("mov rbx, 0x0000000000005555");
  asm("bextr rcx, rax, rbx");

  asm("mov rax, 0x8236543983945734");
  asm("mov rbx, 0x00000000000055555");
  asm("bextr rcx, rax, rbx");

  asm("mov rax, 0x8236543983945734");
  asm("mov rbx, 0x00000000000555555");
  asm("bextr rcx, rax, rbx");

  asm("mov rax, 0x0123456789abcdef");
  asm("blsi rcx, rax");

  asm("mov rax, 0x0000000000000000");
  asm("blsi rcx, rax");

  asm("mov rax, 0x0000000000000001");
  asm("blsi rcx, rax");

  asm("mov rax, 0x1000000000000001");
  asm("blsi rcx, rax");

  asm("mov rax, 0x8000000000000001");
  asm("blsi rcx, rax");

  asm("mov rax, 0x8000000000000000");
  asm("blsi rcx, rax");

  asm("mov rax, 0x7fffffffffffffff");
  asm("blsi rcx, rax");

  asm("mov rax, 0xffffffffffffffff");
  asm("blsi rcx, rax");

  asm("mov rax, 0xfffffffffffffffe");
  asm("blsi rcx, rax");

  asm("mov rax, 0x2364782365872361");
  asm("blsi rcx, rax");

  asm("mov rax, 0x9283742734823772");
  asm("blsi rcx, rax");

  asm("mov rax, 0x0123456789abcdef");
  asm("blsmsk rcx, rax");

  asm("mov rax, 0x0000000000000000");
  asm("blsmsk rcx, rax");

  asm("mov rax, 0x0000000000000001");
  asm("blsmsk rcx, rax");

  asm("mov rax, 0x1000000000000001");
  asm("blsmsk rcx, rax");

  asm("mov rax, 0x8000000000000001");
  asm("blsmsk rcx, rax");

  asm("mov rax, 0x8000000000000000");
  asm("blsmsk rcx, rax");

  asm("mov rax, 0x7fffffffffffffff");
  asm("blsmsk rcx, rax");

  asm("mov rax, 0xffffffffffffffff");
  asm("blsmsk rcx, rax");

  asm("mov rax, 0xfffffffffffffffe");
  asm("blsmsk rcx, rax");

  asm("mov rax, 0x2364782365872361");
  asm("blsmsk rcx, rax");

  asm("mov rax, 0x9283742734823772");
  asm("blsmsk rcx, rax");

  asm("mov rax, 0x0123456789abcdef");
  asm("blsr rcx, rax");

  asm("mov rax, 0x0000000000000000");
  asm("blsr rcx, rax");

  asm("mov rax, 0x0000000000000001");
  asm("blsr rcx, rax");

  asm("mov rax, 0x1000000000000001");
  asm("blsr rcx, rax");

  asm("mov rax, 0x8000000000000001");
  asm("blsr rcx, rax");

  asm("mov rax, 0x8000000000000000");
  asm("blsr rcx, rax");

  asm("mov rax, 0x7fffffffffffffff");
  asm("blsr rcx, rax");

  asm("mov rax, 0xffffffffffffffff");
  asm("blsr rcx, rax");

  asm("mov rax, 0xfffffffffffffffe");
  asm("blsr rcx, rax");

  asm("mov rax, 0x2364782365872361");
  asm("blsr rcx, rax");

  asm("mov rax, 0x9283742734823772");
  asm("blsr rcx, rax");

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

  asm("pshufd xmm1, xmm2, 1");
  asm("pshufd xmm2, xmm3, 2");
  asm("pshufd xmm2, xmm3, 3");
  asm("pshufd xmm1, xmm4, 4");
  asm("pshufd xmm3, xmm1, 5");
  asm("pshufd xmm1, xmm2, 0x10");
  asm("pshufd xmm2, xmm3, 0x20");
  asm("pshufd xmm2, xmm3, 0x40");
  asm("pshufd xmm1, xmm4, 0xff");
  asm("pshufd xmm3, xmm1, 0xaa");

  asm("lddqu xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("lddqu xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("lddqu xmm3, xmmword ptr [%0]" :: "r"(tab3));
  asm("lddqu xmm4, xmmword ptr [%0]" :: "r"(tab4));

  asm("pshufhw xmm1, xmm2, 1");
  asm("pshufhw xmm2, xmm3, 2");
  asm("pshufhw xmm2, xmm3, 3");
  asm("pshufhw xmm1, xmm4, 4");
  asm("pshufhw xmm3, xmm1, 5");
  asm("pshufhw xmm1, xmm2, 0x10");
  asm("pshufhw xmm2, xmm3, 0x20");
  asm("pshufhw xmm2, xmm3, 0x40");
  asm("pshufhw xmm1, xmm4, 0xff");
  asm("pshufhw xmm3, xmm1, 0xaa");

  asm("lddqu xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("lddqu xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("lddqu xmm3, xmmword ptr [%0]" :: "r"(tab3));
  asm("lddqu xmm4, xmmword ptr [%0]" :: "r"(tab4));

  asm("pshuflw xmm1, xmm2, 1");
  asm("pshuflw xmm2, xmm3, 2");
  asm("pshuflw xmm2, xmm3, 3");
  asm("pshuflw xmm1, xmm4, 4");
  asm("pshuflw xmm3, xmm1, 5");
  asm("pshuflw xmm1, xmm2, 0x10");
  asm("pshuflw xmm2, xmm3, 0x20");
  asm("pshuflw xmm2, xmm3, 0x40");
  asm("pshuflw xmm1, xmm4, 0xff");
  asm("pshuflw xmm3, xmm1, 0xaa");

  asm("lddqu xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("lddqu xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("lddqu xmm3, xmmword ptr [%0]" :: "r"(tab3));
  asm("lddqu xmm4, xmmword ptr [%0]" :: "r"(tab4));

  asm("pminub xmm1, xmm2");
  asm("pminub xmm2, xmm3");
  asm("pminub xmm3, xmm4");
  asm("pminub xmm4, xmm1");
  asm("pminub xmm1, xmm1");
  asm("pminub xmm2, xmm3");
  asm("pminub xmm3, xmm4");
  asm("pminub xmm4, xmm1");
  asm("pminub xmm4, xmm4");

  asm("pmaxub xmm1, xmm3");
  asm("pmaxub xmm2, xmm4");
  asm("pmaxub xmm3, xmm1");
  asm("pmaxub xmm4, xmm2");
  asm("pmaxub xmm1, xmm1");
  asm("pmaxub xmm2, xmm4");
  asm("pmaxub xmm4, xmm3");
  asm("pmaxub xmm4, xmm2");
  asm("pmaxub xmm4, xmm4");

  asm("pminsb xmm1, xmm2");
  asm("pminsb xmm2, xmm3");
  asm("pminsb xmm3, xmm4");
  asm("pminsb xmm4, xmm1");
  asm("pminsb xmm1, xmm1");
  asm("pminsb xmm2, xmm3");
  asm("pminsb xmm3, xmm4");
  asm("pminsb xmm4, xmm1");
  asm("pminsb xmm4, xmm4");

  asm("pmaxsb xmm1, xmm3");
  asm("pmaxsb xmm2, xmm4");
  asm("pmaxsb xmm3, xmm1");
  asm("pmaxsb xmm4, xmm2");
  asm("pmaxsb xmm1, xmm1");
  asm("pmaxsb xmm2, xmm4");
  asm("pmaxsb xmm4, xmm3");
  asm("pmaxsb xmm4, xmm2");
  asm("pmaxsb xmm4, xmm4");

  asm("pminuw xmm1, xmm2");
  asm("pminuw xmm2, xmm3");
  asm("pminuw xmm3, xmm4");
  asm("pminuw xmm4, xmm1");
  asm("pminuw xmm1, xmm1");
  asm("pminuw xmm2, xmm3");
  asm("pminuw xmm3, xmm4");
  asm("pminuw xmm4, xmm1");
  asm("pminuw xmm4, xmm4");

  asm("pmaxuw xmm1, xmm3");
  asm("pmaxuw xmm2, xmm4");
  asm("pmaxuw xmm3, xmm1");
  asm("pmaxuw xmm4, xmm2");
  asm("pmaxuw xmm1, xmm1");
  asm("pmaxuw xmm2, xmm4");
  asm("pmaxuw xmm4, xmm3");
  asm("pmaxuw xmm4, xmm2");
  asm("pmaxuw xmm4, xmm4");

  asm("pminsw xmm1, xmm2");
  asm("pminsw xmm2, xmm3");
  asm("pminsw xmm3, xmm4");
  asm("pminsw xmm4, xmm1");
  asm("pminsw xmm1, xmm1");
  asm("pminsw xmm2, xmm3");
  asm("pminsw xmm3, xmm4");
  asm("pminsw xmm4, xmm1");
  asm("pminsw xmm4, xmm4");

  asm("pmaxsw xmm1, xmm3");
  asm("pmaxsw xmm2, xmm4");
  asm("pmaxsw xmm3, xmm1");
  asm("pmaxsw xmm4, xmm2");
  asm("pmaxsw xmm1, xmm1");
  asm("pmaxsw xmm2, xmm4");
  asm("pmaxsw xmm4, xmm3");
  asm("pmaxsw xmm4, xmm2");
  asm("pmaxsw xmm4, xmm4");

  asm("pminud xmm1, xmm2");
  asm("pminud xmm2, xmm3");
  asm("pminud xmm3, xmm4");
  asm("pminud xmm4, xmm1");
  asm("pminud xmm1, xmm1");
  asm("pminud xmm2, xmm3");
  asm("pminud xmm3, xmm4");
  asm("pminud xmm4, xmm1");
  asm("pminud xmm4, xmm4");

  asm("pmaxud xmm1, xmm3");
  asm("pmaxud xmm2, xmm4");
  asm("pmaxud xmm3, xmm1");
  asm("pmaxud xmm4, xmm2");
  asm("pmaxud xmm1, xmm1");
  asm("pmaxud xmm2, xmm4");
  asm("pmaxud xmm4, xmm3");
  asm("pmaxud xmm4, xmm2");
  asm("pmaxud xmm4, xmm4");

  asm("pminsd xmm1, xmm2");
  asm("pminsd xmm2, xmm3");
  asm("pminsd xmm3, xmm4");
  asm("pminsd xmm4, xmm1");
  asm("pminsd xmm1, xmm1");
  asm("pminsd xmm2, xmm3");
  asm("pminsd xmm3, xmm4");
  asm("pminsd xmm4, xmm1");
  asm("pminsd xmm4, xmm4");

  asm("pmaxsd xmm1, xmm3");
  asm("pmaxsd xmm2, xmm4");
  asm("pmaxsd xmm3, xmm1");
  asm("pmaxsd xmm4, xmm2");
  asm("pmaxsd xmm1, xmm1");
  asm("pmaxsd xmm2, xmm4");
  asm("pmaxsd xmm4, xmm3");
  asm("pmaxsd xmm4, xmm2");
  asm("pmaxsd xmm4, xmm4");

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

  init(tab1, tab2, tab3, tab4, tab5, tab6, tab7, tab8);
  asm("lddqu xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("lddqu xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("lddqu xmm3, xmmword ptr [%0]" :: "r"(tab3));
  asm("lddqu xmm4, xmmword ptr [%0]" :: "r"(tab4));

  asm("pmovsxbw xmm5, xmm1");
  asm("pmovsxbw xmm5, xmm2");
  asm("pmovsxbw xmm5, xmm3");
  asm("pmovsxbw xmm5, xmm4");

  asm("pmovzxbw xmm5, xmm1");
  asm("pmovzxbw xmm5, xmm2");
  asm("pmovzxbw xmm5, xmm3");
  asm("pmovzxbw xmm5, xmm4");

  asm("pmovsxbd xmm5, xmm1");
  asm("pmovsxbd xmm5, xmm2");
  asm("pmovsxbd xmm5, xmm3");
  asm("pmovsxbd xmm5, xmm4");

  asm("pmovzxbd xmm5, xmm1");
  asm("pmovzxbd xmm5, xmm2");
  asm("pmovzxbd xmm5, xmm3");
  asm("pmovzxbd xmm5, xmm4");

  asm("pmovsxbq xmm5, xmm1");
  asm("pmovsxbq xmm5, xmm2");
  asm("pmovsxbq xmm5, xmm3");
  asm("pmovsxbq xmm5, xmm4");

  asm("pmovzxbq xmm5, xmm1");
  asm("pmovzxbq xmm5, xmm2");
  asm("pmovzxbq xmm5, xmm3");
  asm("pmovzxbq xmm5, xmm4");

  asm("pmovsxwd xmm5, xmm1");
  asm("pmovsxwd xmm5, xmm2");
  asm("pmovsxwd xmm5, xmm3");
  asm("pmovsxwd xmm5, xmm4");

  asm("pmovzxwd xmm5, xmm1");
  asm("pmovzxwd xmm5, xmm2");
  asm("pmovzxwd xmm5, xmm3");
  asm("pmovzxwd xmm5, xmm4");

  asm("pmovsxwq xmm5, xmm1");
  asm("pmovsxwq xmm5, xmm2");
  asm("pmovsxwq xmm5, xmm3");
  asm("pmovsxwq xmm5, xmm4");

  asm("pmovzxwq xmm5, xmm1");
  asm("pmovzxwq xmm5, xmm2");
  asm("pmovzxwq xmm5, xmm3");
  asm("pmovzxwq xmm5, xmm4");

  asm("pmovsxdq xmm5, xmm1");
  asm("pmovsxdq xmm5, xmm2");
  asm("pmovsxdq xmm5, xmm3");
  asm("pmovsxdq xmm5, xmm4");

  asm("pmovzxdq xmm5, xmm1");
  asm("pmovzxdq xmm5, xmm2");
  asm("pmovzxdq xmm5, xmm3");
  asm("pmovzxdq xmm5, xmm4");

  asm("extractps rax, xmm1, 0");
  asm("extractps rax, xmm1, 1");
  asm("extractps rax, xmm1, 2");
  asm("extractps rax, xmm1, 3");
  asm("extractps rax, xmm1, 4");
  asm("extractps rax, xmm2, 0");
  asm("extractps rax, xmm2, 1");
  asm("extractps rax, xmm2, 2");
  asm("extractps rax, xmm2, 3");
  asm("extractps rax, xmm2, 4");
  asm("extractps rax, xmm3, 0");
  asm("extractps rax, xmm3, 1");
  asm("extractps rax, xmm3, 2");
  asm("extractps rax, xmm3, 3");
  asm("extractps rax, xmm3, 4");
  asm("extractps rax, xmm4, 0");
  asm("extractps rax, xmm4, 1");
  asm("extractps rax, xmm4, 2");
  asm("extractps rax, xmm4, 3");
  asm("extractps rax, xmm4, 4");

  asm("extractps edx, xmm1, 0");
  asm("extractps edx, xmm1, 1");
  asm("extractps edx, xmm1, 2");
  asm("extractps edx, xmm1, 3");
  asm("extractps edx, xmm1, 4");
  asm("extractps edx, xmm2, 0");
  asm("extractps edx, xmm2, 1");
  asm("extractps edx, xmm2, 2");
  asm("extractps edx, xmm2, 3");
  asm("extractps edx, xmm2, 4");
  asm("extractps edx, xmm3, 0");
  asm("extractps edx, xmm3, 1");
  asm("extractps edx, xmm3, 2");
  asm("extractps edx, xmm3, 3");
  asm("extractps edx, xmm3, 4");
  asm("extractps edx, xmm4, 0");
  asm("extractps edx, xmm4, 1");
  asm("extractps edx, xmm4, 2");
  asm("extractps edx, xmm4, 3");
  asm("extractps edx, xmm4, 4");

  asm("pavgb xmm1, xmm1");
  asm("pavgb xmm1, xmm2");
  asm("pavgb xmm1, xmm3");
  asm("pavgb xmm1, xmm4");
  asm("pavgb xmm2, xmm1");
  asm("pavgb xmm2, xmm2");
  asm("pavgb xmm2, xmm3");
  asm("pavgb xmm2, xmm4");
  asm("pavgb xmm3, xmm1");
  asm("pavgb xmm3, xmm2");
  asm("pavgb xmm3, xmm3");
  asm("pavgb xmm3, xmm4");
  asm("pavgb xmm4, xmm1");
  asm("pavgb xmm4, xmm2");
  asm("pavgb xmm4, xmm3");
  asm("pavgb xmm4, xmm4");

  asm("pavgw xmm1, xmm1");
  asm("pavgw xmm1, xmm2");
  asm("pavgw xmm1, xmm3");
  asm("pavgw xmm1, xmm4");
  asm("pavgw xmm2, xmm1");
  asm("pavgw xmm2, xmm2");
  asm("pavgw xmm2, xmm3");
  asm("pavgw xmm2, xmm4");
  asm("pavgw xmm3, xmm1");
  asm("pavgw xmm3, xmm2");
  asm("pavgw xmm3, xmm3");
  asm("pavgw xmm3, xmm4");
  asm("pavgw xmm4, xmm1");
  asm("pavgw xmm4, xmm2");
  asm("pavgw xmm4, xmm3");
  asm("pavgw xmm4, xmm4");

  init(tab1, tab2, tab3, tab4, tab5, tab6, tab7, tab8);
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("vmovdqa xmm3, xmmword ptr [%0]" :: "r"(tab3));
  asm("vmovdqa xmm4, xmmword ptr [%0]" :: "r"(tab4));

  asm("vpor xmm1, xmm2, xmm3");
  asm("vpor xmm1, xmm1, xmm2");
  asm("vpor xmm1, xmm3, xmm4");

  asm("vpxor xmm2, xmm3, xmm3");
  asm("vpxor xmm2, xmm1, xmm3");
  asm("vpxor xmm2, xmm1, xmm4");

  asm("vpand xmm3, xmm1, xmm4");
  asm("vpand xmm3, xmm2, xmm2");
  asm("vpand xmm3, xmm3, xmm2");

  asm("vpandn xmm4, xmm3, xmm2");
  asm("vpandn xmm4, xmm2, xmm1");
  asm("vpandn xmm4, xmm2, xmm3");

  asm("vpshufd xmm1, xmm2, 1");
  asm("vpshufd xmm2, xmm3, 2");
  asm("vpshufd xmm2, xmm3, 3");
  asm("vpshufd xmm1, xmm4, 4");
  asm("vpshufd xmm3, xmm1, 5");
  asm("vpshufd xmm1, xmm2, 0x10");
  asm("vpshufd xmm2, xmm3, 0x20");
  asm("vpshufd xmm2, xmm3, 0x40");
  asm("vpshufd xmm1, xmm4, 0xff");
  asm("vpshufd xmm3, xmm1, 0xaa");

  init(utab1, utab2, utab3, utab4, tab5, tab6, tab7, tab8);
  asm("vmovdqu xmm1, xmmword ptr [%0]" :: "r"(utab1));
  asm("vmovdqu xmm2, xmmword ptr [%0]" :: "r"(utab2));
  asm("vmovdqu xmm3, xmmword ptr [%0]" :: "r"(utab3));
  asm("vmovdqu xmm4, xmmword ptr [%0]" :: "r"(utab4));

  asm("vpor xmm1, xmm2, xmm3");
  asm("vpor xmm1, xmm1, xmm2");
  asm("vpor xmm1, xmm3, xmm4");

  asm("vmovdqa xmm0, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab2));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab3));
  asm("vmovdqa xmm3, xmmword ptr [%0]" :: "r"(tab4));
  asm("vpmovmskb eax, xmm0");
  asm("vpmovmskb eax, xmm1");
  asm("vpmovmskb eax, xmm2");
  asm("vpmovmskb eax, xmm3");
  asm("vpmovmskb ecx, ymm0");
  asm("vpmovmskb ecx, ymm1");
  asm("vpmovmskb ecx, ymm2");
  asm("vpmovmskb ecx, ymm3");

  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("pslld xmm1, 0");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab2));
  asm("pslld xmm1, 8");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab3));
  asm("pslld xmm1, 31");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab4));
  asm("pslld xmm1, 32");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("pslld xmm1, 33");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab2));
  asm("pslld xmm1, 120");

  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("pslld xmm1, xmm2");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab2));
  asm("pslld xmm1, xmm2");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab3));
  asm("pslld xmm1, xmm2");

  asm("pslld xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("pslld xmm1, xmmword ptr [%0]" :: "r"(tab2));
  asm("pslld xmm1, xmmword ptr [%0]" :: "r"(tab3));
  asm("pslld xmm1, xmmword ptr [%0]" :: "r"(tab4));

  asm("pslld mm1, 1");
  asm("pslld mm1, 2");
  asm("pslld mm1, 3");

  asm("pslld mm1, mm1");
  asm("pslld mm1, mm2");
  asm("pslld mm1, mm3");

  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("psllw xmm1, 0");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab2));
  asm("psllw xmm1, 8");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab3));
  asm("psllw xmm1, 31");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab4));
  asm("psllw xmm1, 32");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("psllw xmm1, 33");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab2));
  asm("psllw xmm1, 120");

  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("psllw xmm1, xmm2");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab2));
  asm("psllw xmm1, xmm2");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab3));
  asm("psllw xmm1, xmm2");

  asm("psllw xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("psllw xmm1, xmmword ptr [%0]" :: "r"(tab2));
  asm("psllw xmm1, xmmword ptr [%0]" :: "r"(tab3));
  asm("psllw xmm1, xmmword ptr [%0]" :: "r"(tab4));

  asm("psllw mm1, 1");
  asm("psllw mm1, 2");
  asm("psllw mm1, 3");

  asm("psllw mm1, mm1");
  asm("psllw mm1, mm2");
  asm("psllw mm1, mm3");

  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("psllq xmm1, 0");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab2));
  asm("psllq xmm1, 8");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab3));
  asm("psllq xmm1, 31");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab4));
  asm("psllq xmm1, 32");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("psllq xmm1, 33");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab2));
  asm("psllq xmm1, 63");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab3));
  asm("psllq xmm1, 64");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab4));
  asm("psllq xmm1, 65");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("psllq xmm1, 120");

  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("psllq xmm1, xmm2");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab2));
  asm("psllq xmm1, xmm2");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab3));
  asm("psllq xmm1, xmm2");

  asm("psllq xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("psllq xmm1, xmmword ptr [%0]" :: "r"(tab2));
  asm("psllq xmm1, xmmword ptr [%0]" :: "r"(tab3));
  asm("psllq xmm1, xmmword ptr [%0]" :: "r"(tab4));

  asm("psllq mm1, 1");
  asm("psllq mm1, 2");
  asm("psllq mm1, 3");

  asm("psllq mm1, mm1");
  asm("psllq mm1, mm2");
  asm("psllq mm1, mm3");

  init(tab1, tab2, tab3, tab4, tab5, tab6, tab7, tab8);

  // movss
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("movss xmm1, xmm2");
  asm("movss xmm2, dword ptr [%0]" :: "r"(tab1));
  asm("movss dword ptr [%0], xmm2" :: "r"(tab2));

  init(tab1, tab2, tab3, tab4, tab5, tab6, tab7, tab8);

  // movbe
  asm("xor rbx, rbx");
  asm("movbe bx, word ptr [%0]" :: "r"(tab5));
  asm("xor rbx, rbx");
  asm("movbe ebx, dword ptr [%0]" :: "r"(tab5));
  asm("xor rbx, rbx");
  asm("movbe rbx, qword ptr [%0]" :: "r"(tab5));

  asm("mov qword ptr [%0], rbx" :: "r"(tab5));
  asm("movbe word ptr [%0], bx" :: "r"(tab1));
  asm("movbe dword ptr [%0], ebx" :: "r"(tab1));
  asm("movbe qword ptr [%0], rbx" :: "r"(tab1));

  init(tab1, tab2, tab3, tab4, tab5, tab6, tab7, tab8);

  // vpbroadcastb
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vpbroadcastb xmm2, xmm1");
  asm("vpbroadcastb xmm3, byte ptr [%0]" :: "r"(tab2));

  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vpbroadcastb ymm2, xmm1");
  asm("vpbroadcastb ymm3, byte ptr [%0]" :: "r"(tab2));

  // vpminub
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab2));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab3));
  asm("vpminub xmm3, xmm1, xmm2");
  asm("vpminub xmm4, xmm1, xmmword ptr [%0]" :: "r"(tab3));

  asm("vmovdqu ymm1, ymmword ptr [%0]" :: "r"(tab6));
  asm("vmovdqu ymm2, ymmword ptr [%0]" :: "r"(tab7));
  asm("vpminub ymm3, ymm1, ymm2");
  asm("vpminub ymm4, ymm1, ymmword ptr [%0]" :: "r"(tab7));

  // vpcmpeqb, vpcmpeqw, vpcmpeqd, vpcmpeqq
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm3, xmmword ptr [%0]" :: "r"(tab2));
  asm("vpcmpeqb xmm1, xmm2, xmm3");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab4));
  asm("vpcmpeqb xmm1, xmm3, xmmword ptr [%0]" :: "r"(tab3));

  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab4));
  asm("vpcmpeqw xmm1, xmm2, xmm3");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab4));
  asm("vpcmpeqw xmm1, xmm3, xmmword ptr [%0]" :: "r"(tab3));

  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab4));
  asm("vpcmpeqd xmm1, xmm2, xmm3");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab4));
  asm("vpcmpeqd xmm1, xmm3, xmmword ptr [%0]" :: "r"(tab3));

  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab4));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm3, xmmword ptr [%0]" :: "r"(tab6));
  asm("vpcmpeqq xmm1, xmm2, xmm3");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab4));
  asm("vpcmpeqq xmm1, xmm3, xmmword ptr [%0]" :: "r"(tab3));

  asm("vpxor ymm1, ymm1, ymm1");
  asm("vmovdqu ymm2, ymmword ptr [%0]" :: "r"(tab6));
  asm("vmovdqu ymm3, ymmword ptr [%0]" :: "r"(tab7));
  asm("vpcmpeqb ymm1, ymm2, ymm3");
  asm("vpxor ymm1, ymm1, ymm1");
  asm("vpcmpeqb ymm1, ymm2, ymmword ptr [%0]" :: "r"(tab7));

  asm("vpxor ymm1, ymm1, ymm1");
  asm("vpcmpeqw ymm1, ymm2, ymm3");
  asm("vpxor ymm1, ymm1, ymm1");
  asm("vpcmpeqw ymm1, ymm2, ymmword ptr [%0]" :: "r"(tab7));

  asm("vpxor ymm1, ymm1, ymm1");
  asm("vpcmpeqd ymm1, ymm2, ymm3");
  asm("vpxor ymm1, ymm1, ymm1");
  asm("vpcmpeqd ymm1, ymm2, ymmword ptr [%0]" :: "r"(tab7));

  asm("vpxor ymm1, ymm1, ymm1");
  asm("vpcmpeqq ymm1, ymm2, ymm3");
  asm("vpxor ymm1, ymm1, ymm1");
  asm("vpcmpeqq ymm1, ymm2, ymmword ptr [%0]" :: "r"(tab7));

  // vpslldq
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm3, xmmword ptr [%0]" :: "r"(tab1));
  asm("vpslldq xmm1, xmm1, 1");
  asm("vpslldq xmm4, xmm2, 10");
  asm("vpslldq xmm1, xmm3, 16");

  asm("vmovdqu ymm1, ymmword ptr [%0]" :: "r"(tab6));
  asm("vmovdqu ymm2, ymmword ptr [%0]" :: "r"(tab6));
  asm("vmovdqu ymm3, ymmword ptr [%0]" :: "r"(tab6));
  asm("vpslldq ymm1, ymm1, 1");
  asm("vpslldq ymm4, ymm2, 15");
  asm("vpslldq ymm5, ymm3, 16");

  // vpcmpgtb, vpcmpgtw, vpcmpgtd
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm3, xmmword ptr [%0]" :: "r"(tab3));
  asm("vpcmpgtb xmm1, xmm2, xmm3");
  asm("vpcmpgtb xmm1, xmm2, xmmword ptr [%0]" :: "r"(tab3));
  asm("vpcmpgtw xmm1, xmm2, xmm3");
  asm("vpcmpgtw xmm1, xmm2, xmmword ptr [%0]" :: "r"(tab3));
  asm("vpcmpgtd xmm1, xmm2, xmm3");
  asm("vpcmpgtd xmm1, xmm2, xmmword ptr [%0]" :: "r"(tab3));

  asm("vmovdqu ymm2, ymmword ptr [%0]" :: "r"(tab6));
  asm("vmovdqu ymm3, ymmword ptr [%0]" :: "r"(tab7));
  asm("vpcmpgtb ymm1, ymm2, ymm3");
  asm("vpcmpgtb ymm1, ymm2, ymmword ptr [%0]" :: "r"(tab7));
  asm("vpcmpgtw ymm1, ymm2, ymm3");
  asm("vpcmpgtw ymm1, ymm2, ymmword ptr [%0]" :: "r"(tab7));
  asm("vpcmpgtd ymm1, ymm2, ymm3");
  asm("vpcmpgtd ymm1, ymm2, ymmword ptr [%0]" :: "r"(tab7));

  // vpsubb, vpsubw, vpsubd, vpsubq
  asm("vmovdqu xmm2, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqu xmm3, xmmword ptr [%0]" :: "r"(tab5));
  asm("vpsubb xmm1, xmm2, xmm3");
  asm("vpsubb xmm1, xmm2, xmmword ptr [%0]" :: "r"(tab5));
  asm("vpsubw xmm1, xmm2, xmm3");
  asm("vpsubw xmm1, xmm2, xmmword ptr [%0]" :: "r"(tab5));
  asm("vpsubd xmm1, xmm2, xmm3");
  asm("vpsubd xmm1, xmm2, xmmword ptr [%0]" :: "r"(tab5));
  asm("vpsubq xmm1, xmm2, xmm3");
  asm("vpsubq xmm1, xmm2, xmmword ptr [%0]" :: "r"(tab5));

  asm("vmovdqu ymm2, ymmword ptr [%0]" :: "r"(tab6));
  asm("vmovdqu ymm3, ymmword ptr [%0]" :: "r"(tab7));
  asm("vpsubb ymm1, ymm2, ymm3");
  asm("vpsubb ymm1, ymm2, ymmword ptr [%0]" :: "r"(tab7));
  asm("vpsubw ymm1, ymm2, ymm3");
  asm("vpsubw ymm1, ymm2, ymmword ptr [%0]" :: "r"(tab7));
  asm("vpsubd ymm1, ymm2, ymm3");
  asm("vpsubd ymm1, ymm2, ymmword ptr [%0]" :: "r"(tab7));
  asm("vpsubq ymm1, ymm2, ymm3");
  asm("vpsubq ymm1, ymm2, ymmword ptr [%0]" :: "r"(tab7));

  // vxorps
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm3, xmmword ptr [%0]" :: "r"(tab2));
  asm("vxorps xmm1, xmm2, xmm3");
  asm("vxorps xmm1, xmm2, xmmword ptr [%0]" :: "r"(tab2));

  asm("vmovdqu ymm2, ymmword ptr [%0]" :: "r"(tab6));
  asm("vmovdqu ymm3, ymmword ptr [%0]" :: "r"(tab7));
  asm("vxorps ymm1, ymm2, ymm3");
  asm("vxorps ymm1, ymm2, ymmword ptr [%0]" :: "r"(tab7));

  // vmovaps
  asm("vmovaps xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("vmovaps xmm1, xmm2");

  //asm("vmovaps ymm1, ymmword ptr [%0]" :: "r"(tab6));
  asm("vmovdqu ymm2, ymmword ptr [%0]" :: "r"(tab7));
  asm("vmovaps ymm1, ymm2");

  // vmovups
  asm("vmovups xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("vmovups xmm1, xmm2");

  asm("vmovups ymm1, ymmword ptr [%0]" :: "r"(tab6));
  asm("vmovdqu ymm2, ymmword ptr [%0]" :: "r"(tab7));
  asm("vmovups ymm1, ymm2");

  // vmovsd
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("vmovdqa xmm3, xmmword ptr [%0]" :: "r"(tab3));
  asm("vmovsd xmm1, xmm2, xmm3");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovsd xmm1, qword ptr [%0]" :: "r"(tab2));
  asm("vmovsd qword ptr [%0], xmm1" :: "r"(tab1));

  init(tab1, tab2, tab3, tab4, tab5, tab6, tab7, tab8);

  // packuswb, packsswb
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab5));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("packuswb xmm1, xmm2");
  asm("packuswb xmm2, xmmword ptr [%0]" :: "r"(tab5));
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab5));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("packsswb xmm1, xmm2");
  asm("packsswb xmm2, xmmword ptr [%0]" :: "r"(tab5));

  // palignr
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("palignr xmm1, xmm2, 0x1");
  asm("palignr xmm2, xmmword ptr [%0], 0x1" :: "r"(tab1));
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("palignr xmm1, xmm2, 0x5");
  asm("palignr xmm2, xmmword ptr [%0], 0x5" :: "r"(tab1));
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("palignr xmm1, xmm2, 0x1f");
  asm("palignr xmm2, xmmword ptr [%0], 0x1f" :: "r"(tab1));
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("palignr xmm1, xmm2, 0x20");
  asm("palignr xmm2, xmmword ptr [%0], 0x20" :: "r"(tab1));
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("palignr xmm1, xmm2, 0x25");
  asm("palignr xmm2, xmmword ptr [%0], 0x25" :: "r"(tab1));

  init(tab1, tab2, tab3, tab4, tab5, tab6, tab7, tab8);

  // pmulhw, pmullw, pmulld
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("pmulhw xmm1, xmm2");
  asm("pmulhw xmm2, xmmword ptr [%0]"  :: "r"(tab1));
  asm("pmullw xmm1, xmm2");
  asm("pmullw xmm2, xmmword ptr [%0]"  :: "r"(tab1));
  asm("pmulld xmm1, xmm2");
  asm("pmulld xmm2, xmmword ptr [%0]"  :: "r"(tab1));
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab8));
  asm("pmulhw xmm1, xmm2");
  asm("pmulhw xmm2, xmmword ptr [%0]"  :: "r"(tab8));
  asm("pmullw xmm1, xmm2");
  asm("pmullw xmm2, xmmword ptr [%0]"  :: "r"(tab8));
  asm("pmulld xmm1, xmm2");
  asm("pmulld xmm2, xmmword ptr [%0]"  :: "r"(tab8));

  // vpmulhw, vpmullw
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("vmovdqa xmm3, xmmword ptr [%0]" :: "r"(tab8));
  asm("vpmulhw xmm4, xmm1, xmm2");
  asm("vpmulhw xmm4, xmm1, xmmword ptr [%0]" :: "r"(tab2));
  asm("vpmulhw xmm4, xmm2, xmm3");
  asm("vpmullw xmm4, xmm1, xmm2");
  asm("vpmullw xmm4, xmm1, xmmword ptr [%0]" :: "r"(tab2));
  asm("vpmullw xmm4, xmm2, xmm3");
  asm("vmovdqu ymm1, ymmword ptr [%0]" :: "r"(tab6));
  asm("vmovdqu ymm2, ymmword ptr [%0]" :: "r"(tab7));
  asm("vmovdqu ymm3, ymmword ptr [%0]" :: "r"(tab1));
  asm("vpmulhw ymm4, ymm1, ymm2");
  asm("vpmulhw ymm4, ymm1, ymmword ptr [%0]" :: "r"(tab2));
  asm("vpmulhw ymm4, ymm2, ymm3");
  asm("vpmullw ymm4, ymm1, ymm2");
  asm("vpmullw ymm4, ymm1, ymmword ptr [%0]" :: "r"(tab2));
  asm("vpmullw ymm4, ymm2, ymm3");

  // vpaddb, vpaddd, vpaddw
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("vpaddb xmm4, xmm1, xmm1");
  asm("vpaddb xmm4, xmm1, xmm2");
  asm("vpaddd xmm4, xmm1, xmm1");
  asm("vpaddd xmm4, xmm1, xmm2");
  asm("vpaddw xmm4, xmm1, xmm1");
  asm("vpaddw xmm4, xmm1, xmm2");
  asm("vmovdqu ymm1, ymmword ptr [%0]" :: "r"(tab6));
  asm("vmovdqu ymm2, ymmword ptr [%0]" :: "r"(tab7));
  asm("vpaddb ymm4, ymm1, ymm1");
  asm("vpaddb ymm4, ymm1, ymm2");
  asm("vpaddd ymm4, ymm1, ymm1");
  asm("vpaddd ymm4, ymm1, ymm2");
  asm("vpaddw ymm4, ymm1, ymm1");
  asm("vpaddw ymm4, ymm1, ymm2");

  // psraw, psrad
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("psraw xmm1, 1");
  asm("psraw xmm1, 6");
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("psraw xmm2, 15");
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("psraw xmm2, 17");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab8));
  asm("psraw xmm1, xmm2");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("psraw xmm1, xmm2");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("psrad xmm1, 1");
  asm("psrad xmm1, 6");
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("psrad xmm2, 16");
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("psrad xmm2, 32");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab8));
  asm("psrad xmm1, xmm2");
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("psrad xmm1, xmm2");

  // vpsraw, vpsrad
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("vmovdqa xmm3, xmmword ptr [%0]" :: "r"(tab3));
  asm("vpsraw xmm4, xmm1, 1");
  asm("vpsraw xmm5, xmm2, 10");
  asm("vpsraw xmm6, xmm3, 18");
  asm("vpsraw xmm4, xmm4, xmm1");
  asm("vpsrad xmm4, xmm1, 1");
  asm("vpsrad xmm5, xmm2, 10");
  asm("vpsrad xmm6, xmm3, 18");
  asm("vpsrad xmm4, xmm4, xmm1");
  asm("vmovdqu ymm1, ymmword ptr [%0]" :: "r"(tab6));
  asm("vmovdqu ymm2, ymmword ptr [%0]" :: "r"(tab7));
  asm("vmovdqu ymm3, ymmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab8));
  asm("vpsraw ymm4, ymm1, 1");
  asm("vpsraw ymm5, ymm2, 10");
  asm("vpsraw ymm6, ymm3, 18");
  asm("vpsraw ymm5, ymm4, xmm1");
  asm("vpsraw ymm5, ymm4, xmm2");
  asm("vpsrad ymm4, ymm1, 1");
  asm("vpsrad ymm5, ymm2, 10");
  asm("vpsrad ymm6, ymm3, 18");
  asm("vpsrad ymm5, ymm4, xmm1");
  asm("vpsrad ymm5, ymm4, xmm2");

  // vpsllw
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab5));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("vmovdqa xmm3, xmmword ptr [%0]" :: "r"(tab8));
  asm("vpsllw xmm4, xmm1, 1");
  asm("vpsllw xmm4, xmm1, 4");
  asm("vpsllw xmm4, xmm2, 10");
  asm("vpsllw xmm4, xmm2, 15");
  asm("vpsllw xmm4, xmm1, xmm1");
  asm("vpsllw xmm4, xmm2, xmm3");
  asm("vmovdqu ymm1, ymmword ptr [%0]" :: "r"(tab6));
  asm("vmovdqu ymm2, ymmword ptr [%0]" :: "r"(tab7));
  asm("vpsllw ymm4, ymm1, 1");
  asm("vpsllw ymm4, ymm1, 4");
  asm("vpsllw ymm4, ymm2, 10");
  asm("vpsllw ymm4, ymm2, 15");
  asm("vpsllw ymm4, ymm1, xmm1");

  // vpsrlw
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab5));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("vmovdqa xmm3, xmmword ptr [%0]" :: "r"(tab8));
  asm("vpsrlw xmm4, xmm1, 1");
  asm("vpsrlw xmm4, xmm1, 4");
  asm("vpsrlw xmm4, xmm2, 10");
  asm("vpsrlw xmm4, xmm2, 15");
  asm("vpsrlw xmm4, xmm1, xmm1");
  asm("vpsrlw xmm4, xmm2, xmm3");
  asm("vmovdqu ymm1, ymmword ptr [%0]" :: "r"(tab6));
  asm("vmovdqu ymm2, ymmword ptr [%0]" :: "r"(tab7));
  asm("vpsrlw ymm4, ymm1, 1");
  asm("vpsrlw ymm4, ymm1, 4");
  asm("vpsrlw ymm4, ymm2, 10");
  asm("vpsrlw ymm4, ymm2, 15");
  asm("vpsrlw ymm4, ymm1, xmm1");

  // vpsrldq
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab3));
  asm("vpsrldq xmm4, xmm1, 1");
  asm("vpsrldq xmm4, xmm1, 4");
  asm("vpsrldq xmm4, xmm2, 10");
  asm("vpsrldq xmm4, xmm2, 18");
  asm("vmovdqu ymm1, ymmword ptr [%0]" :: "r"(tab6));
  asm("vmovdqu ymm2, ymmword ptr [%0]" :: "r"(tab7));
  asm("vpsrldq ymm4, ymm1, 1");
  asm("vpsrldq ymm4, ymm1, 4");
  asm("vpsrldq ymm4, ymm2, 10");
  asm("vpsrldq ymm4, ymm2, 18");

  // packssdw, packsswb
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab2));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab7));
  asm("packssdw xmm1, xmm2");
  asm("packssdw xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab5));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("packsswb xmm1, xmm2");
  asm("packsswb xmm2, xmmword ptr [%0]" :: "r"(tab5));

  // vpackuswb
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab5));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("vpackuswb xmm3, xmm1, xmm2");
  asm("vmovdqu ymm1, ymmword ptr [%0]" :: "r"(tab7));
  asm("vmovdqu ymm2, ymmword ptr [%0]" :: "r"(tab5));
  asm("vpackuswb ymm3, ymm1, ymm2");

  // vpackssdw, vpacksswb
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab5));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("vpackssdw xmm3, xmm1, xmm2");
  asm("vpacksswb xmm3, xmm1, xmm2");
  asm("vmovdqu ymm1, ymmword ptr [%0]" :: "r"(tab6));
  asm("vmovdqu ymm2, ymmword ptr [%0]" :: "r"(tab7));
  asm("vpackssdw ymm3, ymm1, ymm2");
  asm("vpacksswb ymm3, ymm1, ymm2");

  // vpunpckhbw, vpunpckhdq, vpunpckhqdq, vpunpckhwd
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab4));
  asm("vpunpckhbw xmm3, xmm1, xmm2");
  asm("vpunpckhdq xmm3, xmm1, xmm2");
  asm("vpunpckhqdq xmm3, xmm1, xmm2");
  asm("vpunpckhwd xmm3, xmm1, xmm2");
  asm("vmovdqu ymm1, ymmword ptr [%0]" :: "r"(tab6));
  asm("vmovdqu ymm2, ymmword ptr [%0]" :: "r"(tab7));
  asm("vpunpckhbw ymm3, ymm1, ymm2");
  asm("vpunpckhdq ymm3, ymm1, ymm2");
  asm("vpunpckhqdq ymm3, ymm1, ymm2");
  asm("vpunpckhwd ymm3, ymm1, ymm2");

  // vpunpcklbw, vpunpckldq, vpunpcklqdq, vpunpcklwd
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab4));
  asm("vpunpcklbw xmm3, xmm1, xmm2");
  asm("vpunpckldq xmm3, xmm1, xmm2");
  asm("vpunpcklqdq xmm3, xmm1, xmm2");
  asm("vpunpcklwd xmm3, xmm1, xmm2");
  asm("vmovdqu ymm1, ymmword ptr [%0]" :: "r"(tab6));
  asm("vmovdqu ymm2, ymmword ptr [%0]" :: "r"(tab7));
  asm("vpunpcklbw ymm3, ymm1, ymm2");
  asm("vpunpckldq ymm3, ymm1, ymm2");
  asm("vpunpcklqdq ymm3, ymm1, ymm2");
  asm("vpunpcklwd ymm3, ymm1, ymm2");

  // vperm2i128
  asm("vmovdqu ymm1, ymmword ptr [%0]" :: "r"(tab6));
  asm("vmovdqu ymm2, ymmword ptr [%0]" :: "r"(tab7));
  asm("vperm2i128 ymm3, ymm1, ymm2, 0");
  asm("vperm2i128 ymm3, ymm1, ymm2, 1");
  asm("vperm2i128 ymm3, ymm1, ymm2, 2");
  asm("vperm2i128 ymm3, ymm1, ymm2, 3");
  asm("vperm2i128 ymm3, ymm1, ymm2, 8");
  asm("vperm2i128 ymm3, ymm1, ymm2, 9");
  asm("vperm2i128 ymm3, ymm1, ymm2, 10");
  asm("vperm2i128 ymm3, ymm1, ymm2, 11");
  asm("vperm2i128 ymm3, ymm1, ymm2, 16");
  asm("vperm2i128 ymm3, ymm1, ymm2, 17");
  asm("vperm2i128 ymm3, ymm1, ymm2, 18");
  asm("vperm2i128 ymm3, ymm1, ymm2, 19");
  asm("vperm2i128 ymm3, ymm1, ymm2, 24");
  asm("vperm2i128 ymm3, ymm1, ymm2, 25");
  asm("vperm2i128 ymm3, ymm1, ymm2, 26");
  asm("vperm2i128 ymm3, ymm1, ymm2, 27");
  asm("vperm2i128 ymm3, ymm1, ymm2, 32");
  asm("vperm2i128 ymm3, ymm1, ymm2, 33");
  asm("vperm2i128 ymm3, ymm1, ymm2, 34");
  asm("vperm2i128 ymm3, ymm1, ymm2, 35");
  asm("vperm2i128 ymm3, ymm1, ymm2, 40");
  asm("vperm2i128 ymm3, ymm1, ymm2, 41");
  asm("vperm2i128 ymm3, ymm1, ymm2, 42");
  asm("vperm2i128 ymm3, ymm1, ymm2, 43");
  asm("vperm2i128 ymm3, ymm1, ymm2, 48");
  asm("vperm2i128 ymm3, ymm1, ymm2, 49");
  asm("vperm2i128 ymm3, ymm1, ymm2, 50");
  asm("vperm2i128 ymm3, ymm1, ymm2, 51");
  asm("vperm2i128 ymm3, ymm1, ymm2, 56");
  asm("vperm2i128 ymm3, ymm1, ymm2, 57");
  asm("vperm2i128 ymm3, ymm1, ymm2, 58");
  asm("vperm2i128 ymm3, ymm1, ymm2, 59");
  asm("vperm2i128 ymm3, ymm1, ymm2, 128");
  asm("vperm2i128 ymm3, ymm1, ymm2, 129");
  asm("vperm2i128 ymm3, ymm1, ymm2, 130");
  asm("vperm2i128 ymm3, ymm1, ymm2, 131");
  asm("vperm2i128 ymm3, ymm1, ymm2, 136");
  asm("vperm2i128 ymm3, ymm1, ymm2, 137");
  asm("vperm2i128 ymm3, ymm1, ymm2, 138");
  asm("vperm2i128 ymm3, ymm1, ymm2, 139");
  asm("vperm2i128 ymm3, ymm1, ymm2, 144");
  asm("vperm2i128 ymm3, ymm1, ymm2, 145");
  asm("vperm2i128 ymm3, ymm1, ymm2, 146");
  asm("vperm2i128 ymm3, ymm1, ymm2, 147");
  asm("vperm2i128 ymm3, ymm1, ymm2, 152");
  asm("vperm2i128 ymm3, ymm1, ymm2, 153");
  asm("vperm2i128 ymm3, ymm1, ymm2, 154");
  asm("vperm2i128 ymm3, ymm1, ymm2, 155");
  asm("vperm2i128 ymm3, ymm1, ymm2, 160");
  asm("vperm2i128 ymm3, ymm1, ymm2, 161");
  asm("vperm2i128 ymm3, ymm1, ymm2, 162");
  asm("vperm2i128 ymm3, ymm1, ymm2, 163");
  asm("vperm2i128 ymm3, ymm1, ymm2, 168");
  asm("vperm2i128 ymm3, ymm1, ymm2, 169");
  asm("vperm2i128 ymm3, ymm1, ymm2, 170");
  asm("vperm2i128 ymm3, ymm1, ymm2, 171");
  asm("vperm2i128 ymm3, ymm1, ymm2, 176");
  asm("vperm2i128 ymm3, ymm1, ymm2, 177");
  asm("vperm2i128 ymm3, ymm1, ymm2, 178");
  asm("vperm2i128 ymm3, ymm1, ymm2, 179");
  asm("vperm2i128 ymm3, ymm1, ymm2, 184");
  asm("vperm2i128 ymm3, ymm1, ymm2, 185");
  asm("vperm2i128 ymm3, ymm1, ymm2, 186");
  asm("vperm2i128 ymm3, ymm1, ymm2, 187");

  // pmaddwd, vpmaddwd
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab4));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab7));
  asm("vmovdqa xmm3, xmmword ptr [%0]" :: "r"(tab2));
  asm("vpmaddwd xmm4, xmm1, xmm2");
  asm("pmaddwd xmm1, xmm2");
  asm("vpmaddwd xmm4, xmm3, xmmword ptr [%0]" :: "r"(tab6));
  asm("pmaddwd xmm3, xmmword ptr [%0]" :: "r"(tab6));
  asm("vmovdqu ymm1, ymmword ptr [%0]" :: "r"(tab6));
  asm("vmovdqu ymm2, ymmword ptr [%0]" :: "r"(tab7));
  asm("vpmaddwd ymm3, ymm1, ymm2");

  // vpermq
  asm("vmovdqu ymm1, ymmword ptr [%0]" :: "r"(tab6));
  asm("vpermq ymm2, ymm1, 0");
  asm("vpermq ymm2, ymm1, 43");
  asm("vpermq ymm2, ymm1, 85");
  asm("vpermq ymm2, ymm1, 114");
  asm("vpermq ymm2, ymm1, 170");
  asm("vpermq ymm2, ymm1, 216");
  asm("vpermq ymm2, ymm1, 228");
  asm("vpermq ymm2, ymm1, 255");

  // vextracti128
  asm("vmovdqu ymm1, ymmword ptr [%0]" :: "r"(tab7));
  asm("vextracti128 xmm2, ymm1, 0");
  asm("vextracti128 xmm2, ymm1, 1");
  asm("vextracti128 xmm2, ymm1, 2");
  asm("vextracti128 xmm2, ymm1, 255");

  // vmovntdq
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab1));
  asm("vmovntdq xmmword ptr [%0], xmm1" :: "r"(tab2));

  init(tab1, tab2, tab3, tab4, tab5, tab6, tab7, tab8);

  // vpsignw
  asm("vmovdqa xmm1, xmmword ptr [%0]" :: "r"(tab5));
  asm("vmovdqa xmm2, xmmword ptr [%0]" :: "r"(tab2));
  asm("vpsignw xmm3, xmm1, xmm2");
  asm("vpsignw xmm3, xmm1, xmm1");

  // popcnt
  asm("mov rax, -1");
  asm("popcnt rdx, rax");
  asm("mov rax, 0");
  asm("popcnt rdx, rax");
  asm("mov rax, 1");
  asm("popcnt rdx, rax");
  asm("mov rax, 5");
  asm("popcnt rdx, rax");
  asm("mov rax, 234");
  asm("popcnt rdx, rax");

  asm("mov eax, -1");
  asm("popcnt edx, eax");
  asm("mov eax, 0");
  asm("popcnt edx, eax");
  asm("mov eax, 1");
  asm("popcnt edx, eax");
  asm("mov eax, 5");
  asm("popcnt edx, eax");
  asm("mov eax, 123456");
  asm("popcnt edx, eax");

  asm("mov ax, -1");
  asm("popcnt dx, ax");
  asm("mov ax, 0");
  asm("popcnt dx, ax");
  asm("mov ax, 1");
  asm("popcnt dx, ax");
  asm("mov ax, 5");
  asm("popcnt dx, ax");
  asm("mov ax, 12345");
  asm("popcnt dx, ax");

}

int main(){
  check();
}
