## Description

This directory contains some tools based on the Triton's API.

## Format string bug analysis

This tool taints all arguments (`*argv[]`) and checks when a printf occurs if
there is some tainted bytes in its first argument (RDI). If RDI points on a
memory area which contains tainted bytes, that means there is a possible
vulnerability.

```
$ ../../../pin -t ./triton.so -script ./tools/format_string_bug_analysis.py -- ./samples/vulns/formatString abcd titutatatoto
[+] 012 bytes tainted from the argv[2] (0x7fff367da0f9) pointer
[+] 004 bytes tainted from the argv[1] (0x7fff367da0f4) pointer
[+] 028 bytes tainted from the argv[0] (0x7fff367da0d7) pointer
[+] Analyzing the printf prologue argument.
[+] Possible format string bug found. The first arugment contains some tainted bytes.
         [trace] 0x4005e6: mov byte ptr [rax], 0x0
         [trace] 0x4005e9: mov rax, qword ptr [rbp-0x8]
         [trace] 0x4005ed: mov rdi, rax
         [trace] 0x4005f0: mov eax, 0x0
         [trace] 0x4005f5: call 0x400460
         [trace] 0x400460: jmp qword ptr [rip+0x200bb2]
         [trace] 0x400466: push 0x0
         [trace] 0x40046b: jmp 0x400450
         [trace] 0x400450: push qword ptr [rip+0x200bb2]
         [trace] 0x400456: jmp qword ptr [rip+0x200bb4]
abcd
$
```


