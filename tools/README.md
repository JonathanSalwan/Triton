## Description

This directory contains some tools based on the Triton's API.



## Format string bug analysis

This tool taints all arguments (`*argv[]`) and checks when a printf occurs if
there is some tainted bytes in its first argument (RDI). If RDI points on a
memory area which contains tainted bytes, that means there is a possible
vulnerability.

```
$ ./triton ./tools/format_string_bug_analysis.py ./samples/vulns/formatString abcd titutatatoto
[+] 012 bytes tainted from the argv[2] (0x7fff367da0f9) pointer
[+] 004 bytes tainted from the argv[1] (0x7fff367da0f4) pointer
[+] 028 bytes tainted from the argv[0] (0x7fff367da0d7) pointer
[+] Analyzing the printf prologue argument.
[+] Possible format string bug found. The first argument contains some tainted bytes.
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



## Use after free bug and memory leak analysis

This tool maintains a free table (TF) and an allocation table (TA) which
represents the states of pointers allocated/freed during the execution.
When a LOAD and STORE instruction occurs, the tool checks if the memory
access is referenced into TA or TF.

If the memory access is in TF -> use-after-free.

```
$ ./triton ./tools/use_after_free_bug_and_memory_leak_analysis.py ./samples/vulns/testSuite
[+] TA <- (0x1bec010, 0x20)
[+] TA <- (0x1bec040, 0x20)
[+] TA -> (0x1bec010, 0x20)
[+] TF <- (0x1bec010, 0x20)
[!] Use-after-free (0x1bec020) at 0x4006cb: mov byte ptr [rax], 0x43
[+] TF -> (0x1bec010, 0x20)
[+] TA <- (0x1bec010, 0x20)
[+] TA -> (0x1bec040, 0x20)
[+] TF <- (0x1bec040, 0x20)

Free table:
        (0x1bec040, 0x20)

Allocation table:
        (0x1bec010, 0x20)

[!] There is 32 bytes of leaked memory
```



## Read/Write memory tracer

This tool is used to trace all memory access. With this tool, you know
which instruction read and write in memory, where it read/write,
the access' size and the value. May be useful to track quickly some
specific data.

```
$ ./triton ./tools/memory_tracer.py ./samples/vulns/testSuite
[...]
[R:4] 0x0000004005fa: mov eax, dword ptr [rbp-0x8]      R:0x00007fff51aa7c08: 04 00 00 00 (0x4)
[W:1] 0x000000400606: mov byte ptr [rax], 0x45          W:0x00007fff51aa7c08: 45 (0x45)
[R:4] 0x000000400609: add dword ptr [rbp-0x8], 0x1      R:0x00007fff51aa7c08: 45 00 00 00 (0x45)
[R:4] 0x00000040060d: mov eax, dword ptr [rbp-0x8]      R:0x00007fff51aa7c08: 46 00 00 00 (0x46)
[R:8] 0x000000400615: pop rbp                           R:0x00007fff51aa7c10: 50 7c aa 51 ff 7f 00 00 (0x7fff51aa7c50)
[R:8] 0x000000400616: ret                               R:0x00007fff51aa7c18: f8 06 40 00 00 00 00 00 (0x4006f8)
[R:8] 0x0000004006f8: mov rax, qword ptr [rbp-0x8]      R:0x00007fff51aa7c48: 40 b0 73 01 00 00 00 00 (0x173b040)
[W:8] 0x0000004006ff: call 0x400460                     W:0x00007fff51aa7c18: 04 07 40 00 00 00 00 00 (0x400704)
[R:8] 0x000000400460: jmp qword ptr [rip+0x200bb2]      R:0x0000000000601018: 00 b1 0e dd 9b 7f 00 00 (0x7f9bdd0eb100)
[R:8] 0x7f9bdd0eb100: mov rax, qword ptr [rip+0x315de1] R:0x00007f9bdd400ee8: e8 37 40 dd 9b 7f 00 00 (0x7f9bdd4037e8)
[R:8] 0x7f9bdd0eb107: mov rax, qword ptr [rax]          R:0x00007f9bdd4037e8: 00 00 00 00 00 00 00 00 (0x0)
[R:8] 0x7f9bdd0eb114: mov rax, qword ptr [rdi-0x8]      R:0x000000000173b038: 31 00 00 00 00 00 00 00 (0x31)
[W:8] 0x7f9bdd0e7890: push r15                          W:0x00007fff51aa7c10: 00 00 00 00 00 00 00 00 (0x0)
[W:8] 0x7f9bdd0e7892: push r14                          W:0x00007fff51aa7c08: 00 00 00 00 00 00 00 00 (0x0)
[W:8] 0x7f9bdd0e7894: push r13                          W:0x00007fff51aa7c00: 30 7d aa 51 ff 7f 00 00 (0x7fff51aa7d30)
[W:8] 0x7f9bdd0e7896: push r12                          W:0x00007fff51aa7bf8: a0 04 40 00 00 00 00 00 (0x4004a0)
[W:8] 0x7f9bdd0e7898: push rbp                          W:0x00007fff51aa7bf0: 50 7c aa 51 ff 7f 00 00 (0x7fff51aa7c50)
[W:8] 0x7f9bdd0e7899: push rbx                          W:0x00007fff51aa7be8: 00 00 00 00 00 00 00 00 (0x0)
[R:8] 0x7f9bdd0e78a1: mov rax, qword ptr [rsi+0x8]      R:0x000000000173b038: 31 00 00 00 00 00 00 00 (0x31)
[...]
```



## Database generation

Sometime it's useful to work offline and to apply advanced DBA
based on a concrete trace. This tool is used to generate a database
which will may be then loaded into several tools like IDA or may be
used to perform more analysis. This database contains all instructions
executed with their symbolic expressions, their memory access information
and their registers value information.

```
$ ./triton ./tools/generate_db.py ./samples/crackmes/crackme_xor test
[+] Database created.
loose
[+] Trace dumped.

$ sqlite3 ./trace.db
SQLite version 3.8.10.1 2015-05-09 12:14:55
Enter ".help" for usage hints.

sqlite> .schema
CREATE TABLE instructions(addr INTEGER, assembly TEXT, exprs TEXT);
CREATE TABLE expressions(id INTEGER PRIMARY KEY, expr TEXT);
CREATE TABLE memoryAccess(addr INTEGER, accessType TEXT, accessSize INTEGER, accessAddr INTEGER, contentAsString TEXT, contentAsInteger INTEGER);
CREATE TABLE registersValue(addr INTEGER, id INTEGER, name TEXT, size INTEGER, content INTEGER);

sqlite> select * from expressions where id=3194;
3194|(bvadd ((_ extract 63 0) #3107) (_ bv8 64))
```
