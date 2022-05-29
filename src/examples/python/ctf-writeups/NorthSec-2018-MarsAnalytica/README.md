# NorthSec 2018 MarsAnalytica (Virtual Machine) challenge

I did not participate to the challenge in 2018 but yesterday (in 2022) I saw
the [Toshi's](https://twitter.com/piazzt) write-up on the RPISEC's
[blog](https://rpis.ec/blog/northsec-2018-marsanalytica/). At the end of the
blog post Toshi said:

> Initially I was hoping for a solution which employed Triton. Since it sports
> an associated pintool I assumed it would be a lot faster to run and to pick
> up path constraints. The technique of dumping the path predicate and solving
> for one particular branch was also inspired by Triton's concolic execution.
>
> Furthermore, Triton was used in a partial solution to the Tigress VM Challenges,
> another set of challenges which demonstrates virtualization obfuscation techniques.
> Unfortunately, I couldn’t get Triton to run on this binary but I’d love to see
> someone reconstruct the source using this same technique!

Well, with a comment like this I can't resist the temptation to take a look at
the challenge :).

This write-up have several objective:

* Pleasing Toshi (even if it's 4 years later :D)
* Giving another Virtual Machine to Triton (see [Tigress](https://github.com/JonathanSalwan/Tigress_protection) and [VMProtect](https://github.com/JonathanSalwan/VMProtect-devirtualization))
* Providing a methodology example when analyzing a big binary with Triton
* Last but not least, having fun :)

# The challenge

Ok, let's just execute the binary to see what we have to do:

```
$ ./MarsAnalytica
  __  __                                      _       _   _
 |  \/  |                   /\               | |     | | (_)
 | \  / | __ _ _ __ ___    /  \   _ __   __ _| |_   _| |_ _  ___ __ _
 | |\/| |/ _` | '__/ __|  / /\ \ | '_ \ / _` | | | | | __| |/ __/ _` |
 | |  | | (_| | |  \__ \ / ____ \| | | | (_| | | |_| | |_| | (_| (_| |
 |_|  |_|\__,_|_|  |___//_/    \_\_| |_|\__,_|_|\__, |\__|_|\___\__,_|
                                                 __/ |
                                                |___/        NSEC 2018


Citizen Access ID: test test test test

[!] ACCESS DENIED - Invalid Citizen ID
[-] Session Terminated
```

It looks like we have to provide a good Citizen ID on `stdin`. The binary is about
4M and if we take a look at the code with IDA it appears to be packed. So first
of all, we will unpack it.

## Unpack the binary

The easy and lazy way to do this is to use GDB when the binary is waiting for
an input on stdin. So, we run the binary in gdb, when the binary is waiting for
an input, we press *ctrl-c* in order to go back on GDB's prompt and then we dump
the process memory.

```
$ gdb ./MarsAnalytica
GNU gdb (Gentoo 11.2 vanilla) 11.2
[...]
gdb-peda$ r
Starting program: /home/jonathan/Works/Tools/Triton/src/examples/python/ctf-writeups/NorthSec-2018-MarsAnalytica/MarsAnalytica
  __  __                                      _       _   _
 |  \/  |                   /\               | |     | | (_)
 | \  / | __ _ _ __ ___    /  \   _ __   __ _| |_   _| |_ _  ___ __ _
 | |\/| |/ _` | '__/ __|  / /\ \ | '_ \ / _` | | | | | __| |/ __/ _` |
 | |  | | (_| | |  \__ \ / ____ \| | | | (_| | | |_| | |_| | (_| (_| |
 |_|  |_|\__,_|_|  |___//_/    \_\_| |_|\__,_|_|\__, |\__|_|\___\__,_|
                                                 __/ |
                                                |___/        NSEC 2018


Citizen Access ID: ^C
Program received signal SIGINT, Interrupt.

[----------------------------------registers-----------------------------------]
RAX: 0xfffffffffffffe00
RBX: 0x7ffff7f99aa0 --> 0xfbad2288
RCX: 0x7ffff7ea369e (cmp    rax,0xfffffffffffff000)
RDX: 0x400
RSI: 0x105fad0 --> 0x0
RDI: 0x0
RBP: 0x7ffff7f965e0 --> 0x0
RSP: 0x7ffffff42cb8 --> 0x7ffff7e2a95c (test   rax,rax)
RIP: 0x7ffff7ea369e (cmp    rax,0xfffffffffffff000)
R8 : 0x0
R9 : 0x77 ('w')
R10: 0x5d (']')
R11: 0x246
R12: 0x7ffff7f9a780 --> 0xfbad2a84
R13: 0xd68 ('h\r')
R14: 0x7ffff7f959e0 --> 0x0
R15: 0xd68 ('h\r')
EFLAGS: 0x246 (carry PARITY adjust ZERO sign trap INTERRUPT direction overflow)
[-------------------------------------code-------------------------------------]
   0x7ffff7ea3698:	test   eax,eax
   0x7ffff7ea369a:	jne    0x7ffff7ea36b0
   0x7ffff7ea369c:	syscall
=> 0x7ffff7ea369e:	cmp    rax,0xfffffffffffff000
   0x7ffff7ea36a4:	ja     0x7ffff7ea3700
   0x7ffff7ea36a6:	ret
   0x7ffff7ea36a7:	nop    WORD PTR [rax+rax*1+0x0]
   0x7ffff7ea36b0:	sub    rsp,0x28
[------------------------------------stack-------------------------------------]
0000| 0x7ffffff42cb8 --> 0x7ffff7e2a95c (test   rax,rax)
0008| 0x7ffffff42cc0 --> 0x7ffff7ff7000 --> 0x7ffff7ff8220 --> 0x0
0016| 0x7ffffff42cc8 --> 0x7ffff7f965e0 --> 0x0
0024| 0x7ffffff42cd0 --> 0x7ffffff42cf0 --> 0x400da9 (push   rbp)
0032| 0x7ffffff42cd8 --> 0x7ffff7f99aa0 --> 0xfbad2288
0040| 0x7ffffff42ce0 --> 0x7ffff7f965e0 --> 0x0
0048| 0x7ffffff42ce8 --> 0x7fffffffd2f8 --> 0x7fffffffe64f ("/home/jonathan/Works/Tools/Triton/src/examples/python/ctf-writeups/NorthSec-2018-MarsAnalytica/MarsAnalytica")
0056| 0x7ffffff42cf0 --> 0x400da9 (push   rbp)
[------------------------------------------------------------------------------]
Legend: code, data, rodata, value
Stopped reason: SIGINT
0x00007ffff7ea369e in ?? ()

gdb-peda$ getpid
15645

gdb-peda$ cat /proc/15645/maps
00400000-00e5e000 r-xp 00000000 00:00 0
00e5e000-0105d000 ---p 00000000 00:00 0
0105d000-0105e000 r--p 00000000 00:00 0
0105e000-01080000 rw-p 00000000 00:00 0                                  [heap]
7ffff7da8000-7ffff7daa000 rw-p 00000000 00:00 0
7ffff7daa000-7ffff7dd2000 r--p 00000000 103:04 9059496                   /lib64/libc.so.6
7ffff7dd2000-7ffff7f3d000 r-xp 00028000 103:04 9059496                   /lib64/libc.so.6
7ffff7f3d000-7ffff7f94000 r--p 00193000 103:04 9059496                   /lib64/libc.so.6
7ffff7f94000-7ffff7f95000 ---p 001ea000 103:04 9059496                   /lib64/libc.so.6
7ffff7f95000-7ffff7f99000 r--p 001ea000 103:04 9059496                   /lib64/libc.so.6
7ffff7f99000-7ffff7f9b000 rw-p 001ee000 103:04 9059496                   /lib64/libc.so.6
7ffff7f9b000-7ffff7fa5000 rw-p 00000000 00:00 0
7ffff7fc5000-7ffff7fc6000 r--p 00000000 103:04 9059538                   /lib64/ld-linux-x86-64.so.2
7ffff7fc6000-7ffff7feb000 r-xp 00001000 103:04 9059538                   /lib64/ld-linux-x86-64.so.2
7ffff7feb000-7ffff7ff5000 r--p 00026000 103:04 9059538                   /lib64/ld-linux-x86-64.so.2
7ffff7ff5000-7ffff7ff7000 r--p 0002f000 103:04 9059538                   /lib64/ld-linux-x86-64.so.2
7ffff7ff7000-7ffff7ff9000 rw-p 00031000 103:04 9059538                   /lib64/ld-linux-x86-64.so.2
7ffff7ff9000-7ffff7ffd000 r--p 00000000 00:00 0                          [vvar]
7ffff7ffd000-7ffff7fff000 r-xp 00000000 00:00 0                          [vdso]
7ffffff42000-7ffffffff000 rw-p 00000000 00:00 0                          [stack]
ffffffffff600000-ffffffffff601000 r-xp 00000000 00:00 0                  [vsyscall]

gdb-peda$ dump memory 00400000-00e5e000.dump 0x00400000 0x00e5e000
```

After the unpack the binary is about 11M! We will have fun for sure...

```
$ file 00400000-00e5e000.dump
00400000-00e5e000.dump: ELF 64-bit LSB executable, x86-64, version 1 (SYSV), for GNU/Linux 3.2.0, BuildID[sha1]=1e909e60e5acf7d42fbaa5bfd0aa1e413a8d792a, dynamically linked, interpreter /lib64/ld-linux-x86-64.so.2, no section header

$ ls -l 00400000-00e5e000.dump
-rwxr-xr-x 1 jonathan jonathan 11M May 29 15:02 00400000-00e5e000.dump
```

I quickly took a look with IDA on the binary but quickly understood that a
static analysis will be quite hard. A lot of code, a lot of dynamic jumps and
no string. I do not like hard job so let's just emulate the code to get a first
trace of what's going on.

## Emulate the code

As a user of Triton, we will for sure use Triton to emulate the code. After making
the script that emulates the code, I used to print all instructions in a file and start
analyzing the trace but in this case the file is about 717M and contains 21,578,841
instructions. Another bad point is that it takes about 1 hour to generate the trace with Triton,
which is not doable because we will not wait 1h for every test we do. So we have
to find a solution to speed up the execution. Two possible solutions 1) improve Triton
2) do not emulate the binary from the entry point. Well, the second point looks good to
me :).

What we know? We know nothing about the code but we know that it waits for an user
input. So the idea is to put a *watchpoint* on the PLT of the `getchar` function. It
will give us information about where interesting parts of the code start. Via a static
analysis with IDA and some watchpoints on GDB, I found that the first `getchar`
is called at `0x4030A9`. So let's put a breakpoint on it and then do a [fulldump](https://github.com/JonathanSalwan/Triton/blob/316696e09fc38d4d25e6e81e39942302e8dfe932/src/examples/python/ctf-writeups/defcon-2016-baby-re/gdb-peda-fulldump.patch)
of registers and memory segments.

```
$ gdb ./MarsAnalytica
GNU gdb (Gentoo 11.2 vanilla) 11.2
[...]
gdb-peda$ watch *0x105E040
Hardware watchpoint 1: *0x105E040

gdb-peda$ r
Starting program: /home/jonathan/crackmes/MarsAnalytica
[..]
Hardware watchpoint 1: *0x105E040
Old value = 0x1
New value = 0xa6
0x00000000015f68c3 in ?? ()

gdb-peda$ c
Continuing.
Hardware watchpoint 1: *0x105E040
Old value = 0xa6
New value = 0x4008a6
0x00000000015f6891 in ?? ()

gdb-peda$ b *0x4030a4
Breakpoint 2 at 0x4030a4

gdb-peda$ c
Continuing.
  __  __                                      _       _   _
 |  \/  |                   /\               | |     | | (_)
 | \  / | __ _ _ __ ___    /  \   _ __   __ _| |_   _| |_ _  ___ __ _
 | |\/| |/ _` | '__/ __|  / /\ \ | '_ \ / _` | | | | | __| |/ __/ _` |
 | |  | | (_| | |  \__ \ / ____ \| | | | (_| | | |_| | |_| | (_| (_| |
 |_|  |_|\__,_|_|  |___//_/    \_\_| |_|\__,_|_|\__, |\__|_|\___\__,_|
                                                 __/ |
                                                |___/        NSEC 2018


Citizen Access ID:
[...]
[-------------------------------------code-------------------------------------]
   0x403095:	mov    rax,QWORD PTR [rbp-0x5d758]
   0x40309c:	add    rax,rdx
   0x40309f:	jmp    0x401500
=> 0x4030a4:	call   0x4008a0
   0x4030a9:	mov    esi,eax
   0x4030ab:	mov    rax,QWORD PTR [rbp-0x65f40]
   0x4030b2:	sub    eax,0x1
   0x4030b5:	mov    edx,eax
No argument
[...]
Breakpoint 2, 0x00000000004030a4 in ?? ()

gdb-peda$ fulldump
Full dump saved into fulldump.dump
```

The dump is about 55M. The dump contains all memory segments and registers state when the breakpoint
has been reached. So now, we just have to initialize Triton with this concrete state and start the
emulation from the dump. It definitely increases the speed of the execution and now we are able to
emulate the code in ~2 minutes.

## Symbolize the user input and solve constraints

We still know nothing about the binary but we know that it waits for user input using the
`getchar` libc function. So let's hijack this routine during our emulation and symbolize
its return. Note that as we dumped the memory state, the got/plt were already been initialized
with appropriate libc addresses. To have a clean environment we will initialize the plt with
known addresses and when these addresses are executed, we know that we have to call our own
routine.

Once it's done, we emulate the code and when a `getchar` is called, we symbolize its return.
Then, during the emulation we print all instructions that contain symbolic variables. By doing that
we generate a sub-trace that is definitely smaller than the original one (only 1726 instructions)
and that contains only instructions that have a link with our input. This is basically what we
want to extract from big binary and specially from virtual machines. Now we can try to understand what
going on this sub-trace. If we take a look to the [trace](sub-trace-of-sym-instructions) we can see
a lot of `mov` which is a classical behavior of virtual machines (getting and storing context), some
arithmetic operations and conditional jumps. Smells good for us. We will now use the symbolic engine
of Triton to constraint `zf` to be equal to 1 for every conditional jump and see what happens.

```
$ time python solve.py
[+] Define registers
[+] Define memory areas
[+] Define memory 400000-e5e000
[+] Define memory e5e000-105d000
[+] Define memory 105d000-105e000
[+] Define memory 105e000-1080000
[+] Define memory 7ffff7da8000-7ffff7daa000
[+] Define memory 7ffff7daa000-7ffff7dd2000
[+] Define memory 7ffff7dd2000-7ffff7f3d000
[+] Define memory 7ffff7f3d000-7ffff7f94000
[+] Define memory 7ffff7f94000-7ffff7f95000
[+] Define memory 7ffff7f95000-7ffff7f99000
[+] Define memory 7ffff7f99000-7ffff7f9b000
[+] Define memory 7ffff7f9b000-7ffff7fa5000
[+] Define memory 7ffff7fc5000-7ffff7fc6000
[+] Define memory 7ffff7fc6000-7ffff7feb000
[+] Define memory 7ffff7feb000-7ffff7ff5000
[+] Define memory 7ffff7ff5000-7ffff7ff7000
[+] Define memory 7ffff7ff7000-7ffff7ff9000
[+] Define memory 7ffff7ff9000-7ffff7ffd000
[+] Define memory 7ffff7ffd000-7ffff7fff000
[+] Define memory 7ffffff42000-7ffffffff000
[+] Define memory ffffffffff600000-ffffffffff601000
[+] Hijack .plt @0x105E018 -> __free
[+] Hijack .plt @0x105E020 -> __putchar
[+] Hijack .plt @0x105E040 -> __getchar
[+] Hijack .plt @0x105E058 -> __malloc
[+] Hijack .plt @0x105E060 -> __fflush
[+] Hijack .plt @0x105E029 -> __puts
[+] Starting emulation
[+] 100,000 instructions executed
[+] 200,000 instructions executed
[+] 300,000 instructions executed
[+] 400,000 instructions executed
[+] 500,000 instructions executed
[+] 600,000 instructions executed
[+] 700,000 instructions executed
[+] Serial in construction: ",000007000$0P/c00@0"
[+] Serial in construction: "0@`xP@-@``DAp'!``@3"
[+] 800,000 instructions executed
[+] 900,000 instructions executed
[+] 1,000,000 instructions executed
[+] Serial in construction: "`:@``A7P`B0``9!yE+@"
[+] Serial in construction: "hP`MP(7!@c(BX3co[AM"
[+] Serial in construction: "A)<;7A-`pa@0m&!zZ@`"
[+] 1,100,000 instructions executed
[+] 1,200,000 instructions executed
[+] 1,300,000 instructions executed
[+] Serial in construction: "b(S;$@yAtA00n=-`?%d"
[+] Serial in construction: "e17~,C-^`C@sz1!|T:|"
[+] 1,400,000 instructions executed
[+] Serial in construction: "`0A{"`!W`##ppD7rqWx"
[+] Serial in construction: "a=Bd"^yMg$-Y`0-kjPp"
[+] Serial in construction: "o7Pz$d!>w(*oX'7]bH{"
[+] Serial in construction: "o=:H5Tc_l83=zB!ylRt"
[+] 1,500,000 instructions executed
[+] Serial in construction: "{?@X+cc>h55MyA!s^DY"
[+] Serial in construction: "q4Eo-eyMq-1dd0-leKx"
[+] Serial in construction: "q4Eo-eyMq-1dd0-leKx"
[+] Serial in construction: "q4Eo-eyMq-1dd0-leKx"
[+] 1,600,000 instructions executed
[+] Serial in construction: "q4Eo-eyMq-1dd0-leKx"
[+] Serial in construction: "q4Eo-eyMq-1dd0-leKx"
[+] End point reached
[+] Final serial found: q4Eo-eyMq-1dd0-leKx
[+] Emulation done

python solve.py  136.84s user 0.56s system 99% cpu 2:17.53 total
```

Looks like a serial has been generated, let's try it for real.

```
$ ./MarsAnalytica
  __  __                                      _       _   _
 |  \/  |                   /\               | |     | | (_)
 | \  / | __ _ _ __ ___    /  \   _ __   __ _| |_   _| |_ _  ___ __ _
 | |\/| |/ _` | '__/ __|  / /\ \ | '_ \ / _` | | | | | __| |/ __/ _` |
 | |  | | (_| | |  \__ \ / ____ \| | | | (_| | | |_| | |_| | (_| (_| |
 |_|  |_|\__,_|_|  |___//_/    \_\_| |_|\__,_|_|\__, |\__|_|\___\__,_|
                                                 __/ |
                                                |___/        NSEC 2018


Citizen Access ID: q4Eo-eyMq-1dd0-leKx

[+] ACCESS GRANTED!

**  FLAG-l0rdoFb1Nq4EoeyMq1dd0leKx  **

[-] Session Terminated
```


## Going further, lifting the path predicate to LLVM

Back to Toshi's words:

> Unfortunately, I couldn’t get Triton to run on this binary but I’d love to see
> someone reconstruct the source using this same technique!

Ok, let's just get the path predicate generated by Triton and let's use our
lifting engine.

```python
def lifting2llvm(ctx):
   predicate = ctx.getPathPredicate()
   M = ctx.liftToLLVM(predicate, fname="mars_analytica", optimize=True)
   print(M)
   return
```

Result:

```llvm
; ModuleID = 'tritonModule'
source_filename = "tritonModule"

; Function Attrs: mustprogress nofree norecurse nosync nounwind readnone willreturn
define i1 @mars_analytica(i8 %SymVar_0, i8 %SymVar_1, i8 %SymVar_4, i8 %SymVar_3, i8 %SymVar_2, i8 %SymVar_7, i8 %SymVar_6, i8 %SymVar_5, i8 %SymVar_11, i8 %SymVar_8, i8 %SymVar_9, i8 %SymVar_10, i8 %SymVar_14, i8 %SymVar_12, i8 %SymVar_13, i8 %SymVar_15, i8 %SymVar_16, i8 %SymVar_18, i8 %SymVar_17) local_unnamed_addr #0 {
entry:
  %0 = zext i8 %SymVar_13 to i32
  %1 = zext i8 %SymVar_5 to i32
  %2 = add nuw nsw i32 %0, %1
  %3 = zext i8 %SymVar_16 to i32
  %4 = mul nuw nsw i32 %2, %3
  %.not = icmp eq i32 %4, 15049
  %5 = zext i8 %SymVar_15 to i32
  %6 = zext i8 %SymVar_3 to i32
  %7 = mul nuw nsw i32 %5, %6
  %8 = zext i8 %SymVar_2 to i32
  %9 = zext i8 %SymVar_11 to i32
  %10 = mul nuw nsw i32 %9, %8
  %narrow = add nuw nsw i32 %7, %10
  %.not1 = icmp eq i32 %narrow, 18888
  %11 = zext i8 %SymVar_4 to i32
  %12 = zext i8 %SymVar_18 to i32
  %13 = mul nuw nsw i32 %12, %11
  %14 = zext i8 %SymVar_12 to i32
  %15 = sub nsw i32 %5, %14
  %.neg = add nsw i32 %15, %13
  %.not2 = icmp eq i32 %.neg, 5408
  %16 = zext i8 %SymVar_6 to i32
  %17 = mul nuw nsw i32 %9, %16
  %18 = zext i8 %SymVar_1 to i32
  %19 = mul nuw nsw i32 %6, %18
  %narrow3 = add nuw nsw i32 %17, %19
  %.not4 = icmp eq i32 %narrow3, 17872
  %20 = xor i8 %SymVar_14, %SymVar_7
  %21 = zext i8 %20 to i32
  %22 = zext i8 %SymVar_17 to i32
  %23 = mul nuw nsw i32 %22, %21
  %.not5 = icmp eq i32 %23, 7200
  %24 = zext i8 %SymVar_0 to i32
  %25 = add nuw nsw i32 %8, %24
  %26 = sub nsw i32 %25, %1
  %.neg6 = add nsw i32 %26, %3
  %.not7 = icmp eq i32 %.neg6, 182
  %27 = zext i8 %SymVar_9 to i32
  %28 = zext i8 %SymVar_10 to i32
  %29 = zext i8 %SymVar_8 to i32
  %30 = mul nuw nsw i32 %28, %29
  %31 = add nuw nsw i32 %30, %27
  %narrow8 = add nuw nsw i32 %31, %0
  %.not9 = icmp eq i32 %narrow8, 5630
  %32 = add nuw nsw i32 %6, %14
  %.neg10 = sub nsw i32 %1, %32
  %.not11 = icmp eq i32 %.neg10, -110
  %33 = zext i8 %SymVar_7 to i32
  %34 = zext i8 %SymVar_14 to i32
  %35 = mul nuw nsw i32 %0, %34
  %.neg12 = sub nsw i32 %33, %35
  %.not13 = icmp eq i32 %.neg12, -2083
  %36 = mul nuw nsw i32 %3, %8
  %37 = xor i8 %SymVar_17, %SymVar_0
  %38 = zext i8 %37 to i32
  %39 = mul nuw nsw i32 %38, %18
  %narrow14 = add nuw nsw i32 %39, %36
  %.not15 = icmp eq i32 %narrow14, 9985
  %40 = xor i8 %SymVar_10, %SymVar_9
  %41 = zext i8 %40 to i32
  %42 = add nuw nsw i32 %9, %12
  %43 = sub nsw i32 %41, %42
  %44 = xor i32 %43, %16
  %.not16 = icmp eq i32 %44, -199
  %45 = sub nsw i32 %29, %11
  %46 = add nsw i32 %45, %5
  %.not19 = icmp eq i32 %46, 176
  %47 = add nuw nsw i32 %8, %11
  %48 = xor i32 %47, %29
  %.not20 = icmp eq i32 %48, 3
  %.neg21 = sub nsw i32 %9, %6
  %.not22 = icmp eq i32 %.neg21, -11
  %.neg23 = sub nsw i32 %3, %22
  %49 = add nuw nsw i32 %27, %1
  %50 = xor i32 %49, %24
  %.neg24 = mul nsw i32 %.neg23, %50
  %.not25 = icmp eq i32 %.neg24, 5902
  %51 = sub nsw i32 %5, %33
  %52 = xor i8 %SymVar_18, %SymVar_1
  %53 = zext i8 %52 to i32
  %54 = xor i32 %51, %53
  %.not26 = icmp eq i32 %54, 83
  %55 = mul nuw nsw i32 %34, %16
  %56 = sub nsw i32 %14, %28
  %57 = xor i32 %56, %0
  %58 = mul nsw i32 %55, %57
  %.not27 = icmp eq i32 %58, 16335
  %SymVar_18.off = add i8 %SymVar_18, -33
  %59 = icmp ult i8 %SymVar_18.off, 94
  %SymVar_17.off = add i8 %SymVar_17, -33
  %60 = icmp ult i8 %SymVar_17.off, 94
  %SymVar_16.off = add i8 %SymVar_16, -33
  %61 = icmp ult i8 %SymVar_16.off, 94
  %SymVar_15.off = add i8 %SymVar_15, -33
  %62 = icmp ult i8 %SymVar_15.off, 94
  %SymVar_14.off = add i8 %SymVar_14, -33
  %63 = icmp ult i8 %SymVar_14.off, 94
  %SymVar_13.off = add i8 %SymVar_13, -33
  %64 = icmp ult i8 %SymVar_13.off, 94
  %SymVar_12.off = add i8 %SymVar_12, -33
  %65 = icmp ult i8 %SymVar_12.off, 94
  %SymVar_11.off = add i8 %SymVar_11, -33
  %66 = icmp ult i8 %SymVar_11.off, 94
  %SymVar_10.off = add i8 %SymVar_10, -33
  %67 = icmp ult i8 %SymVar_10.off, 94
  %SymVar_9.off = add i8 %SymVar_9, -33
  %68 = icmp ult i8 %SymVar_9.off, 94
  %SymVar_8.off = add i8 %SymVar_8, -33
  %69 = icmp ult i8 %SymVar_8.off, 94
  %SymVar_7.off = add i8 %SymVar_7, -33
  %70 = icmp ult i8 %SymVar_7.off, 94
  %SymVar_6.off = add i8 %SymVar_6, -33
  %71 = icmp ult i8 %SymVar_6.off, 94
  %SymVar_5.off = add i8 %SymVar_5, -33
  %72 = icmp ult i8 %SymVar_5.off, 94
  %SymVar_4.off = add i8 %SymVar_4, -33
  %73 = icmp ult i8 %SymVar_4.off, 94
  %SymVar_3.off = add i8 %SymVar_3, -33
  %74 = icmp ult i8 %SymVar_3.off, 94
  %SymVar_2.off = add i8 %SymVar_2, -33
  %75 = icmp ult i8 %SymVar_2.off, 94
  %SymVar_1.off = add i8 %SymVar_1, -33
  %76 = icmp ult i8 %SymVar_1.off, 94
  %SymVar_0.off = add i8 %SymVar_0, -33
  %77 = icmp ult i8 %SymVar_0.off, 94
  %78 = and i1 %77, %76
  %79 = and i1 %78, %75
  %80 = and i1 %74, %79
  %81 = and i1 %73, %80
  %82 = and i1 %81, %72
  %83 = and i1 %71, %82
  %84 = and i1 %70, %83
  %85 = and i1 %69, %84
  %86 = and i1 %68, %85
  %87 = and i1 %67, %86
  %88 = and i1 %66, %87
  %89 = and i1 %65, %88
  %90 = and i1 %64, %89
  %91 = and i1 %63, %90
  %92 = and i1 %62, %91
  %93 = and i1 %61, %92
  %94 = and i1 %60, %93
  %95 = and i1 %59, %94
  %96 = and i1 %77, %95
  %97 = and i1 %76, %96
  %98 = and i1 %75, %97
  %99 = and i1 %74, %98
  %100 = and i1 %73, %99
  %101 = and i1 %72, %100
  %102 = and i1 %71, %101
  %103 = and i1 %70, %102
  %104 = and i1 %69, %103
  %105 = and i1 %68, %104
  %106 = and i1 %67, %105
  %107 = and i1 %66, %106
  %108 = and i1 %65, %107
  %109 = and i1 %64, %108
  %110 = and i1 %63, %109
  %111 = and i1 %62, %110
  %112 = and i1 %61, %111
  %113 = and i1 %60, %112
  %114 = and i1 %59, %113
  %115 = and i1 %.not27, %114
  %116 = and i1 %.not26, %115
  %117 = and i1 %.not25, %116
  %118 = and i1 %.not22, %117
  %119 = and i1 %.not20, %118
  %120 = and i1 %.not19, %119
  %121 = and i1 %.not16, %120
  %122 = and i1 %.not15, %121
  %123 = and i1 %.not13, %122
  %124 = and i1 %.not11, %123
  %125 = and i1 %.not9, %124
  %126 = and i1 %.not7, %125
  %127 = and i1 %.not5, %126
  %128 = and i1 %.not4, %127
  %129 = and i1 %.not2, %128
  %130 = and i1 %.not1, %129
  %131 = and i1 %.not, %130
  ret i1 %131
}

attributes #0 = { mustprogress nofree norecurse nosync nounwind readnone willreturn }
```

It was easy because it looks like the virtual code contains only one basic block
(it was also the case for Tigress challenges).


# Conclusion

Even if the challenge is 4 years old, I thought it would be interesting to talk
about a potential methodology when analyzing a big binary with Triton. Hope you
are no longer afraid about using Triton ! :)
