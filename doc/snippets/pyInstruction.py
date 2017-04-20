# [Instruction code]
>>> from triton import TritonContext, ARCH, Instruction, OPERAND

>>> trace = [
...     (0x400000, "\x48\x8b\x05\xb8\x13\x00\x00"), # mov        rax, QWORD PTR [rip+0x13b8]
...     (0x400007, "\x48\x8d\x34\xc3"),             # lea        rsi, [rbx+rax*8]
...     (0x40000b, "\x67\x48\x8D\x74\xC3\x0A"),     # lea        rsi, [ebx+eax*8+0xa]
...     (0x400011, "\x66\x0F\xD7\xD1"),             # pmovmskb   edx, xmm1
...     (0x400015, "\x89\xd0"),                     # mov        eax, edx
...     (0x400017, "\x80\xf4\x99"),                 # xor        ah, 0x99
... ]

>>> ctxt = TritonContext()

# Set the arch
>>> ctxt.setArchitecture(ARCH.X86_64)

>>> for (addr, opcodes) in trace:
...
...     # Build an instruction
...     inst = Instruction()
...
...     # Setup opcodes
...     inst.setOpcodes(opcodes)
...
...     # Setup Address
...     inst.setAddress(addr)
...
...     # Process everything
...     if not ctxt.processing(inst):
...         print "Fail an instruction"
...
...     print inst
...     for op in inst.getOperands():
...         print '   ', op
...         if op.getType() == OPERAND.MEM:
...             print '         base  : ', op.getBaseRegister()
...             print '         index : ', op.getIndexRegister()
...             print '         disp  : ', op.getDisplacement()
...             print '         scale : ', op.getScale()
...     print
... # [Instruction code]
0x400000: mov rax, qword ptr [rip + 0x13b8]
    rax:64 bv[63..0]
    [@0x4013bf]:64 bv[63..0]
         base  :  rip:64 bv[63..0]
         index :  unknown:1 bv[0..0]
         disp  :  0x13b8:64 bv[63..0]
         scale :  0x1:64 bv[63..0]
<BLANKLINE>
0x400007: lea rsi, qword ptr [rbx + rax*8]
    rsi:64 bv[63..0]
    [@0x0]:64 bv[63..0]
         base  :  rbx:64 bv[63..0]
         index :  rax:64 bv[63..0]
         disp  :  0x0:64 bv[63..0]
         scale :  0x8:64 bv[63..0]
<BLANKLINE>
0x40000b: lea rsi, dword ptr [ebx + eax*8 + 0xa]
    rsi:64 bv[63..0]
    [@0xa]:32 bv[31..0]
         base  :  ebx:32 bv[31..0]
         index :  eax:32 bv[31..0]
         disp  :  0xa:32 bv[31..0]
         scale :  0x8:32 bv[31..0]
<BLANKLINE>
0x400011: pmovmskb edx, xmm1
    edx:32 bv[31..0]
    xmm1:128 bv[127..0]
<BLANKLINE>
0x400015: mov eax, edx
    eax:32 bv[31..0]
    edx:32 bv[31..0]
<BLANKLINE>
0x400017: xor ah, 0x99
    ah:8 bv[15..8]
    0x99:8 bv[7..0]
<BLANKLINE>

# [Constructor]
>>> inst = Instruction("\x48\xC7\xC0\x01\x00\x00\x00")
>>> inst.setAddress(0x40000)
>>> ctxt.processing(inst)
True
>>> print inst
0x40000: mov rax, 1

# [Constructor]

# [Constructor bis]
>>> inst = Instruction()
>>> inst.setAddress(0x40000)
>>> inst.setOpcodes("\x48\xC7\xC0\x01\x00\x00\x00")
>>> ctxt.processing(inst)
True
>>> print inst
0x40000: mov rax, 1

# [Constructor bis]
