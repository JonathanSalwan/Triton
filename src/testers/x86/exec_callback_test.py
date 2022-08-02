from triton import *

function = {
	0x401000: b"\x55",                 #  push   ebp
	0x401001: b"\x8b\xec",             #  mov    ebp,             esp
	0x401003: b"\x6b\x45\x08\x06",     #  imul   eax,             DWORD PTR [ebp+0x8], 0x6
	0x401007: b"\x8b\x4d\x0c",         #  mov    ecx,             DWORD PTR [ebp+0xc]
	0x40100a: b"\x89\x01",             #  mov    DWORD PTR [ecx], eax
	0x40100c: b"\xb8\x01\x00\x00\x00", #  mov    eax,             0x1
	0x401011: b"\x5d",                 #  pop    ebp
	0x401012: b"\xc3",                 #  ret
}

expect = [
    ('REG', 'R', 'ebp', 0x7ffff0),
    ('REG', 'R', 'esp', 0x7ffff0),
    ('REG', 'W', 'esp', 0x7fffec),
    ('MEM', 'W', MemoryAccess(0x7fffec, 4), 0x7ffff0),
    ('REG', 'W', 'eip', 0x401001),
    ('REG', 'R', 'esp', 0x7fffec),
    ('REG', 'W', 'ebp', 0x7fffec),
    ('REG', 'W', 'eip', 0x401003),
    ('REG', 'R', 'ebp', 0x7fffec),
    ('MEM', 'R', MemoryAccess(0x7ffff4, 4), 0x4),
    ('REG', 'R', 'ebp', 0x7fffec),
    ('REG', 'R', 'ebp', 0x7fffec),
    ('REG', 'W', 'eax', 0x18),
    ('REG', 'W', 'cf', 0x0),
    ('REG', 'W', 'of', 0x0),
    ('REG', 'W', 'eip', 0x401007),
    ('REG', 'R', 'ebp', 0x7fffec),
    ('MEM', 'R', MemoryAccess(0x7ffff8, 4), 0x5fffa0),
    ('REG', 'R', 'ebp', 0x7fffec),
    ('REG', 'R', 'ebp', 0x7fffec),
    ('REG', 'W', 'ecx', 0x5fffa0),
    ('REG', 'W', 'eip', 0x40100a),
    ('REG', 'R', 'ecx', 0x5fffa0),
    ('REG', 'R', 'eax', 0x18),
    ('REG', 'R', 'ecx', 0x5fffa0),
    ('MEM', 'W', MemoryAccess(0x5fffa0, 4), 0x18),
    ('REG', 'W', 'eip', 0x40100c),
    ('REG', 'W', 'eax', 0x1),
    ('REG', 'W', 'eip', 0x401011),
    ('REG', 'R', 'esp', 0x7fffec),
    ('MEM', 'R', MemoryAccess(0x7fffec, 4), 0x7ffff0),
    ('REG', 'W', 'ebp', 0x7ffff0),
    ('REG', 'R', 'esp', 0x7fffec),
    ('REG', 'W', 'esp', 0x7ffff0),
    ('REG', 'W', 'eip', 0x401012),
    ('REG', 'R', 'esp', 0x7ffff0),
    ('MEM', 'R', MemoryAccess(0x7ffff0, 4), 0x400400),
    ('REG', 'W', 'eip', 0x400400),
    ('REG', 'R', 'esp', 0x7ffff0),
    ('REG', 'W', 'esp', 0x7ffff4),
]

actual = list()

trace = iter(expect)

log_trace = False

def mem_read_cb(tt, mem):
    if log_trace:
        print('(\'MEM\', \'R\', MemoryAccess({}, {}), {}),'.format(
            hex(mem.getAddress()),
            mem.getSize(),
            hex(tt.getConcreteMemoryValue(mem, execCallbacks=False)),
        ))
        return
    event = next(trace, None)
    assert(event is not None)
    (eType, eAction, eTarget, eValue) = event
    assert(eType == 'MEM')
    assert(eAction == 'R')
    assert(eTarget.getSize() == mem.getSize())
    assert(eTarget.getAddress() == mem.getAddress())
    tValue = tt.getConcreteMemoryValue(mem, execCallbacks=False)
    if tValue != eValue:
        assert(tValue == 0)
        tt.setConcreteMemoryValue(mem, eValue, execCallbacks=False)
    actual.append(event)

def mem_write_cb(tt, mem, value):
    if log_trace:
        print('(\'MEM\', \'W\', MemoryAccess({}, {}), {}),'.format(
            hex(mem.getAddress()),
            mem.getSize(),
            hex(value),
        ))
        return
    event = next(trace, None)
    assert(event is not None)
    (eType, eAction, eTarget, eValue) = event
    assert(eType == 'MEM')
    assert(eAction == 'W')
    assert(eTarget.getSize() == mem.getSize())
    assert(eTarget.getAddress() == mem.getAddress())
    assert(eValue == value)
    actual.append(event)

def reg_read_cb(tt, reg):
    if log_trace:
        print('(\'REG\', \'R\', \'{}\', {}),'.format(
            reg.getName(),
            hex(tt.getConcreteRegisterValue(reg, execCallbacks=False)),
        ))
        return
    event = next(trace, None)
    assert(event is not None)
    (eType, eAction, eTarget, eValue) = event
    assert(eType == 'REG')
    assert(eAction == 'R')
    assert(eTarget == reg.getName())
    tValue = tt.getConcreteRegisterValue(reg, execCallbacks=False)
    if tValue != eValue:
        assert(tValue == 0)
        tt.setConcreteRegisterValue(reg, eValue, execCallbacks=False)
    actual.append(event)

def reg_write_cb(tt, reg, value):
    if log_trace:
        print('(\'REG\', \'W\', \'{}\', {}),'.format(
            reg.getName(),
            hex(value),
        ))
        return
    event = next(trace, None)
    assert(event is not None)
    (eType, eAction, eTarget, eValue) = event
    assert(eType == 'REG')
    assert(eAction == 'W')
    assert(eTarget == reg.getName())
    assert(eValue == value)
    actual.append(event)

tt = TritonContext()
tt.setArchitecture(ARCH.X86)
tt.setMode(MODE.ALIGNED_MEMORY, True)
tt.setAstRepresentationMode(AST_REPRESENTATION.PYTHON)

if log_trace:
    tt.setConcreteRegisterValue(tt.registers.ebp, 0x7FFFF0)
    tt.setConcreteRegisterValue(tt.registers.esp, 0x7FFFF0)
    tt.setConcreteRegisterValue(tt.registers.esp, 0x7FFFF0)
    tt.setConcreteMemoryValue(MemoryAccess(0x7FFFF0, 4), 0x400400)
    tt.setConcreteMemoryValue(MemoryAccess(0x7FFFF4, 4), 4)
    tt.setConcreteMemoryValue(MemoryAccess(0x7FFFF8, 4), 0x5FFFA0)

tt.addCallback(CALLBACK.GET_CONCRETE_MEMORY_VALUE, mem_read_cb)
tt.addCallback(CALLBACK.SET_CONCRETE_MEMORY_VALUE, mem_write_cb)
tt.addCallback(CALLBACK.GET_CONCRETE_REGISTER_VALUE, reg_read_cb)
tt.addCallback(CALLBACK.SET_CONCRETE_REGISTER_VALUE, reg_write_cb)

pc = 0x401000
while pc in function:
    inst = Instruction(pc, function[pc])
    tt.processing(inst)
    pc = tt.getConcreteRegisterValue(tt.registers.eip, execCallbacks=False)

assert(expect == actual)
