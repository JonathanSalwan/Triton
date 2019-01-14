# $ ./triton ./src/testers/qemu-test-x86_64.py ./src/samples/ir_test_suite/qemu-test-x86_64

from triton import *
import pintool as Pintool

# Get the Triton context over the pintool
Triton = Pintool.getTritonContext()



def needReg(ctx, reg):
    ctx.setConcreteRegisterValue(reg, Pintool.getCurrentRegisterValue(reg))
    return


def needMem(ctx, mem):
    ctx.setConcreteMemoryValue(mem, Pintool.getCurrentMemoryValue(mem))
    return


def sbefore(instruction):
    Triton.reset()
    Triton.addCallback(needReg, CALLBACK.GET_CONCRETE_REGISTER_VALUE)
    Triton.addCallback(needMem, CALLBACK.GET_CONCRETE_MEMORY_VALUE)
    return


def cafter(instruction):

    ofIgnored = [
        OPCODE.X86.RCL,
        OPCODE.X86.RCR,
        OPCODE.X86.ROL,
        OPCODE.X86.ROR,
        OPCODE.X86.SAR,
        OPCODE.X86.SHL,
        OPCODE.X86.SHLD,
        OPCODE.X86.SHR,
        OPCODE.X86.SHRD,
    ]

    bad  = list()
    regs = Triton.getParentRegisters()

    for reg in regs:

        se = Triton.getSymbolicRegister(reg)
        if se is None:
            continue

        svalue = se.getAst().evaluate()
        cvalue = Pintool.getCurrentRegisterValue(reg)

        # Check register
        if cvalue != svalue:

            if reg.getName() == 'of' and instruction.getType() in ofIgnored:
                continue

            bad.append({
                'reg':    reg.getName(),
                'svalue': svalue,
                'cvalue': cvalue,
                'expr':   se.getAst()
            })

    if bad:
        dump = '[KO] %#x: %s (%d register error(s))' %(instruction.getAddress(), instruction.getDisassembly(), len(bad))
        for w in bad:
            dump += '\n     Register       : %s'    %(w['reg'])
            dump += '\n     Symbolic Value : %016x' %(w['svalue'])
            dump += '\n     Concrete Value : %016x' %(w['cvalue'])
            dump += '\n     Expression     : %s'    %(w['expr'])

        print dump
        with open('./semantics_issues', 'a') as fd:
            fd.write(dump+'\n')

    if len(instruction.getSymbolicExpressions()) == 0:
        dump = '[unsupported] %#x: %s' %(instruction.getAddress(), instruction.getDisassembly())
        print dump
        with open('./semantics_issues', 'a') as fd:
            fd.write(dump+'\n')
        return

    return


if __name__ == '__main__':
    Pintool.setupImageWhitelist(['qemu-test-x86_64'])
    Pintool.startAnalysisFromSymbol('main')
    Pintool.insertCall(cafter,  Pintool.INSERT_POINT.AFTER)
    Pintool.insertCall(sbefore, Pintool.INSERT_POINT.BEFORE_SYMPROC)
    Pintool.runProgram()
