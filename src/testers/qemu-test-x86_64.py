# $ ./triton ./src/testers/qemu-test-x86_64.py ./src/samples/ir_test_suite/qemu-test-x86_64

from triton import ARCH, SYMEXPR, OPCODE
import pintool as Pintool

# Get the Triton context over the pintool
Triton = Pintool.getTritonContext()


def sbefore(instruction):
    Triton.concretizeAllMemory()
    Triton.concretizeAllRegister()
    return


def cafter(instruction):

    ofIgnored = [
        OPCODE.RCL,
        OPCODE.RCR,
        OPCODE.ROL,
        OPCODE.ROR,
        OPCODE.SAR,
        OPCODE.SHL,
        OPCODE.SHLD,
        OPCODE.SHR,
        OPCODE.SHRD,
    ]

    bad  = list()
    regs = Triton.getParentRegisters()

    for reg in regs:

        cvalue = Pintool.getCurrentRegisterValue(reg)
        seid   = Triton.getSymbolicRegisterId(reg)

        if seid == SYMEXPR.UNSET:
            continue

        expr   = Triton.getFullAstFromId(seid)
        svalue = expr.evaluate()
        #svalue = Triton.evaluateAstViaZ3(expr)

        # Check register
        if cvalue != svalue:

            if reg.getName() == 'of' and instruction.getType() in ofIgnored:
                continue

            bad.append({
                'reg':    reg.getName() + str(instruction.getType()),
                'svalue': svalue,
                'cvalue': cvalue,
                'expr':   expr
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

    # Reset everything
    Triton.resetEngines()

    return


if __name__ == '__main__':
    Triton.setArchitecture(ARCH.X86_64)
    Pintool.setupImageWhitelist(['qemu-test-x86_64'])
    Pintool.startAnalysisFromSymbol('main')
    Pintool.insertCall(cafter,  Pintool.INSERT_POINT.AFTER)
    Pintool.insertCall(sbefore, Pintool.INSERT_POINT.BEFORE_SYMPROC)
    Pintool.runProgram()
