
# $ ./build/triton ./src/examples/pin/inject_model_with_snapshot.py ./src/samples/crackmes/crackme_xor a
# [+] Take a snapshot at the prologue of the function
# [+] Still not the good password. Restore snapshot.
# [+] Inject the character 'e' in memory
# [+] Still not the good password. Restore snapshot.
# [+] Inject the character 'e' in memory
# [+] Inject the character 'l' in memory
# [+] Still not the good password. Restore snapshot.
# [+] Inject the character 'e' in memory
# [+] Inject the character 'l' in memory
# [+] Inject the character 'i' in memory
# [+] Still not the good password. Restore snapshot.
# [+] Inject the character 'e' in memory
# [+] Inject the character 'l' in memory
# [+] Inject the character 'i' in memory
# [+] Inject the character 't' in memory
# [+] Still not the good password. Restore snapshot.
# [+] Inject the character 'e' in memory
# [+] Inject the character 'l' in memory
# [+] Inject the character 'i' in memory
# [+] Inject the character 't' in memory
# [+] Inject the character 'e' in memory
# [+] Good password found!
# Win
# [+] Analysis done!

from triton     import ARCH
from pintool    import *

password  = dict()
symVarMem = None
Triton    = getTritonContext()


def csym(instruction):
    # Prologue of the function
    if instruction.getAddress() == 0x400556 and isSnapshotEnabled() == False:
        takeSnapshot()
        print '[+] Take a snapshot at the prologue of the function'
        return

    # 0x40058b: movzx eax, byte ptr [rax]
    if instruction.getAddress() == 0x400574:
        global symVarMem
        rax = getCurrentRegisterValue(Triton.registers.rax)
        symVarMem = rax
        if rax in password:
            setCurrentMemoryValue(rax, password[rax])
            print '[+] Inject the character \'%c\' in memory' %(chr(password[rax]))
        return

    # Epilogue of the function
    if instruction.getAddress() == 0x4005b1:
        rax = getCurrentRegisterValue(Triton.registers.rax)
        # The function returns 0 if the password is valid
        # So, we restore the snapshot until this function
        # returns something else than 0.
        if rax != 0:
            print '[+] Still not the good password. Restore snapshot.'
            restoreSnapshot()
        else:
            print '[+] Good password found!'
            disableSnapshot()
        return
    return


def cafter(instruction):
    # 0x40058b: movzx eax, byte ptr [rax]
    if instruction.getAddress() == 0x400574:
        var = Triton.convertRegisterToSymbolicVariable(Triton.registers.rax)
        return

    # 0x4005ae: cmp ecx, eax
    if instruction.getAddress() == 0x400597:
        zfId    = Triton.getSymbolicRegisterId(Triton.registers.zf)
        zfExpr  = Triton.getFullAstFromId(zfId)
        astCtxt = Triton.getAstContext();
        expr    = astCtxt.equal(zfExpr, astCtxt.bvtrue()) # (= zf True)
        models  = Triton.getModel(expr)
        global password
        for k, v in models.items():
            password.update({symVarMem: v.getValue()})
        return

    return


def fini():
    print '[+] Analysis done!'
    return


if __name__ == '__main__':
    # Define the architecture
    Triton.setArchitecture(ARCH.X86_64)

    # Start the symbolic analysis from the 'check' function
    startAnalysisFromSymbol('check')

    insertCall(cafter,  INSERT_POINT.AFTER)
    insertCall(csym,    INSERT_POINT.BEFORE_SYMPROC)
    insertCall(fini,    INSERT_POINT.FINI)

    # Run the instrumentation - Never returns
    runProgram()
