#!/usr/bin/env python
## -*- coding: utf-8 -*-
##
## According to the paper https://arxiv.org/pdf/2109.03698.pdf, they implemented
## three ways (LIN, ITE and BST) to handle symbolic memory pointers. In this example,
## we show you an example of their ITE implementation. The idea is to emulate the following
## piece of code where a table is used with a symbolic index. As you know, Triton
## does not handle memory array and so we have to deal with it. However, it's possible
## to simulate the behavior of a symbolic pointer by enumerating all its potential values.
## In this example we only handle symbolic LOAD (not STORE) of their ITE algorithm.
## Hope it can give some fresh ideas for interested people =).
##
## Use case:
##
##      int table[7] = {3, 7, 14, 0, 5, 11, 9};
##
##      int foo(int a) {
##        if (!(a >= 0 && a <=6))
##          return 0;
##        int res = table[a];
##        if (res == 5) {
##          return 1;
##        }
##        return 0;
##      }
##
## Output:
##      $ ./symbolic_pointers_reasoning.py
##      0x1125: push rbp
##      0x1126: mov rbp, rsp
##      0x1129: mov dword ptr [rbp - 0x14], edi
##      0x112c: cmp dword ptr [rbp - 0x14], 0
##      0x1130: js 0x1138
##      0x1132: cmp dword ptr [rbp - 0x14], 6
##      0x1136: jle 0x113f
##      0x113f: mov eax, dword ptr [rbp - 0x14]
##      0x1142: cdqe
##      0x1144: lea rdx, [rax*4]
##      0x114c: lea rax, [rip + 0x2edd]
##      0x1153: mov eax, dword ptr [rdx + rax]
##      	`+--> Symbolic reasoning on the memory access [@0x4030]:32 bv[31..0]
##      	`+--> Formula of the effective address: (bvadd (bvadd ref!42 (bvmul ref!44 (_ bv1 64))) (_ bv0 64))
##      	`+--> The symbolic index can be equal to: [0, 1, 2, 3, 4, 5, 6]
##      	`+--> The symbolic read can be hit the following address: [16432, 16436, 16440, 16444, 16448, 16452, 16456]
##      	`+--> If sym_index:32 is equal to 0 then the loaded value is 3
##      	`+--> If sym_index:32 is equal to 1 then the loaded value is 7
##      	`+--> If sym_index:32 is equal to 2 then the loaded value is 14
##      	`+--> If sym_index:32 is equal to 3 then the loaded value is 0
##      	`+--> If sym_index:32 is equal to 4 then the loaded value is 5
##      	`+--> If sym_index:32 is equal to 5 then the loaded value is 11
##      	`+--> If sym_index:32 is equal to 6 then the loaded value is 9
##      	`+--> Crafting the new symbolic expression assigned to rax:64 bv[63..0]
##      0x1156: mov dword ptr [rbp - 4], eax
##      0x1159: cmp dword ptr [rbp - 4], 5
##      0x115d: jne 0x1166
##      0x1166: mov eax, 0
##      0x116b: pop rbp
##      0x116c: ret
##
##      ---> If you want to load the value 5 the symbolic index must be equal to 4
##

import sys
from triton import *

# .data:0000000000004030                 public table
# .data:0000000000004030 table           dd 3                    ; DATA XREF: foo+14↑o
# .data:0000000000004034                 dd 7
# .data:0000000000004038                 dd 14
# .data:000000000000403C                 dd 0
# .data:0000000000004040                 dd 5
# .data:0000000000004044                 dd 11
# .data:0000000000004048                 dd 9
#
# NOTE: If you want, you can switch the value 5 to another position
DATA = [3, 7, 14, 0, 5, 11, 9]

# .text:0000000000001125                 public foo
# .text:0000000000001125 foo             proc near
# .text:0000000000001125
# .text:0000000000001125 var_14          = dword ptr -14h
# .text:0000000000001125 var_4           = dword ptr -4
# .text:0000000000001125
# .text:0000000000001125 ; __unwind {
# .text:0000000000001125                 push    rbp
# .text:0000000000001126                 mov     rbp, rsp
# .text:0000000000001129                 mov     [rbp+var_14], edi
# .text:000000000000112C                 cmp     [rbp+var_14], 0
# .text:0000000000001130                 js      short loc_1138
# .text:0000000000001132                 cmp     [rbp+var_14], 6
# .text:0000000000001136                 jle     short loc_113F
# .text:0000000000001138
# .text:0000000000001138 loc_1138:                               ; CODE XREF: foo+B↑j
# .text:0000000000001138                 mov     eax, 0
# .text:000000000000113D                 jmp     short loc_116B
# .text:000000000000113F ; ---------------------------------------------------------------------------
# .text:000000000000113F
# .text:000000000000113F loc_113F:                               ; CODE XREF: foo+11↑j
# .text:000000000000113F                 mov     eax, [rbp+var_14]
# .text:0000000000001142                 cdqe
# .text:0000000000001144                 lea     rdx, ds:0[rax*4]
# .text:000000000000114C                 lea     rax, table
# .text:0000000000001153                 mov     eax, [rdx+rax]
# .text:0000000000001156                 mov     [rbp+var_4], eax
# .text:0000000000001159                 cmp     [rbp+var_4], 5
# .text:000000000000115D                 jnz     short loc_1166
# .text:000000000000115F                 mov     eax, 1
# .text:0000000000001164                 jmp     short loc_116B
# .text:0000000000001166 ; ---------------------------------------------------------------------------
# .text:0000000000001166
# .text:0000000000001166 loc_1166:                               ; CODE XREF: foo+38↑j
# .text:0000000000001166                 mov     eax, 0
# .text:000000000000116B
# .text:000000000000116B loc_116B:                               ; CODE XREF: foo+18↑j
# .text:000000000000116B                                         ; foo+3F↑j
# .text:000000000000116B                 pop     rbp
# .text:000000000000116C                 retn
#
# NOTE: The code below is the x86_64 bytecode of the above function
CODE  = "554889E5897DEC837DEC007806837DEC067E07B800000000EB2C8B45EC4898488D148500000000488D05DD2E00008B04028945FC837DFC057507B801000000EB05B8000000005DC3"
# Entry point of the function and thus of our emulation
ENTRY = 0x1125

# READ Effective Address
R_EA = None

# Boundary limit
BOUNDARY = 100


def save_read_ea(ctx, mem):
    global R_EA
    if mem.getLeaAst():
        R_EA = mem




def symbolic_read_reasoning(ctx, inst, mem):
    addr = mem.getAddress()
    size = mem.getSize()
    lea  = mem.getLeaAst()
    ast  = ctx.getAstContext()
    pp   = ctx.getPathPredicate()

    # Returns all possible indexes
    def get_indexes(models):
        indexes = []
        for m in models:
            for _, v in m.items():
                indexes.append(v.getValue())
        return sorted(indexes)

    # Returns all addresses that may be hit
    def get_addresses(ctx, lea, models):
        addr = []
        var  = ctx.getSymbolicVariable(0)
        org  = ctx.getConcreteVariableValue(var)
        for index in get_indexes(models):
            ctx.setConcreteVariableValue(var, index)
            addr.append(lea.evaluate())
        ctx.setConcreteVariableValue(var, org)
        return addr

    # Returns the dst register where the load is stored
    def get_dst(ctx, inst, mem):
        for mem, load_ast in inst.getLoadAccess():
            for node in load_ast.getParents():
                for se in inst.getSymbolicExpressions():
                    if se.getAst().equalTo(node):
                        return se.getOrigin()
        return None

    # Maps a sym index to a loaded value
    def map_index_result(ctx, mem, models):
        res = {}
        var = ctx.getSymbolicVariable(0)
        org = ctx.getConcreteVariableValue(var)
        for index in get_indexes(models):
            ctx.setConcreteVariableValue(var, index)
            load = MemoryAccess(mem.getLeaAst().evaluate(), mem.getSize())
            res.update({index : ctx.getMemoryAst(load)})
        ctx.setConcreteVariableValue(var, org)
        return res

    # Build the recursive ITE
    def build_ite(ctx, mem, models):
            ast = ctx.getAstContext()
            var = ctx.getSymbolicVariable(0)
            mapping = map_index_result(ctx, mem, models)
            res = ast.bv(mem.getBitvector().getMaxValue(), 32) # max value for -1 but should never be used
            for k, v in mapping.items():
                print(f"\t`+--> If {var} is equal to {k} then the loaded value is {v.evaluate()}")
                res = ast.ite(ast.variable(var) == k, v, res)
            return res

    if lea.isSymbolized():
        print(f"\t`+--> Symbolic reasoning on the memory access {mem}")
        print(f"\t`+--> Formula of the effective address: {lea}")
        models = ctx.getModels(ast.land([pp, lea > 0]), BOUNDARY)
        print(f"\t`+--> The symbolic index can be equal to: {get_indexes(models)}")
        print(f"\t`+--> The symbolic read can be hit the following address: {get_addresses(ctx, lea, models)}")
        dst = get_dst(ctx, inst, mem)
        node = build_ite(ctx, mem, models)
        node = ast.zx(dst.getBitSize() - node.getBitvectorSize(), node)
        print(f"\t`+--> Crafting the new symbolic expression assigned to {dst}")
        expr = ctx.newSymbolicExpression(node, "Symbolic read over ITE expressions")
        ctx.assignSymbolicExpressionToRegister(expr, dst)

    return


def emulate(ctx, pc):
    global R_EA

    while pc:
        # Fetch opcode
        opcode = ctx.getConcreteMemoryAreaValue(pc, 16)

        # Create the Triton instruction
        inst = Instruction(pc, opcode)

        # Process the instruction
        ctx.processing(inst)
        print(inst)
        if R_EA:
            symbolic_read_reasoning(ctx, inst, R_EA)
            R_EA = None

        # Next instruction
        pc = ctx.getConcreteRegisterValue(ctx.registers.rip)

    return


# Note that this following function is very specific to our use case.
# It's just used as a proof to see if we successfully managed to handle the
# symbolic read at 0x115D.
def ask_model(ctx):
    ast = ctx.getAstContext()
    # Pop the last constraint at 0x115D
    #.text:0000000000001159     cmp     [rbp+var_4], 5
    #.text:000000000000115D     jnz     short loc_1166
    ctx.popPathConstraint()
    # Force the jnz at 0x115D to be valide. 61 is the reference id to ZF.
    ctx.pushPathConstraint(ast.reference(ctx.getSymbolicExpression(61)) == 1)
    # Ask for model
    model = ctx.getModel(ctx.getPathPredicate())
    print(f'\n---> If you want to load the value 5 the symbolic index must be equal to {model[0].getValue()}')


if __name__ == "__main__":
    ctx = TritonContext(ARCH.X86_64)

    # Add callbacks
    ctx.addCallback(CALLBACK.GET_CONCRETE_MEMORY_VALUE, save_read_ea)

    # Load the CODE part
    ctx.setConcreteMemoryAreaValue(ENTRY, bytes.fromhex(CODE))
    ctx.setConcreteRegisterValue(ctx.registers.rip, ENTRY)
    ctx.setConcreteRegisterValue(ctx.registers.rsp, 0x1ffffffff)
    ctx.setConcreteRegisterValue(ctx.registers.rbp, 0x1ffffffff)

    # Load the DATA part
    for index, item in enumerate(DATA):
        ctx.setConcreteMemoryValue(MemoryAccess(0x4030 + (index * CPUSIZE.DWORD), CPUSIZE.DWORD), item)

    # Symbolize the argument of the foo function
    ctx.symbolizeRegister(ctx.registers.edi, "sym_index")

    # Emulate the code
    emulate(ctx, ENTRY)

    # Try to invert the symbolic branch
    ask_model(ctx)

    sys.exit(0)
