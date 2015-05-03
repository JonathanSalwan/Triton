
# Output
#
# $ ../../../pin -t ./triton.so -script ./examples/callback_after.py -- ./samples/crackmes/crackme_xor a
# 0x40056d: push rbp
#          -> #0 = (bvsub (_ bv140735751966024 64) (_ bv8 64)) 
#          -> #1 = (_ bv140735751966064 64) 
#          -> #2 = (_ bv4195694 64) ; RIP
#
# 0x40056e: mov rbp, rsp
#          -> #3 = ((_ extract 63 0) #0) 
#          -> #4 = (_ bv4195697 64) ; RIP
#
# 0x400571: mov qword ptr [rbp-0x18], rdi
#          -> #5 = (_ bv140735751971077 64) 
#          -> #6 = (_ bv4195701 64) ; RIP
#
# 0x400575: mov dword ptr [rbp-0x4], 0x0
#          -> #7 = (_ bv0 32) 
#          -> #8 = (_ bv4195708 64) ; RIP
#
# 0x40057c: jmp 0x4005bd
#
# 0x4005bd: cmp dword ptr [rbp-0x4], 0x4
#          -> #9 = (bvsub #7 ((_ sign_extend 0) (_ bv4 32))) 
#          -> #10 = (ite (= (_ bv16 32) (bvand (_ bv16 32) (bvxor #9 (bvxor #7 ((_ sign_extend 0) (_ bv4 32)))))) (_ bv1 1) (_ bv0 1)) ; Adjust flag
#          -> #11 = (ite (bvult #7 ((_ sign_extend 0) (_ bv4 32))) (_ bv1 1) (_ bv0 1)) ; Carry flag
#          -> #12 = (ite (= ((_ extract 31 31) (bvand (bvxor #7 ((_ sign_extend 0) (_ bv4 32))) (bvxor #7 #9))) (_ bv1 1)) (_ bv1 1) (_ bv0 1)) ; Overflow flag
#          -> #13 = (ite (= (parity_flag ((_ extract 7 0) #9)) (_ bv0 1)) (_ bv1 1) (_ bv0 1)) ; Parity flag
#          -> #14 = (ite (= ((_ extract 31 31) #9) (_ bv1 1)) (_ bv1 1) (_ bv0 1)) ; Sign flag
#          -> #15 = (ite (= #9 (_ bv0 32)) (_ bv1 1) (_ bv0 1)) ; Zero flag
#          -> #16 = (_ bv4195777 64) ; RIP
#
# 0x40057e: mov eax, dword ptr [rbp-0x4]
#          -> #17 = ((_ extract 31 0) #9) 
#          -> #18 = (_ bv4195713 64) ; RIP
#
# 0x400581: movsxd rdx, eax
#          -> #19 = ((_ sign_extend 32) ((_ extract 31 0) #17)) 
#          -> #20 = (_ bv4195716 64) ; RIP
#
# 0x400584: mov rax, qword ptr [rbp-0x18]
#          -> #21 = ((_ extract 63 0) #5) 
#          -> #22 = (_ bv4195720 64) ; RIP
#
# 0x400588: add rax, rdx
#          -> #23 = (bvadd ((_ extract 63 0) #21) ((_ extract 63 0) #19)) 
#          -> #24 = (ite (= (_ bv16 64) (bvand (_ bv16 64) (bvxor #23 (bvxor ((_ extract 63 0) #21) ((_ extract 63 0) #19))))) (_ bv1 1) (_ bv0 1)) ; Adjust flag
#          -> #25 = (ite (bvult #23 ((_ extract 63 0) #21)) (_ bv1 1) (_ bv0 1)) ; Carry flag
#          -> #26 = (ite (= ((_ extract 63 63) (bvand (bvxor ((_ extract 63 0) #21) (bvnot ((_ extract 63 0) #19))) (bvxor ((_ extract 63 0) #21) #23))) (_ bv1 1)) (_ bv1 1) (_ bv0 1)) ; Overflow flag
#          -> #27 = (ite (= (parity_flag ((_ extract 7 0) #23)) (_ bv0 1)) (_ bv1 1) (_ bv0 1)) ; Parity flag
#          -> #28 = (ite (= ((_ extract 63 63) #23) (_ bv1 1)) (_ bv1 1) (_ bv0 1)) ; Sign flag
#          -> #29 = (ite (= #23 (_ bv0 64)) (_ bv1 1) (_ bv0 1)) ; Zero flag
#          -> #30 = (_ bv4195723 64) ; RIP
#
# 0x40058b: movzx eax, byte ptr [rax]
#          -> #31 = ((_ zero_extend 24) (_ bv97 8)) 
#          -> #32 = (_ bv4195726 64) ; RIP
#
# 0x40058e: movsx eax, al
#          -> #33 = ((_ sign_extend 24) ((_ extract 7 0) #31)) 
#          -> #34 = (_ bv4195729 64) ; RIP
#
# 0x400591: sub eax, 0x1
#          -> #35 = (bvsub ((_ extract 31 0) #33) (_ bv1 32)) 
#          -> #36 = (ite (= (_ bv16 32) (bvand (_ bv16 32) (bvxor #35 (bvxor ((_ extract 31 0) #33) (_ bv1 32))))) (_ bv1 1) (_ bv0 1)) ; Adjust flag
#          -> #37 = (ite (bvult ((_ extract 31 0) #33) (_ bv1 32)) (_ bv1 1) (_ bv0 1)) ; Carry flag
#          -> #38 = (ite (= ((_ extract 31 31) (bvand (bvxor ((_ extract 31 0) #33) (_ bv1 32)) (bvxor ((_ extract 31 0) #33) #35))) (_ bv1 1)) (_ bv1 1) (_ bv0 1)) ; Overflow flag
#          -> #39 = (ite (= (parity_flag ((_ extract 7 0) #35)) (_ bv0 1)) (_ bv1 1) (_ bv0 1)) ; Parity flag
#          -> #40 = (ite (= ((_ extract 31 31) #35) (_ bv1 1)) (_ bv1 1) (_ bv0 1)) ; Sign flag
#          -> #41 = (ite (= #35 (_ bv0 32)) (_ bv1 1) (_ bv0 1)) ; Zero flag
#          -> #42 = (_ bv4195732 64) ; RIP
# 
# 0x400594: xor eax, 0x55
#          -> #43 = (bvxor ((_ extract 31 0) #35) (_ bv85 32)) 
#          -> #44 = (_ bv0 1) ; Clear carry flag
#          -> #45 = (_ bv0 1) ; Clear overflow flag
#          -> #46 = (ite (= (parity_flag ((_ extract 7 0) #43)) (_ bv0 1)) (_ bv1 1) (_ bv0 1)) ; Parity flag
#          -> #47 = (ite (= ((_ extract 31 31) #43) (_ bv1 1)) (_ bv1 1) (_ bv0 1)) ; Sign flag
#          -> #48 = (ite (= #43 (_ bv0 32)) (_ bv1 1) (_ bv0 1)) ; Zero flag
#          -> #49 = (_ bv4195735 64) ; RIP
# 
# 0x400597: mov ecx, eax
#          -> #50 = ((_ extract 31 0) #43) 
#          -> #51 = (_ bv4195737 64) ; RIP
# 
# 0x400599: mov rdx, qword ptr [rip+0x200aa0]
#          -> #52 = (_ bv4196036 64) 
#          -> #53 = (_ bv4195744 64) ; RIP
# 
# 0x4005a0: mov eax, dword ptr [rbp-0x4]
#          -> #54 = ((_ extract 31 0) #9) 
#          -> #55 = (_ bv4195747 64) ; RIP
# 
# 0x4005a3: cdqe 
# 
# 0x4005a5: add rax, rdx
#          -> #56 = (bvadd ((_ extract 63 0) #54) ((_ extract 63 0) #52)) 
#          -> #57 = (ite (= (_ bv16 64) (bvand (_ bv16 64) (bvxor #56 (bvxor ((_ extract 63 0) #54) ((_ extract 63 0) #52))))) (_ bv1 1) (_ bv0 1)) ; Adjust flag
#          -> #58 = (ite (bvult #56 ((_ extract 63 0) #54)) (_ bv1 1) (_ bv0 1)) ; Carry flag
#          -> #59 = (ite (= ((_ extract 63 63) (bvand (bvxor ((_ extract 63 0) #54) (bvnot ((_ extract 63 0) #52))) (bvxor ((_ extract 63 0) #54) #56))) (_ bv1 1)) (_ bv1 1) (_ bv0 1)) ; Overflow flag
#          -> #60 = (ite (= (parity_flag ((_ extract 7 0) #56)) (_ bv0 1)) (_ bv1 1) (_ bv0 1)) ; Parity flag
#          -> #61 = (ite (= ((_ extract 63 63) #56) (_ bv1 1)) (_ bv1 1) (_ bv0 1)) ; Sign flag
#          -> #62 = (ite (= #56 (_ bv0 64)) (_ bv1 1) (_ bv0 1)) ; Zero flag
#          -> #63 = (_ bv4195752 64) ; RIP
# 
# 0x4005a8: movzx eax, byte ptr [rax]
#          -> #64 = ((_ zero_extend 24) (_ bv49 8)) 
#          -> #65 = (_ bv4195755 64) ; RIP
# 
# 0x4005ab: movsx eax, al
#          -> #66 = ((_ sign_extend 24) ((_ extract 7 0) #64)) 
#          -> #67 = (_ bv4195758 64) ; RIP
# 
# 0x4005ae: cmp ecx, eax
#          -> #68 = (bvsub ((_ extract 31 0) #50) ((_ extract 31 0) #66)) 
#          -> #69 = (ite (= (_ bv16 32) (bvand (_ bv16 32) (bvxor #68 (bvxor ((_ extract 31 0) #50) ((_ extract 31 0) #66))))) (_ bv1 1) (_ bv0 1)) ; Adjust flag
#          -> #70 = (ite (bvult ((_ extract 31 0) #50) ((_ extract 31 0) #66)) (_ bv1 1) (_ bv0 1)) ; Carry flag
#          -> #71 = (ite (= ((_ extract 31 31) (bvand (bvxor ((_ extract 31 0) #50) ((_ extract 31 0) #66)) (bvxor ((_ extract 31 0) #50) #68))) (_ bv1 1)) (_ bv1 1) (_ bv0 1)) ; Overflow flag
#          -> #72 = (ite (= (parity_flag ((_ extract 7 0) #68)) (_ bv0 1)) (_ bv1 1) (_ bv0 1)) ; Parity flag
#          -> #73 = (ite (= ((_ extract 31 31) #68) (_ bv1 1)) (_ bv1 1) (_ bv0 1)) ; Sign flag
#          -> #74 = (ite (= #68 (_ bv0 32)) (_ bv1 1) (_ bv0 1)) ; Zero flag
#          -> #75 = (_ bv4195760 64) ; RIP
# 
# 0x4005b0: jz 0x4005b9
# 
# 0x4005b2: mov eax, 0x1
#          -> #76 = (_ bv1 32) 
#          -> #77 = (_ bv4195767 64) ; RIP
# 
# 0x4005b7: jmp 0x4005c8
# 
# 0x4005c8: pop rbp
#          -> #78 = #1 
#          -> #79 = (bvadd #0 (_ bv8 64)) 
#          -> #80 = (_ bv4195785 64) ; RIP
# 
# loose
# $

from triton import *


# A callback must be a function with one argument. This argument is
# always the Instruction class and contains all information
def my_callback_after(instruction):

    print '%#x: %s' %(instruction.address, instruction.assembly)

    for se in instruction.symbolicElements:
        print '\t -> %s %s' %(se.expression, (('; ' + se.comment) if se.comment is not None else ''))

    print


if __name__ == '__main__':

    # Start the symbolic analysis from the 'check' function
    startAnalysisFromSymbol('main')

    # Add a callback.
    # BEFORE: Add the callback before the instruction processing
    # AFTER:  Add the callback after the instruction processing
    # FINI:   Add the callback at the end of the execution
    addCallback(my_callback_after, IDREF.CALLBACK.AFTER)

    # Run the instrumentation - Never returns
    runProgram()

