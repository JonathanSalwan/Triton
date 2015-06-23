
# Output
#
# $ ../../../pin -t ./triton.so -script ./examples/callback_after.py -- ./samples/crackmes/crackme_xor a
# 0x40056d: push rbp
#          -> #0 = (bvsub (_ bv140735022953896 64) (_ bv8 64)) ; Aligns stack
#          -> #1 = (_ bv140735022953936 64) 
#          -> #2 = (_ bv4195694 64) ; RIP
#
# 0x40056e: mov rbp, rsp
#          -> #3 = ((_ extract 63 0) #0) 
#          -> #4 = (_ bv4195697 64) ; RIP
#
# 0x400571: mov qword ptr [rbp-0x18], rdi
#          -> #5 = (_ bv140735022960969 64) 
#          -> #6 = (_ bv4195701 64) ; RIP
#
# 0x400575: mov dword ptr [rbp-0x4], 0x0
#          -> #7 = (_ bv0 32) 
#          -> #8 = (_ bv4195708 64) ; RIP
#
# 0x40057c: jmp 0x4005bd
#          -> #9 = (_ bv4195773 64) ; RIP
#
# 0x4005bd: cmp dword ptr [rbp-0x4], 0x4
#          -> #10 = (bvsub #7 ((_ sign_extend 0) (_ bv4 32))) 
#          -> #11 = (ite (= (_ bv16 32) (bvand (_ bv16 32) (bvxor #10 (bvxor #7 ((_ sign_extend 0) (_ bv4 32)))))) (_ bv1 1) (_ bv0 1)) ; Adjust flag
#          -> #12 = (ite (bvult #7 ((_ sign_extend 0) (_ bv4 32))) (_ bv1 1) (_ bv0 1)) ; Carry flag
#          -> #13 = (ite (= ((_ extract 31 31) (bvand (bvxor #7 ((_ sign_extend 0) (_ bv4 32))) (bvxor #7 #10))) (_ bv1 1)) (_ bv1 1) (_ bv0 1)) ; Overflow flag
#          -> #14 = (ite (= (parity_flag ((_ extract 7 0) #10)) (_ bv0 1)) (_ bv1 1) (_ bv0 1)) ; Parity flag
#          -> #15 = (ite (= ((_ extract 31 31) #10) (_ bv1 1)) (_ bv1 1) (_ bv0 1)) ; Sign flag
#          -> #16 = (ite (= #10 (_ bv0 32)) (_ bv1 1) (_ bv0 1)) ; Zero flag
#          -> #17 = (_ bv4195777 64) ; RIP
#
# 0x40057e: mov eax, dword ptr [rbp-0x4]
#          -> #19 = ((_ extract 31 0) #10) 
#          -> #20 = (_ bv4195713 64) ; RIP
#
# 0x400581: movsxd rdx, eax
#          -> #21 = ((_ sign_extend 32) ((_ extract 31 0) #19)) 
#          -> #22 = (_ bv4195716 64) ; RIP
#
# 0x400584: mov rax, qword ptr [rbp-0x18]
#          -> #23 = ((_ extract 63 0) #5) 
#          -> #24 = (_ bv4195720 64) ; RIP
#
# 0x400588: add rax, rdx
#          -> #25 = (bvadd ((_ extract 63 0) #23) ((_ extract 63 0) #21)) 
#          -> #26 = (ite (= (_ bv16 64) (bvand (_ bv16 64) (bvxor #25 (bvxor ((_ extract 63 0) #23) ((_ extract 63 0) #21))))) (_ bv1 1) (_ bv0 1)) ; Adjust flag
#          -> #27 = (ite (bvult #25 ((_ extract 63 0) #23)) (_ bv1 1) (_ bv0 1)) ; Carry flag
#          -> #28 = (ite (= ((_ extract 63 63) (bvand (bvxor ((_ extract 63 0) #23) (bvnot ((_ extract 63 0) #21))) (bvxor ((_ extract 63 0) #23) #25))) (_ bv1 1)) (_ bv1 1) (_ bv0 1)) ; Overflow flag
#          -> #29 = (ite (= (parity_flag ((_ extract 7 0) #25)) (_ bv0 1)) (_ bv1 1) (_ bv0 1)) ; Parity flag
#          -> #30 = (ite (= ((_ extract 63 63) #25) (_ bv1 1)) (_ bv1 1) (_ bv0 1)) ; Sign flag
#          -> #31 = (ite (= #25 (_ bv0 64)) (_ bv1 1) (_ bv0 1)) ; Zero flag
#          -> #32 = (_ bv4195723 64) ; RIP
#
# 0x40058b: movzx eax, byte ptr [rax]
#          -> #33 = ((_ zero_extend 24) (_ bv97 8)) 
#          -> #34 = (_ bv4195726 64) ; RIP
#
# 0x40058e: movsx eax, al
#          -> #35 = ((_ sign_extend 24) ((_ extract 7 0) #33)) 
#          -> #36 = (_ bv4195729 64) ; RIP
#
# 0x400591: sub eax, 0x1
#          -> #37 = (bvsub ((_ extract 31 0) #35) (_ bv1 32)) 
#          -> #38 = (ite (= (_ bv16 32) (bvand (_ bv16 32) (bvxor #37 (bvxor ((_ extract 31 0) #35) (_ bv1 32))))) (_ bv1 1) (_ bv0 1)) ; Adjust flag
#          -> #39 = (ite (bvult ((_ extract 31 0) #35) (_ bv1 32)) (_ bv1 1) (_ bv0 1)) ; Carry flag
#          -> #40 = (ite (= ((_ extract 31 31) (bvand (bvxor ((_ extract 31 0) #35) (_ bv1 32)) (bvxor ((_ extract 31 0) #35) #37))) (_ bv1 1)) (_ bv1 1) (_ bv0 1)) ; Overflow flag
#          -> #41 = (ite (= (parity_flag ((_ extract 7 0) #37)) (_ bv0 1)) (_ bv1 1) (_ bv0 1)) ; Parity flag
#          -> #42 = (ite (= ((_ extract 31 31) #37) (_ bv1 1)) (_ bv1 1) (_ bv0 1)) ; Sign flag
#          -> #43 = (ite (= #37 (_ bv0 32)) (_ bv1 1) (_ bv0 1)) ; Zero flag
#          -> #44 = (_ bv4195732 64) ; RIP
#
# 0x400594: xor eax, 0x55
#          -> #45 = (bvxor ((_ extract 31 0) #37) (_ bv85 32)) 
#          -> #46 = (_ bv0 1) ; Clears carry flag
#          -> #47 = (_ bv0 1) ; Clears overflow flag
#          -> #48 = (ite (= (parity_flag ((_ extract 7 0) #45)) (_ bv0 1)) (_ bv1 1) (_ bv0 1)) ; Parity flag
#          -> #49 = (ite (= ((_ extract 31 31) #45) (_ bv1 1)) (_ bv1 1) (_ bv0 1)) ; Sign flag
#          -> #50 = (ite (= #45 (_ bv0 32)) (_ bv1 1) (_ bv0 1)) ; Zero flag
#          -> #51 = (_ bv4195735 64) ; RIP
# 
# 0x400597: mov ecx, eax
#          -> #52 = ((_ extract 31 0) #45) 
#          -> #53 = (_ bv4195737 64) ; RIP
# 
# 0x400599: mov rdx, qword ptr [rip+0x200aa0]
#          -> #54 = (_ bv4196036 64) 
#          -> #55 = (_ bv4195744 64) ; RIP
# 
# 0x4005a0: mov eax, dword ptr [rbp-0x4]
#          -> #56 = ((_ extract 31 0) #10) 
#          -> #57 = (_ bv4195747 64) ; RIP
# 
# 0x4005a3: cdqe 
#          -> #58 = ((_ sign_extend 32) ((_ extract 31 0) #56)) 
#          -> #59 = (_ bv4195749 64) ; RIP
# 
# 0x4005a5: add rax, rdx
#          -> #60 = (bvadd ((_ extract 63 0) #58) ((_ extract 63 0) #54)) 
#          -> #61 = (ite (= (_ bv16 64) (bvand (_ bv16 64) (bvxor #60 (bvxor ((_ extract 63 0) #58) ((_ extract 63 0) #54))))) (_ bv1 1) (_ bv0 1)) ; Adjust flag
#          -> #62 = (ite (bvult #60 ((_ extract 63 0) #58)) (_ bv1 1) (_ bv0 1)) ; Carry flag
#          -> #63 = (ite (= ((_ extract 63 63) (bvand (bvxor ((_ extract 63 0) #58) (bvnot ((_ extract 63 0) #54))) (bvxor ((_ extract 63 0) #58) #60))) (_ bv1 1)) (_ bv1 1) (_ bv0 1)) ; Overflow flag
#          -> #64 = (ite (= (parity_flag ((_ extract 7 0) #60)) (_ bv0 1)) (_ bv1 1) (_ bv0 1)) ; Parity flag
#          -> #65 = (ite (= ((_ extract 63 63) #60) (_ bv1 1)) (_ bv1 1) (_ bv0 1)) ; Sign flag
#          -> #66 = (ite (= #60 (_ bv0 64)) (_ bv1 1) (_ bv0 1)) ; Zero flag
#          -> #67 = (_ bv4195752 64) ; RIP
# 
# 0x4005a8: movzx eax, byte ptr [rax]
#          -> #68 = ((_ zero_extend 24) (_ bv49 8)) 
#          -> #69 = (_ bv4195755 64) ; RIP
# 
# 0x4005ab: movsx eax, al
#          -> #70 = ((_ sign_extend 24) ((_ extract 7 0) #68)) 
#          -> #71 = (_ bv4195758 64) ; RIP
# 
# 0x4005ae: cmp ecx, eax
#          -> #72 = (bvsub ((_ extract 31 0) #52) ((_ extract 31 0) #70)) 
#          -> #73 = (ite (= (_ bv16 32) (bvand (_ bv16 32) (bvxor #72 (bvxor ((_ extract 31 0) #52) ((_ extract 31 0) #70))))) (_ bv1 1) (_ bv0 1)) ; Adjust flag
#          -> #74 = (ite (bvult ((_ extract 31 0) #52) ((_ extract 31 0) #70)) (_ bv1 1) (_ bv0 1)) ; Carry flag
#          -> #75 = (ite (= ((_ extract 31 31) (bvand (bvxor ((_ extract 31 0) #52) ((_ extract 31 0) #70)) (bvxor ((_ extract 31 0) #52) #72))) (_ bv1 1)) (_ bv1 1) (_ bv0 1)) ; Overflow flag
#          -> #76 = (ite (= (parity_flag ((_ extract 7 0) #72)) (_ bv0 1)) (_ bv1 1) (_ bv0 1)) ; Parity flag
#          -> #77 = (ite (= ((_ extract 31 31) #72) (_ bv1 1)) (_ bv1 1) (_ bv0 1)) ; Sign flag
#          -> #78 = (ite (= #72 (_ bv0 32)) (_ bv1 1) (_ bv0 1)) ; Zero flag
#          -> #79 = (_ bv4195760 64) ; RIP
# 
# 0x4005b0: jz 0x4005b9
#          -> #80 = (ite (= #78 (_ bv1 1)) (_ bv4195769 64) (_ bv4195762 64)) ; RIP
# 
# 0x4005b2: mov eax, 0x1
#          -> #81 = (_ bv1 32) 
#          -> #82 = (_ bv4195767 64) ; RIP
# 
# 0x4005b7: jmp 0x4005c8
#          -> #83 = (_ bv4195784 64) ; RIP
# 
# 0x4005c8: pop rbp
#          -> #84 = #1 
#          -> #85 = (bvadd #0 (_ bv8 64)) ; Aligns stack
#          -> #86 = (_ bv4195785 64) ; RIP
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
    startAnalysisFromSymbol('check')

    # Add a callback.
    # BEFORE: Add the callback before the instruction processing
    # AFTER:  Add the callback after the instruction processing
    # FINI:   Add the callback at the end of the execution
    addCallback(my_callback_after, IDREF.CALLBACK.AFTER)

    # Run the instrumentation - Never returns
    runProgram()

