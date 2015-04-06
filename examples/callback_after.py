
# Output
#
# 0x40056d: push rbp
#          ->  #0 = (bvsub (_ bv140734006985528 64) (_ bv8 64))
#          ->  #1 = (_ bv140734006985568 64)
#
# 0x40056e: mov rbp, rsp
#          ->  #2 = ((_ extract 63 0) #0)
#
# 0x400571: mov qword ptr [rbp-0x18], rdi
#          ->  #3 = (_ bv140734006989031 64)
#
# 0x400575: mov dword ptr [rbp-0x4], 0x0
#          ->  #4 = (_ bv0 32)
#
# 0x40057c: jmp 0x4005bd
#
# 0x4005bd: cmp dword ptr [rbp-0x4], 0x4
#          ->  #5 = (bvsub #4 ((_ sign_extend 0) (_ bv4 32)))
#          ->  #6 = (assert (= (_ bv16 32) (bvand (_ bv16 32) (bvxor #5 (bvxor #4 ((_ sign_extend 0) (_ bv4 32)))))))
#          ->  #7 = (assert (bvult #5 #4))
#          ->  #8 = (assert (= ((_ extract 31 31) (bvand (bvxor #4 (bvnot ((_ sign_extend 0) (_ bv4 32)))) (bvxor #4 #5))) (_ bv1 1)))
#          ->  #9 = (assert (= (parity_flag ((_ extract 7 0) #5)) (_ bv0 1)))
#          ->  #10 = (assert (= ((_ extract 31 31) #5) (_ bv1 1)))
#          ->  #11 = (assert (= #5 (_ bv0 32)))
#
# 0x4005c1: jle 0x40057e
#
# 0x40057e: mov eax, dword ptr [rbp-0x4]
#          ->  #12 = ((_ extract 31 0) #5)
#
# 0x400581: movsxd rdx, eax
#          ->  #13 = ((_ sign_extend 32) ((_ extract 31 0) #12))
#
# 0x400584: mov rax, qword ptr [rbp-0x18]
#          ->  #14 = ((_ extract 63 0) #3)
#
# 0x400588: add rax, rdx
#          ->  #15 = (bvadd #14 ((_ extract 63 0) #13))
#          ->  #16 = (assert (= (_ bv16 64) (bvand (_ bv16 64) (bvxor #15 (bvxor #14 ((_ extract 63 0) #13))))))
#          ->  #17 = (assert (bvult #15 #14))
#          ->  #18 = (assert (= ((_ extract 63 63) (bvand (bvxor #14 (bvnot ((_ extract 63 0) #13))) (bvxor #14 #15))) (_ bv1 1)))
#          ->  #19 = (assert (= (parity_flag ((_ extract 7 0) #15)) (_ bv0 1)))
#          ->  #20 = (assert (= ((_ extract 63 63) #15) (_ bv1 1)))
#          ->  #21 = (assert (= #15 (_ bv0 64)))
#
# 0x40058b: movzx eax, byte ptr [rax]
#          ->  #22 = ((_ zero_extend 24) (_ bv97 8))
#
# 0x40058e: movsx eax, al
#          ->  #23 = ((_ sign_extend 24) ((_ extract 7 0) #22))
#
# 0x400591: sub eax, 0x1
#          ->  #24 = (bvsub #23 (_ bv1 32))
#          ->  #25 = (assert (= (_ bv16 32) (bvand (_ bv16 32) (bvxor #24 (bvxor #23 (_ bv1 32))))))
#          ->  #26 = (assert (bvult #24 #23))
#          ->  #27 = (assert (= ((_ extract 31 31) (bvand (bvxor #23 (bvnot (_ bv1 32))) (bvxor #23 #24))) (_ bv1 1)))
#          ->  #28 = (assert (= (parity_flag ((_ extract 7 0) #24)) (_ bv0 1)))
#          ->  #29 = (assert (= ((_ extract 31 31) #24) (_ bv1 1)))
#          ->  #30 = (assert (= #24 (_ bv0 32)))
# 
# 0x400594: xor eax, 0x55
#          ->  #31 = (bvxor #24 (_ bv85 32))
#          ->  #32 = (assert (= (_ bv16 32) (bvand (_ bv16 32) (bvxor #31 (bvxor #24 (_ bv85 32))))))
#          ->  #33 = (assert (bvult #31 #24))
#          ->  #34 = (assert (= ((_ extract 31 31) (bvand (bvxor #24 (bvnot (_ bv85 32))) (bvxor #24 #31))) (_ bv1 1)))
#          ->  #35 = (assert (= (parity_flag ((_ extract 7 0) #31)) (_ bv0 1)))
#          ->  #36 = (assert (= ((_ extract 31 31) #31) (_ bv1 1)))
#          ->  #37 = (assert (= #31 (_ bv0 32)))
# 
# 0x400597: mov ecx, eax
#          ->  #38 = ((_ extract 31 0) #31)
# 
# 0x400599: mov rdx, qword ptr [rip+0x200aa0]
#          ->  #39 = (_ bv4196036 64)
# 
# 0x4005a0: mov eax, dword ptr [rbp-0x4]
#          ->  #40 = ((_ extract 31 0) #5)
# 
# 0x4005a3: cdqe 
# 
# 0x4005a5: add rax, rdx
#          ->  #41 = (bvadd #40 ((_ extract 63 0) #39))
#          ->  #42 = (assert (= (_ bv16 64) (bvand (_ bv16 64) (bvxor #41 (bvxor #40 ((_ extract 63 0) #39))))))
#          ->  #43 = (assert (bvult #41 #40))
#          ->  #44 = (assert (= ((_ extract 63 63) (bvand (bvxor #40 (bvnot ((_ extract 63 0) #39))) (bvxor #40 #41))) (_ bv1 1)))
#          ->  #45 = (assert (= (parity_flag ((_ extract 7 0) #41)) (_ bv0 1)))
#          ->  #46 = (assert (= ((_ extract 63 63) #41) (_ bv1 1)))
#          ->  #47 = (assert (= #41 (_ bv0 64)))
# 
# 0x4005a8: movzx eax, byte ptr [rax]
#          ->  #48 = ((_ zero_extend 24) (_ bv49 8))
# 
# 0x4005ab: movsx eax, al
#          ->  #49 = ((_ sign_extend 24) ((_ extract 7 0) #48))
# 
# 0x4005ae: cmp ecx, eax
#          ->  #50 = (bvsub #38 ((_ extract 31 0) #49))
#          ->  #51 = (assert (= (_ bv16 32) (bvand (_ bv16 32) (bvxor #50 (bvxor #38 ((_ extract 31 0) #49))))))
#          ->  #52 = (assert (bvult #50 #38))
#          ->  #53 = (assert (= ((_ extract 31 31) (bvand (bvxor #38 (bvnot ((_ extract 31 0) #49))) (bvxor #38 #50))) (_ bv1 1)))
#          ->  #54 = (assert (= (parity_flag ((_ extract 7 0) #50)) (_ bv0 1)))
#          ->  #55 = (assert (= ((_ extract 31 31) #50) (_ bv1 1)))
#          ->  #56 = (assert (= #50 (_ bv0 32)))
# 
# 0x4005b0: jz 0x4005b9
# 
# 0x4005b2: mov eax, 0x1
#          ->  #57 = (_ bv1 32)
# 
# 0x4005b7: jmp 0x4005c8
# 
# 0x4005c8: pop rbp
#          ->  #58 = #1
#          ->  #59 = (bvadd #0 (_ bv8 64))


from triton import *


# A callback must be a function with one argument. This argument is
# always the Instruction class and contains all information
def my_callback_after(instruction):

    print '%#x: %s' %(instruction.address, instruction.assembly)

    for se in instruction.symbolicElements:
        print '\t -> ', se.expression

    print


if __name__ == '__main__':

    # Start the symbolic analysis from the 'check' function
    startAnalysisFromSymbol('main')

    # Add a callback.
    # CB_BEFORE: Add the callback before the instruction processing
    # CB_AFTER: Add the callback after the instruction processing
    addCallback(my_callback_after, CB_AFTER)

    # Run the instrumentation - Never returns
    runProgram()

