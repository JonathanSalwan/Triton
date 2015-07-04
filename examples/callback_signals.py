
from triton import *

# Output
#
#  $ ./triton ./examples/callback_signals.py ./samples/others/signals
#  Signal 11 received on thread 0.
#  ========================== DUMP ==========================
#  rax:    0x00000000000000                        #98 = ((_ zero_extend 32) (_ bv234 32))
#  rbx:    0x00000000000000                        UNSET
#  rcx:    0x00000000001ba4                        #83 = ((_ zero_extend 32) ((_ extract 31 0) #81))
#  rdx:    0x0000000000000b                        #92 = ((_ sign_extend 32) ((_ extract 31 0) #34))
#  rdi:    0x00000000001ba4                        #96 = ((_ sign_extend 32) ((_ extract 31 0) #83))
#  rsi:    0x00000000001ba4                        #94 = ((_ sign_extend 32) ((_ extract 31 0) #90))
#  rbp:    0x007fff097e3540                        #10 = ((_ extract 63 0) #0)
#  rsp:    0x007fff097e3528                        #58 = (bvsub ((_ extract 63 0) #47) (_ bv8 64))
#  rip:    0x007f3fa0735ea7                        #99 = (_ bv139911251582629 64)
#  r8:     0x007f3fa0a94c80                        UNSET
#  r9:     0x007f3fb671b120                        UNSET
#  r10:    0x00000000000000                        UNSET
#  r11:    0x007f3fa0735e70                        UNSET
#  r12:    0x00000000400460                        UNSET
#  r13:    0x007fff097e3620                        UNSET
#  r14:    0x00000000000000                        UNSET
#  r15:    0x00000000000000                        UNSET
#  xmm0:   0x000000ff000000                        UNSET
#  xmm1:   0x2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f      UNSET
#  xmm2:   0x00000000000000                        UNSET
#  xmm3:   0x00ff000000ff00                        UNSET
#  xmm4:   0x000000000000ff                        UNSET
#  xmm5:   0x00000000000000                        UNSET
#  xmm6:   0x00000000000000                        UNSET
#  xmm7:   0x00000000000000                        UNSET
#  xmm8:   0x00000000000000                        UNSET
#  xmm9:   0x00000000000000                        UNSET
#  xmm10:  0x00000000000000                        UNSET
#  xmm11:  0x00000000000000                        UNSET
#  xmm12:  0x00000000000000                        UNSET
#  xmm13:  0x00000000000000                        UNSET
#  xmm14:  0x00000000000000                        UNSET
#  xmm15:  0x00000000000000                        UNSET
#  af:     0x00000000000000                        #13 = (ite (= (_ bv16 64) (bvand (_ bv16 64) (bvxor #12 (bvxor ((_ extract 63 0) #0) (_ bv16 64))))) (_ bv1 1) (_ bv0 1))
#  cf:     0x00000000000000                        #74 = (_ bv0 1)
#  df:     0x00000000000000                        UNSET
#  if:     0x00000000000001                        UNSET
#  of:     0x00000000000000                        #75 = (_ bv0 1)
#  pd:     0x00000000000001                        #76 = (ite (= (parity_flag ((_ extract 7 0) #73)) (_ bv0 1)) (_ bv1 1) (_ bv0 1))
#  sf:     0x00000000000000                        #77 = (ite (= ((_ extract 31 31) #73) (_ bv1 1)) (_ bv1 1) (_ bv0 1))
#  tf:     0x00000000000000                        UNSET
#  zf:     0x00000000000001                        #78 = (ite (= #73 (_ bv0 32)) (_ bv1 1) (_ bv0 1))



def signals(threadId, sig):
    print 'Signal %d received on thread %d.' %(sig, threadId)
    print '========================== DUMP =========================='
    regs = getRegs()
    for reg, data in regs.items():
        value = data['concreteValue']
        seid  = data['symbolicExpr']
        print '%s:\t%#016x\t%s' %(getRegName(reg), value, (getSymExpr(seid).expression if seid != IDREF.MISC.UNSET else 'UNSET'))
    return


if __name__ == '__main__':

    # Start the symbolic analysis from the 'main' function
    startAnalysisFromSymbol('main')

    # Add a callback.
    addCallback(signals, IDREF.CALLBACK.SIGNALS)

    # Run the instrumentation - Never returns
    runProgram()

