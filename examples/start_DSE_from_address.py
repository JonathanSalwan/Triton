
import triton


def fini():
    triton.saveTrace('trace.log')


if __name__ == '__main__':

    # Start the symbolic analysis from the 0x40056d to 0x4005c9
    triton.startAnalysisFromAddr(0x40056d)
    triton.stopAnalysisFromAddr(0x4005c9)

    # When the instruction is over, call the fini function
    triton.addCallback(fini, triton.CB_FINI)

    # Run the instrumentation - Never returns
    triton.runProgram()

