
import triton


if __name__ == '__main__':

    # Start the symbolic analysis from the 0x40056d to 0x4005c9
    triton.startAnalysisFromAddr(0x40056d)
    triton.stopAnalysisFromAddr(0x4005c9)

    # Run the instrumentation - Never returns
    triton.runProgram()

