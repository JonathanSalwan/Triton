
import triton

if __name__ == '__main__':

    # Start the symbolic analysis from the 'check' function
    triton.startAnalysisFromName('check')

    # Dump the symbolic trace at the end of the execution
    triton.dumpTrace(True)

    # Dump some statistics at the end of the execution
    triton.dumpStats(True)

    # Run the instrumentation - Never returns
    triton.runProgram()

