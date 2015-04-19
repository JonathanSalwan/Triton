
import triton


def fini():
    triton.saveTrace('trace.log')


if __name__ == '__main__':

    # Start the symbolic analysis from the 'check' function
    triton.startAnalysisFromSymbol('check')

    # When the instruction is over, call the fini function
    triton.addCallback(fini, triton.CB_FINI)
    
    # Run the instrumentation - Never returns
    triton.runProgram()

