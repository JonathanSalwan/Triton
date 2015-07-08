
import triton


if __name__ == '__main__':

    # Start the symbolic analysis from the 'check' function
    triton.startAnalysisFromSymbol('check')

    # Run the instrumentation - Never returns
    triton.runProgram()

