
import triton

if __name__ == '__main__':
    triton.startAnalysis('check')
    triton.dumpTrace(True)
    triton.dumpStats(True)
    triton.runProgram()

