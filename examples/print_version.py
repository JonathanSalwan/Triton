
import sys
from triton import *

if __name__ == '__main__':
    print "Triton v%d.%d (build %d)" %(IDREF.VERSION.MAJOR, IDREF.VERSION.MINOR, IDREF.VERSION.BUILD)
    sys.exit(0)

