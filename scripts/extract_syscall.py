#! /usr/bin/env python
#
# This script is used to generate the file src/utils/syscalls.cpp.
# As the list of syscalls depends of your Kernel version. We must
# generate the list at the compile time.
#

from __future__ import print_function

import argparse
import sys
import re

PREAMBULE = """
#include <Syscalls.h>
"""

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("file",
                        help="this file must contains the syscalls definitions",
                        type=str)
    args = parser.parse_args()

    regex = re.compile(r"#define\s+(__NR_\w+)\s+\d+")

    with open(args.file) as hfile:
        print(PREAMBULE)
        print("const char *syscallmap[] = {")

        counter = 0
        for match in regex.finditer(hfile.read()):
            name = match.groups()[0]
            print('  "%s", // %s' % (name[5:].upper(), name))
            counter += 1

    print("};")
    print()
    print("const unsigned int NB_SYSCALL = %d;" % counter)
