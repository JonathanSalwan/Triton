#! /usr/bin/env python
#
# This script is used to generate the files src/utils/syscalls{32,64}.cpp.
# As the list of syscalls depends of your Kernel version. We must
# generate the list at the compile time.
#

from __future__ import print_function

import argparse
import sys
import re
import platform

HEADER = """
/*! \\file */
#if defined(__unix__) || defined(__APPLE__)
#include <triton/syscalls.hpp>



namespace triton {
  namespace os {
    namespace unix {
"""

FOOTER = """

    }; /* unix namespace */
  }; /* os namespace */
}; /* triton namespace */

#endif
"""

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("file", help="this file must contains the syscalls definitions", type=str)
    parser.add_argument("arch", help="syscall architecture - 32 or 64", type=str)
    args = parser.parse_args()

    if platform.system() == 'Linux':
        regex = re.compile(r"#define\s+(__NR_)(\w+)\s+(\d+)")
    elif platform.system() == 'Darwin':
        regex = re.compile(r"#define\s+(SYS_)(\w+)\s+(\d+)")
    else:
        sys.exit(0)

    with open(args.file) as hfile:
        print(HEADER)
        print("      const char* syscallmap%s[] = {" % args.arch)

        counter = 0
        for match in regex.finditer(hfile.read()):
            prefix = str(match.groups()[0])
            name   = str(match.groups()[1])
            sysid  = int(match.groups()[2])
            if counter != sysid:
                for i in range(sysid - counter):
                    print('        "UNDEF", // undefined')
                    counter += 1
            print('        "%s", // %s%s' % (name.upper(), prefix, name))
            counter += 1

    print("      };")
    print()
    print("      const unsigned int NB_SYSCALL%s = %d;" % (args.arch, counter))
    print(FOOTER)

