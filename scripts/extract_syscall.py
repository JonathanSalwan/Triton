#! /usr/bin/env python

from __future__ import print_function

import argparse
import sys
import re

PREAMBULE = """
#include <python2.7/Python.h>

#include "PythonBindings.h"
#include "Registers.h"
#include "asm/unistd_64.h"


void initLinux64Env(PyObject *idLinux64ClassDict)
{\
"""

SMT = '  PyDict_SetItemString(idLinux64ClassDict, "%s", PyInt_FromLong(%s));'

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("file",
                        help="this file must contains the syscalls definitions",
                        type=str)
    args = parser.parse_args()

    regex = re.compile(r"(__NR_\w+)")

    print(PREAMBULE)

    with open(args.file) as hfile:
        for match in regex.finditer(hfile.read()):
            name = match.groups()[0]
            print(SMT % (name[5:].upper(), name))

    print("}")
