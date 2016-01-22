#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
## Copyright (C) - Triton
## This program is under the terms of the LGPLv3 License.
##

from   setuptools import setup
import os
import inspect
import shutil
import platform

package_name        = "triton"
version             = "0.3"
package_description = """
Triton is a dynamic binary analysis (DBA) framework. It provides internal components like a
Dynamic Symbolic Exuction (DSE) engine, a Taint Engine, an intermediate representation of
x86 and x86-64 instructions into SMT2-Lib, SMT simplification passes, a Z3 interface to solve
constraints and, the last but not least, Python bindings. Based on these components, you are
able to build program analysis tools, automate reverse engineering and perform software verification.
""".strip()

if platform.system() == 'Linux':
    shutil.copyfile('build/libtriton.so', 'build/triton.so')

elif platform.system() == 'Darwin':
    shutil.copyfile('build/libtriton.dylib', 'build/triton.so')

else:
    print '[+] Invalid platform - Send us a pull request :)'
    sys.exit(1)

setup(
    name             = package_name,
    version          = version,
    description      = package_description,
    license          = "LGPLv3",
    author           = "Jonathan Salwan",
    author_email     = "jsalwan@quarkslab.com",
    url              = "http://triton.quarkslab.com",
    data_files       = [(os.path.dirname(inspect.getfile(inspect)), ['build/triton.so'])],
    classifiers      = [
        'Development Status :: 4 - Beta',
        'Environment :: Console',
        'Intended Audience :: Developers',
        'Intended Audience :: Science/Research',
        'License :: OSI Approved :: GNU Lesser General Public License v3 (LGPLv3)',
        'Operating System :: MacOS :: MacOS X',
        'Operating System :: POSIX :: Linux',
        'Programming Language :: C++',
        'Programming Language :: Python :: 2.7',
        'Topic :: Scientific/Engineering',
        'Topic :: Security',
    ]
)

