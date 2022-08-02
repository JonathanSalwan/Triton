#!/usr/bin/env python
## -*- coding: utf-8 -*-

import lief
import sys

binary = lief.parse(sys.argv[1])

print('std::map<std::string, triton::uint64> symbols = {')
for f in binary.exported_functions:
    print('  {"%s", 0x%x},' %(f.name, f.address))
print('};')
