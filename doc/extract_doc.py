import os
import sys

BUILD_DIR = sys.argv[2] # defined from the doc/CMakeLists.txt
x86_regs  = list()

with open(sys.argv[1], "r") as f:
    for line in f.readlines():
        if line.startswith("REG_SPEC"):
            args = line[line.find("(") + 1: line.find(")")].split(", ")
            x86_regs.append((args[0], args[-1] == "true"))

with open(os.path.join(BUILD_DIR, "x86_reg"), "w") as out:
    out.write('<ul>\n')
    for name, valid in x86_regs:
        if valid:
            out.write("<li><b>REG.X86.{}</b></li>\n".format(name))
    out.write('</ul>\n')

with open(os.path.join(BUILD_DIR, "x8664_reg"), "w") as out:
    out.write('<ul>\n')
    for name, _ in x86_regs:
        out.write("<li><b>REG.X86_64.{}</b></li>\n".format(name))
    out.write('</ul>\n')
