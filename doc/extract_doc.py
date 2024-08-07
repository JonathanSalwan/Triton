import os
import sys

SPEC          = sys.argv[1] # defined from the doc/CMakeLists.txt
BUILD_DIR     = sys.argv[2] # defined from the doc/CMakeLists.txt
x86_regs      = list()
aarch64_regs  = list()
arm32_regs    = list()
rv64_regs     = list()
rv32_regs     = list()

##############################################################################

if SPEC.find('x86') >= 0:
    with open(SPEC, "r") as f:
        for line in f.readlines():
            if line.startswith("REG_SPEC"):
                args = line[line.find("(") + 1: line.find(")")].split(", ")
                x86_regs.append((args[0], args[-1].find("true") >= 0))

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

##############################################################################

elif SPEC.find('aarch64') >= 0:
    with open(SPEC, "r") as f:
        for line in f.readlines():
            if line.startswith("REG_SPEC") or line.startswith("SYS_REG_SPEC"):
                args = line[line.find("(") + 1: line.find(")")].split(", ")
                aarch64_regs.append(args[0])

    with open(os.path.join(BUILD_DIR, "aarch64_reg"), "w") as out:
        out.write('<ul>\n')
        for name in aarch64_regs:
            out.write("<li><b>REG.AARCH64.{}</b></li>\n".format(name))
        out.write('</ul>\n')

##############################################################################

elif SPEC.find('arm32') >= 0:
    with open(SPEC, "r") as f:
        for line in f.readlines():
            if line.startswith("REG_SPEC"):
                args = line[line.find("(") + 1: line.find(")")].split(", ")
                arm32_regs.append(args[0])

    with open(os.path.join(BUILD_DIR, "arm32_reg"), "w") as out:
        out.write('<ul>\n')
        for name in arm32_regs:
            out.write("<li><b>REG.ARM32.{}</b></li>\n".format(name))
        out.write('</ul>\n')

##############################################################################

elif SPEC.find('riscv64') >= 0:
    with open(SPEC, "r") as f:
        for line in f.readlines():
            if line.startswith("REG_SPEC") or line.startswith("SYS_REG_SPEC"):
                args = line[line.find("(") + 1: line.find(")")].split(", ")
                rv64_regs.append(args[1])

    with open(os.path.join(BUILD_DIR, "rv64_reg"), "w") as out:
        out.write('<ul>\n')
        for name in rv64_regs:
            out.write("<li><b>REG.RISCV64.{}</b></li>\n".format(name))
        out.write('</ul>\n')

##############################################################################

elif SPEC.find('riscv32') >= 0:
    with open(SPEC, "r") as f:
        for line in f.readlines():
            if line.startswith("REG_SPEC") or line.startswith("SYS_REG_SPEC"):
                args = line[line.find("(") + 1: line.find(")")].split(", ")
                rv32_regs.append(args[1])

    with open(os.path.join(BUILD_DIR, "rv32_reg"), "w") as out:
        out.write('<ul>\n')
        for name in rv32_regs:
            out.write("<li><b>REG.RISCV32.{}</b></li>\n".format(name))
        out.write('</ul>\n')
