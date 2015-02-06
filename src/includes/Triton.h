
#ifndef   __TRITON_H__
#define   __TRITON_H__

#include <asm/unistd.h>
#include <cstring>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <list>
#include <sstream>
#include <boost/format.hpp>

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

#include <z3++.h>

#include "Registers.h"
#include "Signals.h"
#include "SnapshotEngine.h"
#include "SolverEngine.h"
#include "SymbolicEngine.h"
#include "TaintEngine.h"
#include "Trace.h"
#include "Tritinst.h"
#include "Utils.h"

#define LIB_MAPING_MEMORY 0x7f0000000000



/* Extern decl */

extern KNOB<std::string>        KnobStartAnalysis;
extern KNOB<bool>               KnobDetectFormatString;
extern Trace                    *trace;
extern UINT32                   _analysisStatus;
extern boost::format            outputInstruction;


/* decl */
VOID            Image(IMG img, VOID *v);
VOID            Instruction(INS ins, VOID *v);
VOID            addRegImm(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 imm);
VOID            addRegReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, REG reg2);
VOID            branchs(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, UINT32 opcode);
VOID            cmpMemImm(std::string insDis, ADDRINT insAddr, UINT64 imm, UINT64 mem, UINT32 readSize);
VOID            cmpRegImm(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 imm);
VOID            cmpRegReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, REG reg2);
VOID            movMemImm(std::string insDis, ADDRINT insAddr, UINT64 imm, UINT64 mem, UINT32 writeSize, INT32 opcode);
VOID            movMemReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 mem, UINT32 writeSize, INT32 opcode);
VOID            movRegImm(std::string insDis, ADDRINT insAddr, REG reg1, UINT64 imm, INT32 opcode);
VOID            movRegMem(std::string insDis, ADDRINT insAddr, REG reg1, UINT64 mem, UINT32 readSize, INT32 opcode);
VOID            movRegReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, REG reg2, INT32 opcode);
VOID            notImplemented(std::string insDis, ADDRINT insAddr);
VOID            popReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 mem, UINT32 readSize);
VOID            pushImm(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, UINT64 imm, UINT64 mem, UINT32 writeSize);
VOID            pushReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 mem, UINT32 writeSize);

#endif     /* !__TRITON_H__ */

