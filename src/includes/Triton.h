
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

#include "SnapshotEngine.h"
#include "SolverEngine.h"
#include "SymbolicEngine.h"
#include "TaintEngine.h"
#include "registers.h"
#include "utils.h"


/* Extern decl */

extern SnapshotEngine           *snapshotEngine;
extern TaintEngine              *taintEngine;
extern SymbolicEngine           *symbolicEngine;
extern UINT32                   _analysisStatus;
extern KNOB<std::string>        KnobStartAnalysis;
extern boost::format            outputInstruction;


/* decl */
VOID            Instruction(INS ins, VOID *v);
VOID            Image(IMG img, VOID *v);
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


VOID displayTrace(ADDRINT addr, const std::string &insDis, const std::string &expr, UINT64 isTainted);

#endif     /* !__TRITON_H__ */

