
#ifndef   __DSE_H__
#define   __DSE_H__

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

#define LOCKED        1
#define UNLOCKED      !LOCKED
#define TAINTED       1

#define ID_RAX        0
#define ID_RBX        1
#define ID_RCX        2
#define ID_RDX        3
#define ID_RDI        4
#define ID_RSI        5
#define ID_RBP        6
#define ID_RSP        7
#define ID_R8         8
#define ID_R9         9
#define ID_R10        10
#define ID_R11        11
#define ID_R12        12
#define ID_R13        13
#define ID_R14        14
#define ID_R15        15
#define ID_CF         16
#define ID_PF         17
#define ID_AF         18
#define ID_ZF         19
#define ID_SF         20
#define ID_TF         21
#define ID_IF         22
#define ID_DF         23
#define ID_OF         24

/* Symbolic element */
class symbolicElement {

  public:
    std::stringstream   *symSrc;
    std::stringstream   *symDst;
    std::stringstream   *symExpr;
    UINT32              isTainted;
    UINT64              uniqueID;

    symbolicElement(std::stringstream &dst, std::stringstream &src, UINT64 uniqueID);
    ~symbolicElement();

};

/* Extern decl */
extern UINT32                                   _analysisStatus;
extern UINT64                                   symbolicReg[];
extern UINT64                                   taintedReg[];
extern UINT64                                   uniqueID;
extern boost::format                            outputInstruction;
extern std::list< std::pair<UINT64, UINT64> >   memoryReference;
extern std::list< std::pair<UINT64, UINT8> >    memorySnapshot;
extern std::list<UINT64>                        addressesTainted;
extern std::list<symbolicElement *>             symbolicList;
extern KNOB<std::string>                        KnobStartAnalysis;


/* decl */
INT32   isMemoryReference(UINT64 addr);
REG     getHighReg(REG reg);
UINT32  isMemoryTainted(UINT64 addr);
UINT64  translatePinRegToID(REG reg);
VOID    Image(IMG img, VOID *v);
VOID    Instruction(INS ins, VOID *v);
VOID    addRegImm(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 imm);
VOID    addRegReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, REG reg2);
VOID    cmpMemImm(std::string insDis, ADDRINT insAddr, UINT64 imm, UINT64 mem, UINT32 readSize);
VOID    cmpRegImm(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 imm);
VOID    cmpRegReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, REG reg2);
VOID    lockAnalysis(void);
VOID    movMemImm(std::string insDis, ADDRINT insAddr, UINT64 imm, UINT64 mem, UINT32 writeSize, INT32 opcode);
VOID    movMemReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 mem, UINT32 writeSize, INT32 opcode);
VOID    movRegImm(std::string insDis, ADDRINT insAddr, REG reg1, UINT64 imm, INT32 opcode);
VOID    movRegMem(std::string insDis, ADDRINT insAddr, REG reg1, UINT64 mem, UINT32 readSize, INT32 opcode);
VOID    movRegReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, REG reg2, INT32 opcode);
VOID    notImplemented(std::string insDis, ADDRINT insAddr);
VOID    popReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 mem, UINT32 readSize);
VOID    pushImm(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, UINT64 imm, UINT64 mem, UINT32 writeSize);
VOID    pushReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 mem, UINT32 writeSize);
VOID    taintParams(CONTEXT *ctx);
VOID    unlockAnalysis(void);

#endif     /* !__DSE_H__ */

