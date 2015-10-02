/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_INST_H
#define TRITON_INST_H

#include <list>
#include <string>
#include <tuple>
#include <vector>

#include "IRBuilderOperand.h"
#include "TritonOperand.h"

#ifndef LIGHT_VERSION
  #include "SymbolicExpression.h"
#endif


class Inst {

  private:
    bool                                  branchTaken;
    sint32                                opcodeCategory;
    std::string                           disassembly;
    std::string                           imageName;
    std::string                           routineName;
    std::string                           sectionName;
    std::vector<TritonOperand>            operands;
    uint32                                opcode;
    uint64                                address;
    uint64                                baseAddress;
    uint64                                branchTargetAddress;
    uint64                                nextAddress;
    uint64                                offset;
    uint64                                threadId;
    #ifndef LIGHT_VERSION
    std::list<SymbolicExpression*>        symbolicExpressions;
    #endif

  public:
    bool                                  isBranch(void);
    bool                                  isBranchTaken(void);
    const std::string                     &getDisassembly(void);
    const std::string                     &getImageName(void);
    const std::string                     &getRoutineName(void);
    const std::string                     &getSectionName(void);
    const std::vector<TritonOperand>      &getOperands(void);
    sint32                                getOpcodeCategory(void);
    uint32                                getOpcode(void);
    uint64                                getAddress(void);
    uint64                                getBaseAddress(void);
    uint64                                getBranchTargetAddress(void);
    uint64                                getNextAddress(void);
    uint64                                getOffset(void);
    uint64                                getThreadID(void);
    void                                  setBranchTaken(bool flag);
    void                                  setBranchTargetAddress(uint64 addr);
    void                                  setNextAddress(uint64 addr);
    void                                  setOpcode(uint32 op);
    void                                  setOpcodeCategory(sint32 category);
    void                                  setOperands(const std::vector<TritonOperand> &operands);
    #ifndef LIGHT_VERSION
    size_t                                numberOfExpressions(void);
    const std::list<SymbolicExpression*>  &getSymbolicExpressions(void);
    void                                  addExpression(SymbolicExpression *se);
    #endif

    Inst(uint64 threadId,uint64 address, const std::string &insDis);
    ~Inst();
};

#endif /* ! _INST_H_ */
