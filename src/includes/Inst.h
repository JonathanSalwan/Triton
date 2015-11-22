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
    __uint                                address;
    __uint                                baseAddress;
    __uint                                branchTargetAddress;
    __uint                                nextAddress;
    __uint                                offset;
    __uint                                threadId;
    #ifndef LIGHT_VERSION
    std::list<SymbolicExpression*>        symbolicExpressions;
    #endif

  public:
    __uint                                getAddress(void);
    __uint                                getBaseAddress(void);
    __uint                                getBranchTargetAddress(void);
    __uint                                getNextAddress(void);
    __uint                                getOffset(void);
    __uint                                getThreadID(void);
    bool                                  isBranch(void);
    bool                                  isBranchTaken(void);
    const std::string                     &getDisassembly(void);
    const std::string                     &getImageName(void);
    const std::string                     &getRoutineName(void);
    const std::string                     &getSectionName(void);
    const std::vector<TritonOperand>      &getOperands(void);
    sint32                                getOpcodeCategory(void);
    uint32                                getOpcode(void);
    void                                  importIrbInformation(void *irbv);
    void                                  setBranchTaken(bool flag);
    void                                  setBranchTargetAddress(__uint addr);
    void                                  setNextAddress(__uint addr);
    void                                  setOpcode(uint32 op);
    void                                  setOpcodeCategory(sint32 category);
    void                                  setOperands(const std::vector<TritonOperand> &operands);
    #ifndef LIGHT_VERSION
    size_t                                numberOfExpressions(void);
    const std::list<SymbolicExpression*>  &getSymbolicExpressions(void);
    void                                  addExpression(SymbolicExpression *se);
    #endif

    Inst(__uint threadId,__uint address, const std::string &insDis);
    ~Inst();
};

#endif /* ! _INST_H_ */
