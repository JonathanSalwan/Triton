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
#include "SymbolicExpression.h"
#include "TritonOperand.h"


class Inst {

  private:
    sint32                                opcodeCategory;
    std::list<SymbolicExpression*>        symbolicExpressions;
    std::string                           disassembly;
    std::string                           imageName;
    std::string                           routineName;
    std::string                           sectionName;
    std::vector<TritonOperand>            operands;
    uint32                                opcode;
    uint64                                address;
    uint64                                baseAddress;
    uint64                                offset;
    uint64                                threadId;

  public:
    bool                                  isBranch(void);
    const std::list<SymbolicExpression*>  &getSymbolicExpressions(void);
    const std::string                     &getDisassembly(void);
    const std::string                     &getImageName(void);
    const std::string                     &getRoutineName(void);
    const std::string                     &getSectionName(void);
    const std::vector<TritonOperand>      &getOperands(void);
    sint32                                getOpcodeCategory(void);
    size_t                                numberOfExpressions(void);
    uint32                                getOpcode(void);
    uint64                                getAddress(void);
    uint64                                getBaseAddress(void);
    uint64                                getOffset(void);
    uint64                                getThreadID(void);
    void                                  addExpression(SymbolicExpression *se);
    void                                  setOpcode(uint32 op);
    void                                  setOpcodeCategory(sint32 category);
    void                                  setOperands(const std::vector<TritonOperand> &operands);

    Inst(uint64 threadId,uint64 address, const std::string &insDis);
    ~Inst();
};

#endif /* ! _INST_H_ */
