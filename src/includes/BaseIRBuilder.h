/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef BASEIRBUILDER_H
#define BASEIRBUILDER_H

#include <ostream>
#include <sstream>
#include <tuple>
#include <vector>

#include "ContextHandler.h"
#include "IRBuilder.h"
#include "TritonOperand.h"

#ifndef LIGHT_VERSION
  #include "ControlFlow.h"
#endif


// Abstract class which is main purpose is too implement common methods
// shared by its children classes.
class BaseIRBuilder: public IRBuilder {
  public:
    // Constructor take the two main informations of an instruction.
    BaseIRBuilder(reg_size address, const std::string &disassembly);

    virtual bool                isBranch(void);
    virtual bool                isBranchTaken(void);
    virtual const std::string   &getDisassembly(void) const;
    virtual const std::string   &getImageName(void) const;
    virtual const std::string   &getRoutineName(void) const;
    virtual const std::string   &getSectionName(void) const;
    virtual sint32              getOpcodeCategory(void) const;
    virtual uint32              getOpcode(void) const;
    virtual reg_size              getAddress(void) const;
    virtual reg_size              getBaseAddress(void) const;
    virtual reg_size              getBranchTargetAddress(void) const;
    virtual reg_size              getNextAddress(void) const;
    virtual reg_size              getOffset(void) const;
    virtual reg_size              getThreadID(void) const;
    virtual void                setBranchTaken(bool flag);
    virtual void                setBranchTargetAddress(reg_size addr);
    virtual void                setNextAddress(reg_size nextAddr);
    virtual void                setOpcode(uint32 op);
    virtual void                setOpcodeCategory(sint32 category);
    virtual void                setThreadID(reg_size threadId);


    virtual const std::vector<TritonOperand> &getOperands(void) const;

    // Add an operand to IRBuilder.
    // If it's type is:
    //  - IMM (Immediate), the value is the immediate value.
    //  - REG (Register), the value is the register ID.
    //  - MEM_*, the value doesn't mean anything and it's unused.
    //    The object will need a setup before any processing.
    virtual void addOperand(const TritonOperand &operand);

    virtual void setup(reg_size mem_value);

    virtual void checkSetup() const;

  protected:
    bool                        branchTaken;
    bool                        needSetup;
    sint32                      opcodeCategory;
    std::string                 disas;
    std::string                 imageName;
    std::string                 routineName;
    std::string                 sectionName;
    std::vector<TritonOperand>  operands;
    uint32                      opcode;
    reg_size                      address;
    reg_size                      baseAddress;
    reg_size                      branchTargetAddress;
    reg_size                      nextAddress;
    reg_size                      offset;
    reg_size                      threadId;
};

#endif // BASEIRBUILDER_H

