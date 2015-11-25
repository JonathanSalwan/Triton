/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef IRBUILDER_H
#define IRBUILDER_H

#include "TritonTypes.h"

#include <ostream>
#include <string>

#include "ContextHandler.h"
#include "IRBuilderOperand.h"
#include "Inst.h"
#include "TritonOperand.h"


// IR interface
class IRBuilder {
  public:

    virtual ~IRBuilder() { }

    // Returns the opcode of the instruction.
    virtual uint32 getOpcode(void) const = 0;

    // Returns the thread ID of the Irb.
    virtual __uint getThreadID(void) const = 0;

    // Set the opcode of the instruction.
    virtual void setOpcode(uint32 op) = 0;

    // Set the next instruction address
    virtual void setNextAddress(__uint nextAddr) = 0;

    // Set the branch taken flag.
    virtual void setBranchTaken(bool flag) = 0;

    // Set the target branch address.
    virtual void setBranchTargetAddress(__uint addr) = 0;

    // Set the opcode of the instruction.
    virtual void setThreadID(__uint threadId) = 0;

    // Set the opcode category.
    virtual void setOpcodeCategory(sint32 category) = 0;

    // Get the opcode category.
    virtual sint32 getOpcodeCategory(void) const = 0;

    // Returns true or false if the instruction is branch.
    virtual bool isBranch(void) = 0;

    // Returns true or false if the branch is taken.
    virtual bool isBranchTaken(void) = 0;

    // Returns the address of the instruction.
    virtual __uint getAddress(void) const = 0;

    // Returns the base address.
    virtual __uint getBaseAddress(void) const = 0;

    // Returns the next instruction address.
    virtual __uint getNextAddress(void) const = 0;

    // Returns the target address if the instruction is a brancho.
    virtual __uint getBranchTargetAddress(void) const = 0;

    // Returns the offset of the instruction in the file.
    virtual __uint getOffset(void) const = 0;

    // Returns the assembler instruction.
    virtual const std::string &getDisassembly(void) const = 0;

    // Returns the image name.
    virtual const std::string &getImageName(void) const = 0;

    // Returns the section name.
    virtual const std::string &getSectionName(void) const = 0;

    // Returns the routine name.
    virtual const std::string &getRoutineName(void) const = 0;

    // Returns the operands vector.
    virtual const std::vector<TritonOperand> &getOperands(void) const = 0;

    // Add an operand to IRBuilder.
    // If it's type is:
    //  - IMM (Immediate), the value is the immediate value.
    //  - REG (Register), the value is the register ID.
    //  - MEM_*, the value doesn't mean anything and it's unused.
    //    The object will need a setup before any processing.
    virtual void addOperand(const TritonOperand &operand) = 0;

    // Set the value for the MEM_* operand, if there is no such kind of operand
    // it does nothing.
    virtual void setup(__uint mem_value) = 0;

    // Check if the setup is done (when needed: i.e get the value for
    // MEM_* operands). If it is not, throws a runtime_error.
    // Should be use in process.
    virtual void checkSetup(void) const = 0;

    // Process the symbolic execution and the taint analysis.
    virtual Inst *process(void) const = 0;

    // Check if the operand is of type MEM_*
    static bool isMemOperand(IRBuilderOperand::operand_t type) {
      return (type == IRBuilderOperand::MEM_R) || (type == IRBuilderOperand::MEM_W);
    }

};

#endif // IRBUILDER_H

