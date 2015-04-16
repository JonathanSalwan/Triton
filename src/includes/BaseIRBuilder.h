#ifndef _BASEIRBUILDER_H_
#define _BASEIRBUILDER_H_

#include <ostream>
#include <sstream>
#include <tuple>
#include <vector>

#include "ContextHandler.h"
#include "IRBuilder.h"

// Abstract class which is main purpose is too implement common methods
// shared by its children classes.
class BaseIRBuilder: public IRBuilder {
  public:
    // Constructor take the two main informations of an instruction.
    BaseIRBuilder(uint64_t address, const std::string &disassembly);

    virtual uint32_t            getOpcode(void) const;
    virtual uint64_t            getThreadID(void) const;
    virtual void                setOpcode(uint32_t op);
    virtual void                setOpcodeCategory(int32_t category);
    virtual void                setThreadID(uint64_t threadId);
    virtual int32_t             getOpcodeCategory(void);
    virtual bool                isBranch(void);
    virtual uint64_t            getAddress(void) const;
    virtual const std::string   &getDisassembly(void) const;

    virtual const std::vector< std::tuple<IRBuilderOperand::operand_t, uint64_t, uint32_t> > &getOperands(void) const;

    // Add an operand to IRBuilder.
    // If it's type is:
    //  - IMM (Immediate), the value is the immediate value.
    //  - REG (Register), the value is the register ID.
    //  - MEM_*, the value doesn't mean anything and it's unused.
    //    The object will need a setup before any processing.
    virtual void addOperand(IRBuilderOperand::operand_t type, uint64_t value = 0, uint32_t size = 0);

    virtual void setup(uint64_t mem_value);

    virtual void checkSetup() const;

  protected:
    uint32_t        opcode;
    uint64_t        address;
    std::string     disas;
    bool            needSetup;
    int32_t         opcodeCategory;
    uint64_t        threadId;
    std::vector< std::tuple<IRBuilderOperand::operand_t, uint64_t, uint32_t> > operands;
};

#endif // _BASEIRBUILDER_H_
