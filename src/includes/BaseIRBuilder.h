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

    virtual uint64_t getAddress() const;
    virtual const std::string &getDisassembly() const;


    // Add an operand to IRBuilder.
    // If it's type is:
    //  - IMM (Immediate), the value is the immediate value.
    //  - REG (Register), the value is the register ID.
    //  - MEM_*, the value doesn't mean anything and it's unused.
    //    The object will need a setup before any processing.
    virtual void addOperand(IRBuilder::operand_t type, uint64_t value = 0, uint32_t size = 0);

    virtual void setup(uint64_t mem_value);

    virtual void checkSetup() const;

    virtual void display(std::ostream &os) const;

  protected:
    uint64_t        _address;
    std::string     _disas;
    bool            _needSetup;
    std::vector< std::tuple<IRBuilder::operand_t, uint64_t, uint32_t> > _operands;
};

#endif // _BASEIRBUILDER_H_
