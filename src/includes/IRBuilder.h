#ifndef _IRBUILDER_H_
#define _IRBUILDER_H_

#include <cstdint>

#include <ostream>
#include <sstream>
#include <string>

#include "contextHandler.h"


// IR interface
class IRBuilder {
  public:
    // Define each type of operand.
    enum operand_t { IMM, REG, MEM_R, MEM_W };

    virtual ~IRBuilder() { }

    // Returns the address of the instruction.
    virtual uint64_t getAddress() const = 0;

    // Returns the assembler instruction.
    virtual const std::string &getDisassembly() const = 0;

    // Add an operand to the IRBuilder.
    // If the value is already now (Immediate value), you can speficy it with value.
    virtual void addOperand(IRBuilder::operand_t, uint64_t value) = 0;

    // Set the value for the MEM_* operand, if there is no such kind of operand
    // it does nothing.
    virtual void setup(uint64_t mem_value) = 0;

    // Check if the setup is done (when needed: i.e get the value for
    // MEM_* operands). If it is not, throws a runtime_error.
    // Should be use in process.
    virtual void checkSetup() const = 0;

    // Process the symbolic Execution.
    virtual std::stringstream *process(const ContextHandler &ctxH) const = 0;

    // Display the IRBuilder in the ostream.
    virtual void display(std::ostream &os) const = 0;

    // Check if the operand is of type MEM_*
    static bool isMemOperand(IRBuilder::operand_t type) {
      return (type == IRBuilder::MEM_R) || (type == IRBuilder::MEM_W);
    }

};


// Operators overloading
// Virtual Friend function idiom
inline std::ostream& operator<<(std::ostream& os, const IRBuilder& ir) {
  ir.display(os);
  return os;
}

#endif // _IRBUILDER_H_
