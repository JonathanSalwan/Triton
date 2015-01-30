#ifndef _INSTRUCTION_H_
#define _INSTRUCTION_H_

#include <list>
#include <string>

#include "SymbolicElement.h"


class Instruction {

  private:
    uint64_t                    address;
    std::string                 disassembly;
    std::list<SymbolicElement>  elements;

  public:

    Instruction(uint64_t address, std::string insDis);
    ~Instruction();

    const std::list<SymbolicElement>  &getSymbolicElements();
    const std::string                 &getDisassembly();
    uint64_t                          getAddress();
    void                              addElement(const SymbolicElement& se);
};

#endif /* ! _INSTRUCTION_H_ */
