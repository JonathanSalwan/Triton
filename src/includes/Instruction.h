#ifndef _INSTRUCTION_H_
#define _INSTRUCTION_H_

#include <list>
#include <string>

#include "SymbolicElement.h"


class Instruction {
  private:
    uint64_t address;
    std::string disassembly;
    std::list<symbolicElement> elements;

  public:
    Instruction(uint64_t at, std::string insDis):
      address(at),
      disassembly(insDis),
      elements() {}

    ~Instruction();

    const std::string &getDisassembly() { return disassembly; }
    uint64_t getAddress() { return address; }

    const std::list<symbolicElement> &getSymbolicElements();
    void addElement(const symbolicElement& se);
};

#endif /* ! _INSTRUCTION_H_ */
