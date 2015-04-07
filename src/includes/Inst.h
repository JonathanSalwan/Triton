#ifndef _INST_H_
#define _INST_H_

#include <list>
#include <string>

#include "SymbolicElement.h"


class Inst {

  private:
    uint64_t                          threadId;
    uint64_t                          address;
    std::string                       disassembly;
    std::list<SymbolicElement*>       symbolicElements;
    uint32_t                          opcode;

  public:
    const std::list<SymbolicElement*> &getSymbolicElements(void);
    const std::string                 &getDisassembly(void);
    size_t                            numberOfElements(void);
    uint64_t                          getAddress(void);
    uint64_t                          getThreadId(void);
    uint32_t                          getOpcode(void);
    void                              setOpcode(uint32_t op);
    void                              addElement(SymbolicElement *se);

    Inst(uint64_t threadId,uint64_t address, const std::string &insDis);
    ~Inst();
};

#endif /* ! _INST_H_ */
