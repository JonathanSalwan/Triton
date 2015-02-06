#ifndef _TRITINST_H_
#define _TRITINST_H_

#include <list>
#include <string>

#include "SymbolicElement.h"


class Tritinst {

  private:
    uint64_t                          address;
    std::string                       disassembly;
    std::list<SymbolicElement*>       elements;

  public:
    const std::list<SymbolicElement*> &getSymbolicElements();
    const std::string                 &getDisassembly();
    uint64_t                          getAddress();
    void                              addElement(SymbolicElement *se);

    Tritinst(uint64_t address, std::string insDis);
    ~Tritinst();
};

#endif /* ! _TRITINST_H_ */
