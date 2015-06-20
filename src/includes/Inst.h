#ifndef TRITON_INST_H
#define TRITON_INST_H

#include <list>
#include <string>
#include <tuple>
#include <vector>

#include "IRBuilderOperand.h"
#include "SymbolicElement.h"
#include "TritonOperand.h"


class Inst {

  private:
    uint64                          threadId;
    uint64                          address;
    std::string                     disassembly;
    std::list<SymbolicElement*>     symbolicElements;
    uint32                          opcode;
    int32_t                         opcodeCategory;
    std::vector<TritonOperand>      operands;

  public:
    const std::list<SymbolicElement*> &getSymbolicElements(void);
    const std::string                 &getDisassembly(void);
    const std::vector<TritonOperand>  &getOperands(void);
    size_t                            numberOfElements(void);
    uint32                            getOpcode(void);
    int32_t                           getOpcodeCategory(void);
    uint64                            getAddress(void);
    uint64                            getThreadID(void);
    void                              addElement(SymbolicElement *se);
    void                              setOpcode(uint32 op);
    void                              setOpcodeCategory(int32_t category);
    bool                              isBranch(void);
    void                              setOperands(const std::vector<TritonOperand> &operands);

    Inst(uint64 threadId,uint64 address, const std::string &insDis);
    ~Inst();
};

#endif /* ! _INST_H_ */
