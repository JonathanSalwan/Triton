#ifndef INST_H
#define INST_H

#include <list>
#include <string>
#include <tuple>
#include <vector>

#include "IRBuilderOperand.h"
#include "SymbolicElement.h"
#include "TritonOperand.h"


class Inst {

  private:
    uint64_t                          threadId;
    uint64_t                          address;
    std::string                       disassembly;
    std::list<SymbolicElement*>       symbolicElements;
    uint32_t                          opcode;
    int32_t                           opcodeCategory;
    std::vector<TritonOperand>        operands;

  public:
    const std::list<SymbolicElement*> &getSymbolicElements(void);
    const std::string                 &getDisassembly(void);
    const std::vector<TritonOperand>  &getOperands(void);
    size_t                            numberOfElements(void);
    uint32_t                          getOpcode(void);
    int32_t                           getOpcodeCategory(void);
    uint64_t                          getAddress(void);
    uint64_t                          getThreadID(void);
    void                              addElement(SymbolicElement *se);
    void                              setOpcode(uint32_t op);
    void                              setOpcodeCategory(int32_t category);
    bool                              isBranch(void);
    void                              setOperands(const std::vector<TritonOperand> &operands);

    Inst(uint64_t threadId,uint64_t address, const std::string &insDis);
    ~Inst();
};

#endif /* ! _INST_H_ */
