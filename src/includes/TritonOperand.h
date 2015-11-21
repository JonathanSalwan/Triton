/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#ifndef   TRITONOPERAND_H
#define   TRITONOPERAND_H

#include "IRBuilderOperand.h"
#include "ImmediateOperand.h"
#include "MemoryOperand.h"
#include "RegisterOperand.h"
#include "TritonTypes.h"


class TritonOperand {

  private:

    /* Info */
    IRBuilderOperand::operand_t   type;
    bool                          readAndWrite;
    bool                          readOnly;
    bool                          writeOnly;

    /* Default */
    ImmediateOperand              imm;
    MemoryOperand                 mem;
    RegisterOperand               reg;

    /* LEA */
    ImmediateOperand              displacement;
    ImmediateOperand              memoryScale;
    RegisterOperand               baseReg;
    RegisterOperand               indexReg;

    void copy(const TritonOperand& other);

  public:
    TritonOperand();
    TritonOperand(const TritonOperand& copy);
    ~TritonOperand();

    IRBuilderOperand::operand_t getType(void) const;
    bool                        isReadAndWrite(void) const;
    bool                        isReadOnly(void) const;
    bool                        isWriteOnly(void) const;
    const ImmediateOperand&     getDisplacement(void) const;
    const ImmediateOperand&     getImm(void) const;
    const ImmediateOperand&     getMemoryScale(void) const;
    const MemoryOperand&        getMem(void) const;
    const RegisterOperand&      getBaseReg(void) const;
    const RegisterOperand&      getIndexReg(void) const;
    const RegisterOperand&      getReg(void) const;
    void                        setBaseReg(RegisterOperand reg);
    void                        setDisplacement(ImmediateOperand displacement);
    void                        setImm(ImmediateOperand imm);
    void                        setIndexReg(RegisterOperand reg);
    void                        setMem(MemoryOperand mem);
    void                        setMemAddress(__uint addr);
    void                        setMemSize(__uint size);
    void                        setMemoryScale(ImmediateOperand memoryScale);
    void                        setReadAndWrite(bool flag);
    void                        setReadOnly(bool flag);
    void                        setReg(RegisterOperand reg);
    void                        setRegSize(__uint size);
    void                        setType(IRBuilderOperand::operand_t type);
    void                        setWriteOnly(bool flag);

    void                        operator=(const TritonOperand& other);
};

#endif     /* !__TRITONOPERAND_H__ */
