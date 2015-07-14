
#ifndef   TRITONOPERAND_H
#define   TRITONOPERAND_H

#include "TritonTypes.h"
#include "IRBuilderOperand.h"


class TritonOperand {

  private:
    IRBuilderOperand::operand_t type;
    bool   readAndWrite;
    bool   readOnly;
    bool   writeOnly;
    uint64 baseReg;
    uint64 displacement;
    uint64 indexReg;
    uint64 memoryScale;
    uint64 size;
    uint64 value;


  public:
    TritonOperand(IRBuilderOperand::operand_t type,
                  uint64 value,
                  uint64 size);

    TritonOperand(IRBuilderOperand::operand_t type,
                  uint64 value,
                  uint64 size,
                  uint64 displacement,
                  uint64 baseReg,
                  uint64 indexReg,
                  uint64 memoryScale);

    TritonOperand(const TritonOperand &copy);

    ~TritonOperand();

    IRBuilderOperand::operand_t getType(void) const;
    bool    isReadAndWrite(void) const;
    bool    isReadOnly(void) const;
    bool    isWriteOnly(void) const;
    uint64  getBaseReg(void) const;
    uint64  getDisplacement(void) const;
    uint64  getIndexReg(void) const;
    uint64  getMemoryScale(void) const;
    uint64  getSize(void) const;
    uint64  getValue(void) const;
    void    setReadAndWrite(bool flag);
    void    setReadOnly(bool flag);
    void    setValue(uint64 value);
    void    setWriteOnly(bool flag);

    uint64  operator[](const int index);
    void    operator=(const TritonOperand &other);
};

#endif     /* !__TRITONOPERAND_H__ */
