
#ifndef   TRITONOPERAND_H
#define   TRITONOPERAND_H

#include "TritonTypes.h"
#include "IRBuilderOperand.h"


class TritonOperand {

  private:
    IRBuilderOperand::operand_t type;
    uint64 value;
    uint64 size;
    uint64 displacement;
    uint64 baseReg;
    uint64 indexReg;
    uint64 memoryScale;


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
    uint64 getValue(void) const;
    uint64 getSize(void) const;
    uint64 getDisplacement(void) const;
    uint64 getBaseReg(void) const;
    uint64 getIndexReg(void) const;
    uint64 getMemoryScale(void) const;
    void   setValue(uint64 value);

    uint64 operator[](const int index);
    void operator=(const TritonOperand &other);
};

#endif     /* !__TRITONOPERAND_H__ */
