
#ifndef   __TRITONOPERAND_H__
#define   __TRITONOPERAND_H__

#include "IRBuilderOperand.h"


class TritonOperand {

  private:
    IRBuilderOperand::operand_t type;
    uint64_t value;
    uint64_t size;
    uint64_t displacement;
    uint64_t baseReg;
    uint64_t indexReg;
    uint64_t memoryScale;


  public:
    TritonOperand(IRBuilderOperand::operand_t type,
                  uint64_t value,
                  uint64_t size);

    TritonOperand(IRBuilderOperand::operand_t type,
                  uint64_t value,
                  uint64_t size,
                  uint64_t displacement,
                  uint64_t baseReg,
                  uint64_t indexReg,
                  uint64_t memoryScale);

    ~TritonOperand();

    IRBuilderOperand::operand_t getType(void);
    uint64_t getValue(void);
    uint64_t getSize(void);
    uint64_t getDisplacement(void);
    uint64_t getBaseReg(void);
    uint64_t getIndexReg(void);
    uint64_t getMemoryScale(void);

    uint64_t operator[](const int index);
};

#endif     /* !__TRITONOPERAND_H__ */
