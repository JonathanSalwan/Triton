
#ifndef   TRITONOPERAND_H
#define   TRITONOPERAND_H

#include <cstdint>
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

    TritonOperand(const TritonOperand &copy);

    ~TritonOperand();

    IRBuilderOperand::operand_t getType(void) const;
    uint64_t getValue(void) const;
    uint64_t getSize(void) const;
    uint64_t getDisplacement(void) const;
    uint64_t getBaseReg(void) const;
    uint64_t getIndexReg(void) const;
    uint64_t getMemoryScale(void) const;
    void     setValue(uint64_t value);

    uint64_t operator[](const int index);
    void operator=(const TritonOperand &other);
};

#endif     /* !__TRITONOPERAND_H__ */
