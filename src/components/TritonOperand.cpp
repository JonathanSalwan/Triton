
#include <cstdint>
#include <stdexcept>
#include <TritonOperand.h>



TritonOperand::TritonOperand(IRBuilderOperand::operand_t type,
              uint64 value,
              uint64 size)
{
  this->type          = type;
  this->value         = value;
  this->size          = size;
  this->displacement  = 0;
  this->baseReg       = 0;
  this->indexReg      = 0;
  this->memoryScale   = 0;
}


TritonOperand::TritonOperand(IRBuilderOperand::operand_t type,
              uint64 value,
              uint64 size,
              uint64 displacement,
              uint64 baseReg,
              uint64 indexReg,
              uint64 memoryScale)
{
  this->type          = type;
  this->value         = value;
  this->size          = size;
  this->displacement  = displacement;
  this->baseReg       = baseReg;
  this->indexReg      = indexReg;
  this->memoryScale   = memoryScale;
}

TritonOperand::TritonOperand(const TritonOperand &copy)
{
  this->type          = copy.type;
  this->value         = copy.value;
  this->size          = copy.size;
  this->displacement  = copy.displacement;
  this->baseReg       = copy.baseReg;
  this->indexReg      = copy.indexReg;
  this->memoryScale   = copy.memoryScale;
}


TritonOperand::~TritonOperand(){
}


IRBuilderOperand::operand_t TritonOperand::getType(void) const {
  return this->type;
}


uint64 TritonOperand::getValue(void) const {
  return this->value;
}


void TritonOperand::setValue(uint64 value) {
  this->value = value;
}


uint64 TritonOperand::getSize(void) const {
  return this->size;
}


uint64 TritonOperand::getDisplacement(void) const {
  return this->displacement;
}


uint64 TritonOperand::getBaseReg(void) const {
  return this->baseReg;
}


uint64 TritonOperand::getIndexReg(void) const {
  return this->indexReg;
}


uint64 TritonOperand::getMemoryScale(void) const {
  return this->memoryScale;
}


uint64 TritonOperand::operator[](const int index){
  switch (index){
    case 0: return this->type;
    case 1: return this->value;
    case 2: return this->size;
    case 3: return this->displacement;
    case 4: return this->baseReg;
    case 5: return this->indexReg;
    case 6: return this->memoryScale;
    default:
      throw std::out_of_range("Error: TritonOperand - Index out of range");
  }
  return 0;
}


void TritonOperand::operator=(const TritonOperand &other)
{
  this->type          = other.type;
  this->value         = other.value;
  this->size          = other.size; 
  this->displacement  = other.displacement;
  this->baseReg       = other.baseReg;
  this->indexReg      = other.indexReg;
  this->memoryScale   = other.memoryScale;
}


