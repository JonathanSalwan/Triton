
#include <cstdint>
#include <stdexcept>
#include "TritonOperand.h"



TritonOperand::TritonOperand(IRBuilderOperand::operand_t type,
              uint64_t value,
              uint64_t size)
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
              uint64_t value,
              uint64_t size,
              uint64_t displacement,
              uint64_t baseReg,
              uint64_t indexReg,
              uint64_t memoryScale)
{
  this->type          = type;
  this->value         = value;
  this->size          = size; 
  this->displacement  = displacement;
  this->baseReg       = baseReg;
  this->indexReg      = indexReg;
  this->memoryScale   = memoryScale;
}


TritonOperand::~TritonOperand(){
}


IRBuilderOperand::operand_t TritonOperand::getType(void) {
  return this->type;
}


uint64_t TritonOperand::getValue(void) {
  return this->value;
}


uint64_t TritonOperand::getSize(void) {
  return this->size;
}


uint64_t TritonOperand::getDisplacement(void) {
  return this->displacement;
}


uint64_t TritonOperand::getBaseReg(void) {
  return this->baseReg;
}


uint64_t TritonOperand::getIndexReg(void) {
  return this->indexReg;
}


uint64_t TritonOperand::getMemoryScale(void) {
  return this->memoryScale;
}


uint64_t TritonOperand::operator[](const int index){
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


