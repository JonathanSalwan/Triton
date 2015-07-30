/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <cstdint>
#include <stdexcept>
#include <Registers.h>
#include <TritonOperand.h>



TritonOperand::TritonOperand()
{
  this->baseReg       = ID_INVALID;
  this->displacement  = 0;
  this->indexReg      = ID_INVALID;
  this->memoryScale   = 0;
  this->readAndWrite  = false;
  this->readOnly      = false;
  this->size          = 0;
  this->type          = IRBuilderOperand::UNDEF;
  this->value         = value;
  this->writeOnly     = false;
}


TritonOperand::TritonOperand(const TritonOperand &copy)
{
  this->baseReg       = copy.baseReg;
  this->displacement  = copy.displacement;
  this->indexReg      = copy.indexReg;
  this->memoryScale   = copy.memoryScale;
  this->readAndWrite  = copy.readAndWrite;
  this->readOnly      = copy.readOnly;
  this->size          = copy.size;
  this->type          = copy.type;
  this->value         = copy.value;
  this->writeOnly     = copy.writeOnly;
}


TritonOperand::~TritonOperand(){
}


IRBuilderOperand::operand_t TritonOperand::getType(void) const {
  return this->type;
}


bool TritonOperand::isReadAndWrite(void) const {
  return this->readAndWrite;
}


bool TritonOperand::isReadOnly(void) const {
  return this->readOnly;
}


bool TritonOperand::isWriteOnly(void) const {
  return this->writeOnly;
}


uint64 TritonOperand::getValue(void) const {
  return this->value;
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


void TritonOperand::setReadAndWrite(bool flag) {
  this->readAndWrite = flag;
}


void TritonOperand::setReadOnly(bool flag) {
  this->readOnly = flag;
}


void TritonOperand::setValue(uint64 value) {
  this->value = value;
}


void TritonOperand::setWriteOnly(bool flag) {
  this->writeOnly = flag;
}


void TritonOperand::setBaseReg(uint64 reg) {
  this->baseReg = reg;
}


void TritonOperand::setDisplacement(uint64 displacement) {
  this->displacement = displacement;
}


void TritonOperand::setIndexReg(uint64 reg) {
  this->indexReg = reg;
}


void TritonOperand::setMemoryScale(uint64 memoryScale) {
  this->memoryScale = memoryScale;
}


void TritonOperand::setSize(uint64 size) {
  this->size = size;
}


void TritonOperand::setType(IRBuilderOperand::operand_t type) {
  this->type = type;
}


void TritonOperand::operator=(const TritonOperand &other)
{
  this->baseReg       = other.baseReg;
  this->displacement  = other.displacement;
  this->indexReg      = other.indexReg;
  this->memoryScale   = other.memoryScale;
  this->readAndWrite  = other.readAndWrite;
  this->readOnly      = other.readOnly;
  this->size          = other.size;
  this->type          = other.type;
  this->value         = other.value;
  this->writeOnly     = other.writeOnly;
}

