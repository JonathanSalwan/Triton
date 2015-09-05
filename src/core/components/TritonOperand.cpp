/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <cstdint>
#include <stdexcept>
#include <Registers.h>
#include <TritonOperand.h>



TritonOperand::TritonOperand() {
  this->baseReg       = ID_INVALID;
  this->displacement  = 0;
  this->indexReg      = ID_INVALID;
  this->memoryScale   = 0;
  this->readAndWrite  = false;
  this->readOnly      = false;
  this->type          = IRBuilderOperand::UNDEF;
  this->writeOnly     = false;
}


TritonOperand::TritonOperand(const TritonOperand& other) {
  this->copy(other);
}


TritonOperand::~TritonOperand() {
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


const ImmediateOperand& TritonOperand::getDisplacement(void) const {
  return this->displacement;
}


const RegisterOperand& TritonOperand::getBaseReg(void) const {
  return this->baseReg;
}


const RegisterOperand& TritonOperand::getIndexReg(void) const {
  return this->indexReg;
}


const ImmediateOperand& TritonOperand::getMemoryScale(void) const {
  return this->memoryScale;
}


const ImmediateOperand& TritonOperand::getImm(void) const {
  return this->imm;
}


const MemoryOperand& TritonOperand::getMem(void) const {
  return this->mem;
}


const RegisterOperand& TritonOperand::getReg(void) const {
  return this->reg;
}


void TritonOperand::setReadAndWrite(bool flag) {
  this->readAndWrite = flag;
}


void TritonOperand::setReadOnly(bool flag) {
  this->readOnly = flag;
}


void TritonOperand::setWriteOnly(bool flag) {
  this->writeOnly = flag;
}


void TritonOperand::setBaseReg(RegisterOperand reg) {
  this->baseReg = reg;
}


void TritonOperand::setDisplacement(ImmediateOperand displacement) {
  this->displacement = displacement;
}


void TritonOperand::setIndexReg(RegisterOperand reg) {
  this->indexReg = reg;
}


void TritonOperand::setMemoryScale(ImmediateOperand memoryScale) {
  this->memoryScale = memoryScale;
}


void TritonOperand::setType(IRBuilderOperand::operand_t type) {
  this->type = type;
}


void TritonOperand::setImm(ImmediateOperand imm) {
  this->imm = imm;
}


void TritonOperand::setMem(MemoryOperand mem) {
  this->mem = mem;
}


void TritonOperand::setMemAddress(uint64 addr) {
  this->mem.setAddress(addr);
}


void TritonOperand::setMemSize(uint64 size) {
  this->mem.setSize(size);
}


void TritonOperand::setReg(RegisterOperand reg) {
  this->reg = reg;
}


void TritonOperand::setRegSize(uint64 size) {
  this->reg.setSize(size);
}


void TritonOperand::operator=(const TritonOperand& other) {
  copy(other);
}


void TritonOperand::copy(const TritonOperand& other) {
  this->baseReg       = other.baseReg;
  this->displacement  = other.displacement;
  this->imm           = other.imm;
  this->indexReg      = other.indexReg;
  this->mem           = other.mem;
  this->memoryScale   = other.memoryScale;
  this->readAndWrite  = other.readAndWrite;
  this->readOnly      = other.readOnly;
  this->reg           = other.reg;
  this->type          = other.type;
  this->writeOnly     = other.writeOnly;
}

