/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>

#include <pin.H>
#include <BaseIRBuilder.h>



BaseIRBuilder::BaseIRBuilder(uint64 address, const std::string &dis)
{
  this->address     = address;
  this->baseAddress = IMG_LowAddress(SEC_Img(RTN_Sec(RTN_FindByAddress(address))));
  this->disas       = dis;
  this->imageName   = IMG_Name(SEC_Img(RTN_Sec(RTN_FindByAddress(address))));
  this->needSetup   = false;
  this->offset      = this->address - this->baseAddress;
  this->routineName = RTN_FindNameByAddress(address);
  this->sectionName = SEC_Name(RTN_Sec(RTN_FindByAddress(address)));
}


uint32 BaseIRBuilder::getOpcode(void) const
{
  return this->opcode;
}


uint64 BaseIRBuilder::getThreadID(void) const
{
  return this->threadId;
}


void BaseIRBuilder::setOpcode(uint32 op)
{
  this->opcode = op;
}


void BaseIRBuilder::setNextAddress(uint64 nextAddress)
{
  this->nextAddress = nextAddress;
}


void BaseIRBuilder::setOpcodeCategory(sint32 category)
{
  this->opcodeCategory = category;
}


void BaseIRBuilder::setThreadID(uint64 threadId)
{
  this->threadId = threadId;
}


sint32 BaseIRBuilder::getOpcodeCategory(void) const
{
  return this->opcodeCategory;
}


bool BaseIRBuilder::isBranch(void)
{
  return (this->opcodeCategory == XED_CATEGORY_COND_BR);
}


uint64 BaseIRBuilder::getAddress(void) const
{
  return this->address;
}


uint64 BaseIRBuilder::getBaseAddress(void) const
{
  return this->baseAddress;
}


uint64 BaseIRBuilder::getOffset(void) const
{
  return this->offset;
}


const std::string &BaseIRBuilder::getDisassembly(void) const
{
  return this->disas;
}


const std::string &BaseIRBuilder::getImageName(void) const
{
  return this->imageName;
}


const std::string &BaseIRBuilder::getSectionName(void) const
{
  return this->imageName;
}


const std::string &BaseIRBuilder::getRoutineName(void) const
{
  return this->routineName;
}


const std::vector<TritonOperand> &BaseIRBuilder::getOperands(void) const
{
  return this->operands;
}


void BaseIRBuilder::addOperand(const TritonOperand &operand)
{
  if (IRBuilder::isMemOperand(operand.getType()))
    this->needSetup = true;

  this->operands.push_back(operand);
}


void BaseIRBuilder::setup(uint64 mem_value)
{
  for (auto it = this->operands.begin(); it != this->operands.end(); ++it)
    if (IRBuilder::isMemOperand(it->getType())) {
      it->setValue(mem_value);
      this->needSetup = false;
      break;
    }
}


void BaseIRBuilder::checkSetup() const {
  if (this->needSetup)
    throw std::runtime_error("Error: IRBuilder.setup must be call before "
                             "IRBuilder.process, when there are MEM_* operands.");
}

