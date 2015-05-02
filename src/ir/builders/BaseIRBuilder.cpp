#include <boost/format.hpp>
#include <stdexcept>

#include "xed-category-enum.h"
#include "BaseIRBuilder.h"

boost::format outputInstruction("%1% %|15t| %2% %|55t|");


BaseIRBuilder::BaseIRBuilder(uint64_t address, const std::string &s):
  address(address),
  disas(s),
  needSetup(false),
  operands()
{

}


uint32_t BaseIRBuilder::getOpcode(void) const
{
  return this->opcode;
}


uint64_t BaseIRBuilder::getThreadID(void) const
{
  return this->threadId;
}


void BaseIRBuilder::setOpcode(uint32_t op)
{
  this->opcode = op;
}


void BaseIRBuilder::setNextAddress(uint64_t nextAddress)
{
  this->nextAddress = nextAddress;
}


void BaseIRBuilder::setOpcodeCategory(int32_t category)
{
  this->opcodeCategory = category;
}


void BaseIRBuilder::setThreadID(uint64_t threadId)
{
  this->threadId = threadId;
}


int32_t BaseIRBuilder::getOpcodeCategory(void)
{
  return this->opcodeCategory;
}


bool BaseIRBuilder::isBranch(void)
{
  return (this->opcodeCategory == XED_CATEGORY_COND_BR);
}


uint64_t BaseIRBuilder::getAddress(void) const
{
  return this->address;
}


const std::string &BaseIRBuilder::getDisassembly(void) const
{
  return this->disas;
}


const std::vector< std::tuple<IRBuilderOperand::operand_t, uint64_t, uint32_t> > &BaseIRBuilder::getOperands(void) const
{
  return this->operands;
}


void BaseIRBuilder::addOperand(IRBuilderOperand::operand_t type, uint64_t value, uint32_t size)
{
  if (IRBuilder::isMemOperand(type))
    this->needSetup = true;

  this->operands.push_back(std::make_tuple(type, value, size));
}


void BaseIRBuilder::setup(uint64_t mem_value)
{
  for (auto it = this->operands.begin(); it != this->operands.end(); ++it)
    if (IRBuilder::isMemOperand(std::get<0>(*it))) {
      std::get<1>(*it) = mem_value;
      this->needSetup = false;
      break;
    }
}


void BaseIRBuilder::checkSetup() const {
  if (this->needSetup)
    throw std::runtime_error("Error: IRBuilder.setup must be call before "
                             "IRBuilder.process, when there are MEM_* operands.");
}
