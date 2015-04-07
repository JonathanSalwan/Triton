#include <boost/format.hpp>
#include <stdexcept>

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


void BaseIRBuilder::setOpcode(uint32_t op)
{
  this->opcode = op;
}


uint64_t BaseIRBuilder::getAddress(void) const
{
  return this->address;
}


const std::string &BaseIRBuilder::getDisassembly(void) const
{
  return this->disas;
}


void BaseIRBuilder::addOperand(IRBuilder::operand_t type, uint64_t value, uint32_t size)
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
