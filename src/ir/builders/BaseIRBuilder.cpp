#include <boost/format.hpp>
#include <stdexcept>

#include <xed-category-enum.h>
#include <BaseIRBuilder.h>

boost::format outputInstruction("%1% %|15t| %2% %|55t|");


BaseIRBuilder::BaseIRBuilder(uint64 address, const std::string &s):
  address(address),
  disas(s),
  needSetup(false),
  operands()
{

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


void BaseIRBuilder::setOpcodeCategory(int32_t category)
{
  this->opcodeCategory = category;
}


void BaseIRBuilder::setThreadID(uint64 threadId)
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


uint64 BaseIRBuilder::getAddress(void) const
{
  return this->address;
}


const std::string &BaseIRBuilder::getDisassembly(void) const
{
  return this->disas;
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

