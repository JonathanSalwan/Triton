#include <boost/format.hpp>
#include <stdexcept>

#include "BaseIRBuilder.h"

boost::format outputInstruction("%1% %|15t| %2% %|55t|");


BaseIRBuilder::BaseIRBuilder(uint64_t address, const std::string &s):
  _address(address),
  _disas(s),
  _needSetup(false),
  _operands()
{

}


uint64_t BaseIRBuilder::getAddress() const
{
  return _address;
}

const std::string &BaseIRBuilder::getDisassembly() const
{
  return _disas;
}


void BaseIRBuilder::addOperand(IRBuilder::operand_t type, uint64_t value, uint32_t size)
{
  if (IRBuilder::isMemOperand(type))
    _needSetup = true;

  _operands.push_back(std::make_tuple(type, value, size));
}


void BaseIRBuilder::setup(uint64_t mem_value)
{
  for (auto it = _operands.begin(); it != _operands.end(); ++it)
    if (IRBuilder::isMemOperand(std::get<0>(*it))) {
      std::get<1>(*it) = mem_value;
      _needSetup = false;
      break;
    }
}


void BaseIRBuilder::checkSetup() const {
  if (_needSetup)
    throw std::runtime_error("Error: IRBuilder.setup must be call before "
                             "IRBuilder.process, when there are MEM_* operands.");
}


// Utilities functions

//static const char * enum2Text(IRBuilder::operand_t val)
//{
//  return (const char *[]){"IMM", "REG", "MEM_R", "MEM_W"}[val];
//}

void BaseIRBuilder::display(std::ostream &os) const {

  os << boost::format(outputInstruction) % boost::io::group(std::hex, std::showbase, this->_address) % this->_disas;

  //if (!_operands.empty()) {
  //  os  << "\t[";

  //  for (auto it = _operands.begin(); it != _operands.end(); ++it) {
  //    os << "("  << std::dec << enum2Text(it->first)
  //       << ", " << std::hex << it->second << ")";

  //    if (it < --_operands.end())
  //      os << ", ";
  //  }

  //  os << "]";
  //}

  os << std::dec << std::noshowbase;
}

