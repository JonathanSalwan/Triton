#include "Instruction.h"



Instruction::Instruction(uint64_t address, std::string insDis)
{
  this->address = address;
  this->disassembly = insDis;
}


Instruction::~Instruction()
{
}


const std::string &Instruction::getDisassembly()
{ 
  return this->disassembly;
}


uint64_t Instruction::getAddress()
{
  return this->address;
}


void Instruction::addElement(const SymbolicElement& se)
{
  this->elements.push_back(se);
}


const std::list<SymbolicElement> &Instruction::getSymbolicElements()
{
  return this->elements;
}

