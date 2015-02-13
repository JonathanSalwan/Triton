#include "Inst.h"


Inst::Inst(uint64_t address, const std::string &insDis):
  address(address), disassembly(insDis)
{
}


Inst::~Inst()
{
}

/* Returns the instruction assembly */
const std::string &Inst::getDisassembly()
{
  return this->disassembly;
}

/* Returns the instruction address */
uint64_t Inst::getAddress()
{
  return this->address;
}

/* Adds a new element */
void Inst::addElement(SymbolicElement *se)
{
  this->elements.push_back(se);
}

/* Returns the elements list */
const std::list<SymbolicElement*> &Inst::getSymbolicElements()
{
  return this->elements;
}

/* Returns the number of elements */
size_t Inst::numberOfElements()
{
  return this->elements.size();
}

