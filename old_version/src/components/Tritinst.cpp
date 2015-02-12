#include "Tritinst.h"


Tritinst::Tritinst(uint64_t address, std::string insDis)
{
  this->address     = address;
  this->disassembly = insDis;
}


Tritinst::~Tritinst()
{
}

/* Returns the instruction assembly */
const std::string &Tritinst::getDisassembly()
{ 
  return this->disassembly;
}

/* Returns the instruction address */
uint64_t Tritinst::getAddress()
{
  return this->address;
}

/* Adds a new element */
void Tritinst::addElement(SymbolicElement *se)
{
  this->elements.push_back(se);
}

/* Returns the elements list */
const std::list<SymbolicElement*> &Tritinst::getSymbolicElements()
{
  return this->elements;
}

/* Returns the number of elements */
size_t Tritinst::numberOfElements(void)
{
  return this->elements.size();
}

