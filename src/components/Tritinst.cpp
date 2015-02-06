#include "Tritinst.h"



Tritinst::Tritinst(uint64_t address, std::string insDis)
{
  this->address = address;
  this->disassembly = insDis;
}


Tritinst::~Tritinst()
{
}


const std::string &Tritinst::getDisassembly()
{ 
  return this->disassembly;
}


uint64_t Tritinst::getAddress()
{
  return this->address;
}


void Tritinst::addElement(SymbolicElement *se)
{
  this->elements.push_back(se);
}


const std::list<SymbolicElement*> &Tritinst::getSymbolicElements()
{
  return this->elements;
}

