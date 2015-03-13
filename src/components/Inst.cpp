#include "Inst.h"


Inst::Inst(uint64_t threadId, uint64_t address, const std::string &insDis):
  threadId(threadId), address(address), disassembly(insDis)
{
}


Inst::~Inst()
{
}


/* Returns the instruction assembly */
const std::string &Inst::getDisassembly(void)
{
  return this->disassembly;
}


/* Returns the instruction address */
uint64_t Inst::getAddress(void)
{
  return this->address;
}


/* Returns the thread ID of the instruction */
uint64_t Inst::getThreadId(void)
{
  return this->threadId;
}

/* Adds a new symbolic element */
void Inst::addElement(SymbolicElement *se)
{
  this->elements.push_back(se);
}


/* Returns the elements list */
const std::list<SymbolicElement*> &Inst::getSymbolicElements(void)
{
  return this->elements;
}


/* Returns the number of elements */
size_t Inst::numberOfElements(void)
{
  return this->elements.size();
}

