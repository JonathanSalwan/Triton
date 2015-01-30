#include "Trace.h"


Trace::Trace(uint64_t entry, uint64_t end)
{
  this->entryPoint = entry;
  this->endPoint = end;
}


Trace::~Trace()
{
}


uint64_t Trace::getEntryPoint() 
{
  return entryPoint;
}


uint64_t Trace::getEndPoint()
{
  return endPoint;
}

// TODO
//std::string Trace::dump()
//{
//}


void Trace::addBasicBlock(const BasicBlock &bbl)
{
  // TODO
}


// TODO
//const std::list<BasicBlock> &getForks()
//{
//}

