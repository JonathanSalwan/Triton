
#include "TaintEngine.h"
#include "registers.h"

TaintEngine::TaintEngine()
{
  this->taintedReg[ID_RAX] = (uint64_t)0;
  this->taintedReg[ID_RBX] = (uint64_t)0;
  this->taintedReg[ID_RCX] = (uint64_t)0;
  this->taintedReg[ID_RDX] = (uint64_t)0;
  this->taintedReg[ID_RDI] = (uint64_t)0;
  this->taintedReg[ID_RSI] = (uint64_t)0;
  this->taintedReg[ID_RBP] = (uint64_t)0;
  this->taintedReg[ID_RSP] = (uint64_t)0;
  this->taintedReg[ID_R8]  = (uint64_t)0;
  this->taintedReg[ID_R9]  = (uint64_t)0;
  this->taintedReg[ID_R10] = (uint64_t)0;
  this->taintedReg[ID_R11] = (uint64_t)0;
  this->taintedReg[ID_R12] = (uint64_t)0;
  this->taintedReg[ID_R13] = (uint64_t)0;
  this->taintedReg[ID_R14] = (uint64_t)0;
  this->taintedReg[ID_R15] = (uint64_t)0;

}


TaintEngine::~TaintEngine()
{
}


bool TaintEngine::isMemoryTainted(uint64_t addr)
{
  std::list<uint64_t>::iterator i;
  for(i = this->taintedAddresses.begin(); i != this->taintedAddresses.end(); i++){
    if (addr == *i)
      return true;
  }
  return false;
}


bool TaintEngine::isRegTainted(uint64_t regID)
{
  if (this->taintedReg[regID] == TAINTED)
    return true;
  return false;
}


uint64_t TaintEngine::getRegStatus(uint64_t regID)
{
  return this->taintedReg[regID];
}


void TaintEngine::taintReg(uint64_t regID)
{
  this->taintedReg[regID] = TAINTED;
}


void TaintEngine::untaintReg(uint64_t regID)
{
  this->taintedReg[regID] = !TAINTED;
}


void TaintEngine::addAddress(uint64_t addr)
{
  this->taintedAddresses.push_front(addr);
}

void TaintEngine::removeAddress(uint64_t addr)
{
  this->taintedAddresses.remove(addr);
}

