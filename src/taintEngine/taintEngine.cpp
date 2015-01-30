
#include "TaintEngine.h"
#include "Registers.h"



TaintEngine::TaintEngine()
{
  /* Init all registers to not tainted */
  this->taintedReg[ID_RAX] = (uint64_t)!TAINTED;
  this->taintedReg[ID_RBX] = (uint64_t)!TAINTED;
  this->taintedReg[ID_RCX] = (uint64_t)!TAINTED;
  this->taintedReg[ID_RDX] = (uint64_t)!TAINTED;
  this->taintedReg[ID_RDI] = (uint64_t)!TAINTED;
  this->taintedReg[ID_RSI] = (uint64_t)!TAINTED;
  this->taintedReg[ID_RBP] = (uint64_t)!TAINTED;
  this->taintedReg[ID_RSP] = (uint64_t)!TAINTED;
  this->taintedReg[ID_R8]  = (uint64_t)!TAINTED;
  this->taintedReg[ID_R9]  = (uint64_t)!TAINTED;
  this->taintedReg[ID_R10] = (uint64_t)!TAINTED;
  this->taintedReg[ID_R11] = (uint64_t)!TAINTED;
  this->taintedReg[ID_R12] = (uint64_t)!TAINTED;
  this->taintedReg[ID_R13] = (uint64_t)!TAINTED;
  this->taintedReg[ID_R14] = (uint64_t)!TAINTED;
  this->taintedReg[ID_R15] = (uint64_t)!TAINTED;
}


TaintEngine::TaintEngine(const TaintEngine &copy)
{
  this->taintedReg[ID_RAX] = copy.taintedReg[ID_RAX];
  this->taintedReg[ID_RBX] = copy.taintedReg[ID_RBX];
  this->taintedReg[ID_RCX] = copy.taintedReg[ID_RCX];
  this->taintedReg[ID_RDX] = copy.taintedReg[ID_RDX];
  this->taintedReg[ID_RDI] = copy.taintedReg[ID_RDI];
  this->taintedReg[ID_RSI] = copy.taintedReg[ID_RSI];
  this->taintedReg[ID_RBP] = copy.taintedReg[ID_RBP];
  this->taintedReg[ID_RSP] = copy.taintedReg[ID_RSP];
  this->taintedReg[ID_R8]  = copy.taintedReg[ID_R8];
  this->taintedReg[ID_R9]  = copy.taintedReg[ID_R9];
  this->taintedReg[ID_R10] = copy.taintedReg[ID_R10];
  this->taintedReg[ID_R11] = copy.taintedReg[ID_R11];
  this->taintedReg[ID_R12] = copy.taintedReg[ID_R12];
  this->taintedReg[ID_R13] = copy.taintedReg[ID_R13];
  this->taintedReg[ID_R14] = copy.taintedReg[ID_R14];
  this->taintedReg[ID_R15] = copy.taintedReg[ID_R15];

  this->taintedAddresses = copy.taintedAddresses;
}


TaintEngine::~TaintEngine()
{
}


void TaintEngine::operator=(const TaintEngine &other)
{
  this->taintedReg[ID_RAX] = other.taintedReg[ID_RAX];
  this->taintedReg[ID_RBX] = other.taintedReg[ID_RBX];
  this->taintedReg[ID_RCX] = other.taintedReg[ID_RCX];
  this->taintedReg[ID_RDX] = other.taintedReg[ID_RDX];
  this->taintedReg[ID_RDI] = other.taintedReg[ID_RDI];
  this->taintedReg[ID_RSI] = other.taintedReg[ID_RSI];
  this->taintedReg[ID_RBP] = other.taintedReg[ID_RBP];
  this->taintedReg[ID_RSP] = other.taintedReg[ID_RSP];
  this->taintedReg[ID_R8]  = other.taintedReg[ID_R8];
  this->taintedReg[ID_R9]  = other.taintedReg[ID_R9];
  this->taintedReg[ID_R10] = other.taintedReg[ID_R10];
  this->taintedReg[ID_R11] = other.taintedReg[ID_R11];
  this->taintedReg[ID_R12] = other.taintedReg[ID_R12];
  this->taintedReg[ID_R13] = other.taintedReg[ID_R13];
  this->taintedReg[ID_R14] = other.taintedReg[ID_R14];
  this->taintedReg[ID_R15] = other.taintedReg[ID_R15];

  this->taintedAddresses = other.taintedAddresses;
}


/* Returns true of false if the memory address is currently tainted */
bool TaintEngine::isMemoryTainted(uint64_t addr)
{
  std::list<uint64_t>::iterator i;
  for(i = this->taintedAddresses.begin(); i != this->taintedAddresses.end(); i++){
    if (addr == *i)
      return true;
  }
  return false;
}

/* Returns true of false if the register is currently tainted */
bool TaintEngine::isRegTainted(uint64_t regID)
{
  if (this->taintedReg[regID] == TAINTED)
    return true;
  return false;
}

/* Returns state (TAINTED or !TAINTED) of the register */
uint64_t TaintEngine::getRegStatus(uint64_t regID)
{
  return this->taintedReg[regID];
}

/* Tainted the register */
void TaintEngine::taintReg(uint64_t regID)
{
  this->taintedReg[regID] = TAINTED;
}


/* Untainted the register */
void TaintEngine::untaintReg(uint64_t regID)
{
  this->taintedReg[regID] = !TAINTED;
}


/* Taint the address */
void TaintEngine::taintAddress(uint64_t addr)
{
  this->taintedAddresses.push_front(addr);
}

/* Untaint the address */
void TaintEngine::untaintAddress(uint64_t addr)
{
  this->taintedAddresses.remove(addr);
}


