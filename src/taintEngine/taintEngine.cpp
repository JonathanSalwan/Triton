
#include "TaintEngine.h"

TaintEngine::TaintEngine(){

  this->taintedReg[0]  = (uint64_t)0; /* ID_RAX */
  this->taintedReg[1]  = (uint64_t)0; /* ID_RBX */
  this->taintedReg[2]  = (uint64_t)0; /* ID_RCX */
  this->taintedReg[3]  = (uint64_t)0; /* ID_RDX */
  this->taintedReg[4]  = (uint64_t)0; /* ID_RDI */
  this->taintedReg[5]  = (uint64_t)0; /* ID_RSI */
  this->taintedReg[6]  = (uint64_t)0; /* ID_RBP */
  this->taintedReg[7]  = (uint64_t)0; /* ID_RSP */
  this->taintedReg[8]  = (uint64_t)0; /* ID_R8  */
  this->taintedReg[9]  = (uint64_t)0; /* ID_R9  */
  this->taintedReg[10] = (uint64_t)0; /* ID_R10 */
  this->taintedReg[11] = (uint64_t)0; /* ID_R11 */
  this->taintedReg[12] = (uint64_t)0; /* ID_R12 */
  this->taintedReg[13] = (uint64_t)0; /* ID_R13 */
  this->taintedReg[14] = (uint64_t)0; /* ID_R14 */
  this->taintedReg[15] = (uint64_t)0; /* ID_R15 */

}


TaintEngine::~TaintEngine(){
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

