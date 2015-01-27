
#include "pin.H"
#include "Triton.h"


TaintEngine::TaintEngine(){

  this->taintedReg[0]  = (UINT64)0; /* ID_RAX */
  this->taintedReg[1]  = (UINT64)0; /* ID_RBX */
  this->taintedReg[2]  = (UINT64)0; /* ID_RCX */
  this->taintedReg[3]  = (UINT64)0; /* ID_RDX */
  this->taintedReg[4]  = (UINT64)0; /* ID_RDI */
  this->taintedReg[5]  = (UINT64)0; /* ID_RSI */
  this->taintedReg[6]  = (UINT64)0; /* ID_RBP */
  this->taintedReg[7]  = (UINT64)0; /* ID_RSP */
  this->taintedReg[8]  = (UINT64)0; /* ID_R8  */
  this->taintedReg[9]  = (UINT64)0; /* ID_R9  */
  this->taintedReg[10] = (UINT64)0; /* ID_R10 */
  this->taintedReg[11] = (UINT64)0; /* ID_R11 */
  this->taintedReg[12] = (UINT64)0; /* ID_R12 */
  this->taintedReg[13] = (UINT64)0; /* ID_R13 */
  this->taintedReg[14] = (UINT64)0; /* ID_R14 */
  this->taintedReg[15] = (UINT64)0; /* ID_R15 */

}


TaintEngine::~TaintEngine(){
}


bool TaintEngine::isMemoryTainted(UINT64 addr)
{
  std::list<UINT64>::iterator i;
  for(i = this->taintedAddresses.begin(); i != this->taintedAddresses.end(); i++){
    if (addr == *i)
      return true;
  }
  return false;
}


bool TaintEngine::isRegTainted(UINT64 regID)
{
  if (this->taintedReg[regID] == TAINTED)
    return true;
  return false;
}


UINT64 TaintEngine::getRegStatus(UINT64 regID)
{
  return this->taintedReg[regID];
}


VOID TaintEngine::taintReg(UINT64 regID)
{
  this->taintedReg[regID] = TAINTED;
}


VOID TaintEngine::untaintReg(UINT64 regID)
{
  this->taintedReg[regID] = !TAINTED;
}


VOID TaintEngine::addAddress(UINT64 addr)
{
  this->taintedAddresses.push_front(addr);
}

VOID TaintEngine::removeAddress(UINT64 addr)
{
  this->taintedAddresses.remove(addr);
}
