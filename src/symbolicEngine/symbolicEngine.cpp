
#include "pin.H"
#include "Triton.h"



SymbolicEngine::SymbolicEngine()
{
 this->symbolicReg[0]  = (UINT64)-1; /* ID_RAX   */
 this->symbolicReg[1]  = (UINT64)-1; /* ID_RBX   */
 this->symbolicReg[2]  = (UINT64)-1; /* ID_RCX   */
 this->symbolicReg[3]  = (UINT64)-1; /* ID_RDX   */
 this->symbolicReg[4]  = (UINT64)-1; /* ID_RDI   */
 this->symbolicReg[5]  = (UINT64)-1; /* ID_RSI   */
 this->symbolicReg[6]  = (UINT64)-1; /* ID_RBP   */
 this->symbolicReg[7]  = (UINT64)-1; /* ID_RSP   */
 this->symbolicReg[8]  = (UINT64)-1; /* ID_R8    */
 this->symbolicReg[9]  = (UINT64)-1; /* ID_R9    */
 this->symbolicReg[10] = (UINT64)-1; /* ID_R10   */
 this->symbolicReg[11] = (UINT64)-1; /* ID_R11   */
 this->symbolicReg[12] = (UINT64)-1; /* ID_R12   */
 this->symbolicReg[13] = (UINT64)-1; /* ID_R13   */
 this->symbolicReg[14] = (UINT64)-1; /* ID_R14   */
 this->symbolicReg[15] = (UINT64)-1; /* ID_R15   */
 this->symbolicReg[16] = (UINT64)-1; /* ID_CF    */
 this->symbolicReg[17] = (UINT64)-1; /* ID_PF    */
 this->symbolicReg[18] = (UINT64)-1; /* ID_AF    */
 this->symbolicReg[19] = (UINT64)-1; /* ID_ZF    */
 this->symbolicReg[20] = (UINT64)-1; /* ID_SF    */
 this->symbolicReg[21] = (UINT64)-1; /* ID_TF    */
 this->symbolicReg[22] = (UINT64)-1; /* ID_IF    */
 this->symbolicReg[23] = (UINT64)-1; /* ID_DF    */
 this->symbolicReg[24] = (UINT64)-1; /* ID_OF    */

 this->numberOfSymVar = 0;
}


SymbolicEngine::~SymbolicEngine()
{
}


INT32 SymbolicEngine::isMemoryReference(UINT64 addr)
{
  std::list< std::pair<UINT64, UINT64> >::iterator i;

  for(i = this->memoryReference.begin(); i != this->memoryReference.end(); i++){
    if (i->first == addr)
      return i->second;
  }
  return -1;
}


UINT64 SymbolicEngine::getUniqueID()
{
  return this->uniqueID++;
}


symbolicElement *SymbolicEngine::newSymbolicElement(std::stringstream &src)
{
  std::stringstream dst;
  UINT64            id;
  
  id = this->getUniqueID();

  dst << "#" << std::dec << id;

  symbolicElement *elem = new symbolicElement(dst, src, id);

  this->symbolicList.push_front(elem);

  return elem;
}


VOID SymbolicEngine::setSymbolicReg(UINT64 reg, UINT64 referenceID)
{
  this->symbolicReg[reg] = referenceID;
}


symbolicElement *SymbolicEngine::getElementFromId(UINT64 id)
{
  std::list<symbolicElement *>::iterator i;

  for(i = this->symbolicList.begin(); i != this->symbolicList.end(); i++){
    if ((*i)->getID() == id)
      return *i;
  }
  return NULL;
}

std::string SymbolicEngine::getSmt2LibVarsDecl()
{
  std::list<std::string>::iterator i;
  std::stringstream stream;

  for(i = this->smt2libVarDeclList.begin(); i != this->smt2libVarDeclList.end(); i++)
    stream << *i;

  return stream.str();
}


UINT64 SymbolicEngine::getUniqueSymVarID()
{
  return this->numberOfSymVar++;
}


VOID SymbolicEngine::addSymVarMemoryReference(UINT64 mem, UINT64 symVarID)
{
  this->symVarMemoryReference.push_front(make_pair(mem, symVarID));
}


VOID SymbolicEngine::addSmt2LibVarDecl(UINT64 symVarID, UINT64 readSize)
{
  this->smt2libVarDeclList.push_front(smt2lib_declare(symVarID, readSize));
}

VOID SymbolicEngine::addMemoryReference(UINT64 mem, UINT64 id)
{
  this->memoryReference.push_front(make_pair(mem, id));
}

