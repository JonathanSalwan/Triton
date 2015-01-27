
#include "SymbolicEngine.h"


SymbolicEngine::SymbolicEngine()
{
 this->symbolicReg[0]  = (uint64_t)-1; /* ID_RAX   */
 this->symbolicReg[1]  = (uint64_t)-1; /* ID_RBX   */
 this->symbolicReg[2]  = (uint64_t)-1; /* ID_RCX   */
 this->symbolicReg[3]  = (uint64_t)-1; /* ID_RDX   */
 this->symbolicReg[4]  = (uint64_t)-1; /* ID_RDI   */
 this->symbolicReg[5]  = (uint64_t)-1; /* ID_RSI   */
 this->symbolicReg[6]  = (uint64_t)-1; /* ID_RBP   */
 this->symbolicReg[7]  = (uint64_t)-1; /* ID_RSP   */
 this->symbolicReg[8]  = (uint64_t)-1; /* ID_R8    */
 this->symbolicReg[9]  = (uint64_t)-1; /* ID_R9    */
 this->symbolicReg[10] = (uint64_t)-1; /* ID_R10   */
 this->symbolicReg[11] = (uint64_t)-1; /* ID_R11   */
 this->symbolicReg[12] = (uint64_t)-1; /* ID_R12   */
 this->symbolicReg[13] = (uint64_t)-1; /* ID_R13   */
 this->symbolicReg[14] = (uint64_t)-1; /* ID_R14   */
 this->symbolicReg[15] = (uint64_t)-1; /* ID_R15   */
 this->symbolicReg[16] = (uint64_t)-1; /* ID_CF    */
 this->symbolicReg[17] = (uint64_t)-1; /* ID_PF    */
 this->symbolicReg[18] = (uint64_t)-1; /* ID_AF    */
 this->symbolicReg[19] = (uint64_t)-1; /* ID_ZF    */
 this->symbolicReg[20] = (uint64_t)-1; /* ID_SF    */
 this->symbolicReg[21] = (uint64_t)-1; /* ID_TF    */
 this->symbolicReg[22] = (uint64_t)-1; /* ID_IF    */
 this->symbolicReg[23] = (uint64_t)-1; /* ID_DF    */
 this->symbolicReg[24] = (uint64_t)-1; /* ID_OF    */

 this->numberOfSymVar = 0;
}


SymbolicEngine::~SymbolicEngine()
{
}


int32_t SymbolicEngine::isMemoryReference(uint64_t addr)
{
  std::list< std::pair<uint64_t, uint64_t> >::iterator i;

  for(i = this->memoryReference.begin(); i != this->memoryReference.end(); i++){
    if (i->first == addr)
      return i->second;
  }
  return -1;
}


uint64_t SymbolicEngine::getUniqueID()
{
  return this->uniqueID++;
}


symbolicElement *SymbolicEngine::newSymbolicElement(std::stringstream &src)
{
  std::stringstream dst;
  uint64_t          id;

  id = this->getUniqueID();

  dst << "#" << std::dec << id;

  symbolicElement *elem = new symbolicElement(dst, src, id);

  this->symbolicList.push_front(elem);

  return elem;
}


void SymbolicEngine::setSymbolicReg(uint64_t reg, uint64_t referenceID)
{
  this->symbolicReg[reg] = referenceID;
}


symbolicElement *SymbolicEngine::getElementFromId(uint64_t id)
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


uint64_t SymbolicEngine::getUniqueSymVarID()
{
  return this->numberOfSymVar++;
}


void SymbolicEngine::addSymVarMemoryReference(uint64_t mem, uint64_t symVarID)
{
  this->symVarMemoryReference.push_front(std::make_pair(mem, symVarID));
}


void SymbolicEngine::addSmt2LibVarDecl(uint64_t symVarID, uint64_t readSize)
{
  this->smt2libVarDeclList.push_front(smt2lib_declare(symVarID, readSize));
}

void SymbolicEngine::addMemoryReference(uint64_t mem, uint64_t id)
{
  this->memoryReference.push_front(std::make_pair(mem, id));
}

