
#include "SymbolicEngine.h"
#include "registers.h"


SymbolicEngine::SymbolicEngine()
{
 this->symbolicReg[ID_RAX] = (uint64_t)-1;
 this->symbolicReg[ID_RBX] = (uint64_t)-1;
 this->symbolicReg[ID_RCX] = (uint64_t)-1;
 this->symbolicReg[ID_RDX] = (uint64_t)-1;
 this->symbolicReg[ID_RDI] = (uint64_t)-1;
 this->symbolicReg[ID_RSI] = (uint64_t)-1;
 this->symbolicReg[ID_RBP] = (uint64_t)-1;
 this->symbolicReg[ID_RSP] = (uint64_t)-1;
 this->symbolicReg[ID_R8]  = (uint64_t)-1;
 this->symbolicReg[ID_R9]  = (uint64_t)-1;
 this->symbolicReg[ID_R10] = (uint64_t)-1;
 this->symbolicReg[ID_R11] = (uint64_t)-1;
 this->symbolicReg[ID_R12] = (uint64_t)-1;
 this->symbolicReg[ID_R13] = (uint64_t)-1;
 this->symbolicReg[ID_R14] = (uint64_t)-1;
 this->symbolicReg[ID_R15] = (uint64_t)-1;
 this->symbolicReg[ID_CF]  = (uint64_t)-1;
 this->symbolicReg[ID_PF]  = (uint64_t)-1;
 this->symbolicReg[ID_AF]  = (uint64_t)-1;
 this->symbolicReg[ID_ZF]  = (uint64_t)-1;
 this->symbolicReg[ID_SF]  = (uint64_t)-1;
 this->symbolicReg[ID_TF]  = (uint64_t)-1;
 this->symbolicReg[ID_IF]  = (uint64_t)-1;
 this->symbolicReg[ID_DF]  = (uint64_t)-1;
 this->symbolicReg[ID_OF]  = (uint64_t)-1;

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

