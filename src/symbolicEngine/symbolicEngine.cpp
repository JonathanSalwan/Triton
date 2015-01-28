
#include "SymbolicEngine.h"
#include "registers.h"


SymbolicEngine::SymbolicEngine()
{
  /* Init all symbolic registers/flags to -1 (init state) */
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

  /* Init the number of symbolic variable used */
  this->numberOfSymVar = 0;
}


SymbolicEngine::~SymbolicEngine()
{
  std::vector<symbolicElement *>::iterator it = this->symbolicVector.begin();

  for (; it != this->symbolicVector.end(); ++it) {
    symbolicElement *tmp = *it;
    delete tmp;
    tmp = NULL;
  }

}


/* Returns the reference memory if it's referenced otherwise returns -1 */
int32_t SymbolicEngine::isMemoryReference(uint64_t addr)
{
  std::map<uint64_t, uint64_t>::iterator it;
  if ((it = this->memoryReference.find(addr)) != this->memoryReference.end())
    return it->second;
  return -1;
}

/* Get an unique ID. 
 * Mainly used when a new symbolic element is created */
uint64_t SymbolicEngine::getUniqueID()
{
  return this->uniqueID++;
}

/* Create a new symbolic element */
symbolicElement *SymbolicEngine::newSymbolicElement(std::stringstream &src)
{
  std::stringstream dst;
  uint64_t          id;

  id = this->getUniqueID();

  dst << "#" << std::dec << id;

  symbolicElement *elem = new symbolicElement(dst, src, id);

  this->symbolicVector.push_back(elem);

  return elem;
}

/* Get the symbolic element pointer from a symbolic ID */
symbolicElement *SymbolicEngine::getElementFromId(uint64_t id)
{
  try {
    return this->symbolicVector[id];
  }
  catch (std::out_of_range& oor) {
    return NULL;
  }
}

/* Returns the list of the symbolic variables declared in the trace */
std::string SymbolicEngine::getSmt2LibVarsDecl()
{
  std::list<std::string>::iterator i;
  std::stringstream stream;

  for(i = this->smt2libVarDeclList.begin(); i != this->smt2libVarDeclList.end(); i++)
    stream << *i;

  return stream.str();
}

/* Returns an unique ID for symbolic variable
 * Mainly used when a symbolic variable is created */
uint64_t SymbolicEngine::getUniqueSymVarID()
{
  return this->numberOfSymVar++;
}

/* Assigns a memory address to a symbolic variable
 * Mainly used to know where come from a symbolic variable */
void SymbolicEngine::addSymVarMemoryReference(uint64_t mem, uint64_t symVarID)
{
  this->symVarMemoryReference.insert(std::make_pair(symVarID, mem));
}

/* Add a new symbolic variable */
void SymbolicEngine::addSmt2LibVarDecl(uint64_t symVarID, uint64_t readSize)
{
  this->smt2libVarDeclList.push_front(smt2lib_declare(symVarID, readSize));
}

/* Add and assign a new memory reference */
void SymbolicEngine::addMemoryReference(uint64_t mem, uint64_t id)
{
  this->memoryReference[mem] = id;
}

