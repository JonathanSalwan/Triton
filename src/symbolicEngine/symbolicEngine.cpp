
#include "SymbolicEngine.h"
#include "Registers.h"


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


SymbolicEngine::SymbolicEngine(const SymbolicEngine &copy)
{
  this->symbolicReg[ID_RAX] = copy.symbolicReg[ID_RAX];
  this->symbolicReg[ID_RBX] = copy.symbolicReg[ID_RBX];
  this->symbolicReg[ID_RCX] = copy.symbolicReg[ID_RCX];
  this->symbolicReg[ID_RDX] = copy.symbolicReg[ID_RDX];
  this->symbolicReg[ID_RDI] = copy.symbolicReg[ID_RDI];
  this->symbolicReg[ID_RSI] = copy.symbolicReg[ID_RSI];
  this->symbolicReg[ID_RBP] = copy.symbolicReg[ID_RBP];
  this->symbolicReg[ID_RSP] = copy.symbolicReg[ID_RSP];
  this->symbolicReg[ID_R8]  = copy.symbolicReg[ID_R8];
  this->symbolicReg[ID_R9]  = copy.symbolicReg[ID_R9];
  this->symbolicReg[ID_R10] = copy.symbolicReg[ID_R10];
  this->symbolicReg[ID_R11] = copy.symbolicReg[ID_R11];
  this->symbolicReg[ID_R12] = copy.symbolicReg[ID_R12];
  this->symbolicReg[ID_R13] = copy.symbolicReg[ID_R13];
  this->symbolicReg[ID_R14] = copy.symbolicReg[ID_R14];
  this->symbolicReg[ID_R15] = copy.symbolicReg[ID_R15];
  this->symbolicReg[ID_CF]  = copy.symbolicReg[ID_CF];
  this->symbolicReg[ID_PF]  = copy.symbolicReg[ID_PF];
  this->symbolicReg[ID_AF]  = copy.symbolicReg[ID_AF];
  this->symbolicReg[ID_ZF]  = copy.symbolicReg[ID_ZF];
  this->symbolicReg[ID_SF]  = copy.symbolicReg[ID_SF];
  this->symbolicReg[ID_TF]  = copy.symbolicReg[ID_TF];
  this->symbolicReg[ID_IF]  = copy.symbolicReg[ID_IF];
  this->symbolicReg[ID_DF]  = copy.symbolicReg[ID_DF];
  this->symbolicReg[ID_OF]  = copy.symbolicReg[ID_OF];

  this->uniqueID              = copy.uniqueID;
  this->numberOfSymVar        = copy.numberOfSymVar;
  this->memoryReference       = copy.memoryReference;
  this->symVarMemoryReference = copy.symVarMemoryReference;
  this->smt2libVarDeclList    = copy.smt2libVarDeclList;
  this->symbolicVector        = copy.symbolicVector;
}


void SymbolicEngine::operator=(const SymbolicEngine &other)
{
  this->symbolicReg[ID_RAX] = other.symbolicReg[ID_RAX];
  this->symbolicReg[ID_RBX] = other.symbolicReg[ID_RBX];
  this->symbolicReg[ID_RCX] = other.symbolicReg[ID_RCX];
  this->symbolicReg[ID_RDX] = other.symbolicReg[ID_RDX];
  this->symbolicReg[ID_RDI] = other.symbolicReg[ID_RDI];
  this->symbolicReg[ID_RSI] = other.symbolicReg[ID_RSI];
  this->symbolicReg[ID_RBP] = other.symbolicReg[ID_RBP];
  this->symbolicReg[ID_RSP] = other.symbolicReg[ID_RSP];
  this->symbolicReg[ID_R8]  = other.symbolicReg[ID_R8];
  this->symbolicReg[ID_R9]  = other.symbolicReg[ID_R9];
  this->symbolicReg[ID_R10] = other.symbolicReg[ID_R10];
  this->symbolicReg[ID_R11] = other.symbolicReg[ID_R11];
  this->symbolicReg[ID_R12] = other.symbolicReg[ID_R12];
  this->symbolicReg[ID_R13] = other.symbolicReg[ID_R13];
  this->symbolicReg[ID_R14] = other.symbolicReg[ID_R14];
  this->symbolicReg[ID_R15] = other.symbolicReg[ID_R15];
  this->symbolicReg[ID_CF]  = other.symbolicReg[ID_CF];
  this->symbolicReg[ID_PF]  = other.symbolicReg[ID_PF];
  this->symbolicReg[ID_AF]  = other.symbolicReg[ID_AF];
  this->symbolicReg[ID_ZF]  = other.symbolicReg[ID_ZF];
  this->symbolicReg[ID_SF]  = other.symbolicReg[ID_SF];
  this->symbolicReg[ID_TF]  = other.symbolicReg[ID_TF];
  this->symbolicReg[ID_IF]  = other.symbolicReg[ID_IF];
  this->symbolicReg[ID_DF]  = other.symbolicReg[ID_DF];
  this->symbolicReg[ID_OF]  = other.symbolicReg[ID_OF];

  this->uniqueID              = other.uniqueID;
  this->numberOfSymVar        = other.numberOfSymVar;
  this->memoryReference       = other.memoryReference;
  this->symVarMemoryReference = other.symVarMemoryReference;
  this->smt2libVarDeclList    = other.smt2libVarDeclList;
  this->symbolicVector        = other.symbolicVector;
}


SymbolicEngine::~SymbolicEngine()
{
  std::vector<SymbolicElement *>::iterator it = this->symbolicVector.begin();

  for (; it != this->symbolicVector.end(); ++it) {
    SymbolicElement *tmp = *it;
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
SymbolicElement *SymbolicEngine::newSymbolicElement(std::stringstream &src)
{
  std::stringstream dst;
  uint64_t          id;

  id = this->getUniqueID();

  dst << "#" << std::dec << id;

  SymbolicElement *elem = new SymbolicElement(dst, src, id);

  this->symbolicVector.push_back(elem);

  return elem;
}

/* Get the symbolic element pointer from a symbolic ID */
SymbolicElement *SymbolicEngine::getElementFromId(uint64_t id)
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

