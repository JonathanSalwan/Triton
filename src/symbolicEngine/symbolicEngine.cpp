
#include "SymbolicEngine.h"
#include "Registers.h"


SymbolicEngine::SymbolicEngine()
{
  /* Init all symbolic registers/flags to UNSET (init state) */
  this->symbolicReg[ID_RAX] = UNSET;
  this->symbolicReg[ID_RBX] = UNSET;
  this->symbolicReg[ID_RCX] = UNSET;
  this->symbolicReg[ID_RDX] = UNSET;
  this->symbolicReg[ID_RDI] = UNSET;
  this->symbolicReg[ID_RSI] = UNSET;
  this->symbolicReg[ID_RBP] = UNSET;
  this->symbolicReg[ID_RSP] = UNSET;
  this->symbolicReg[ID_R8]  = UNSET;
  this->symbolicReg[ID_R9]  = UNSET;
  this->symbolicReg[ID_R10] = UNSET;
  this->symbolicReg[ID_R11] = UNSET;
  this->symbolicReg[ID_R12] = UNSET;
  this->symbolicReg[ID_R13] = UNSET;
  this->symbolicReg[ID_R14] = UNSET;
  this->symbolicReg[ID_R15] = UNSET;
  this->symbolicReg[ID_CF]  = UNSET;
  this->symbolicReg[ID_PF]  = UNSET;
  this->symbolicReg[ID_AF]  = UNSET;
  this->symbolicReg[ID_ZF]  = UNSET;
  this->symbolicReg[ID_SF]  = UNSET;
  this->symbolicReg[ID_TF]  = UNSET;
  this->symbolicReg[ID_IF]  = UNSET;
  this->symbolicReg[ID_DF]  = UNSET;
  this->symbolicReg[ID_OF]  = UNSET;

  /* Init the number of symbolic variable used */
  this->numberOfSymVar = 0;
}

void SymbolicEngine::init(const SymbolicEngine &other)
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


SymbolicEngine::SymbolicEngine(const SymbolicEngine &copy)
{
  this->init(copy);
}


void SymbolicEngine::operator=(const SymbolicEngine &other)
{
  this->init(other);
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
uint64_t SymbolicEngine::isMemoryReference(uint64_t addr)
{
  std::map<uint64_t, uint64_t>::iterator it;
  if ((it = this->memoryReference.find(addr)) != this->memoryReference.end())
    return it->second;
  return UNSET;
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

