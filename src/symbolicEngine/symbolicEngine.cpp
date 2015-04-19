
#include "SymbolicEngine.h"
#include "Registers.h"




SymbolicEngine::SymbolicEngine()
{
  /* Init all symbolic registers/flags to UNSET (init state) */
  for (uint64_t i = 0; i < (sizeof(this->symbolicReg) / sizeof(this->symbolicReg[0])); i++){
    this->symbolicReg[i] = UNSET;
  }
  /* Init the number of symbolic variable used */
  this->numberOfSymVar = 0;
}


void SymbolicEngine::init(const SymbolicEngine &other)
{
  for (uint64_t i = 0; i < (sizeof(this->symbolicReg) / sizeof(this->symbolicReg[0])); i++){
    this->symbolicReg[i] = other.symbolicReg[i];
  }
  this->uniqueID              = other.uniqueID;
  this->numberOfSymVar        = other.numberOfSymVar;
  this->memoryReference       = other.memoryReference;
  this->symVarMemoryReference = other.symVarMemoryReference;
  this->symVarDeclaration     = other.symVarDeclaration;
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


/* Returns the reference memory if it's referenced otherwise returns UNSET */
uint64_t SymbolicEngine::getMemSymbolicID(uint64_t addr)
{
  std::map<uint64_t, uint64_t>::iterator it;
  if ((it = this->memoryReference.find(addr)) != this->memoryReference.end())
    return it->second;
  return UNSET;
}


/* Returns the symbolic var ID if it's referenced otherwise returns UNSET */
uint64_t SymbolicEngine::isSymVarMemory(uint64_t addr)
{
  std::map<uint64_t, uint64_t>::iterator it;
  if ((it = this->symVarMemoryReference.find(addr)) != this->symVarMemoryReference.end())
    return it->second;
  return UNSET;
}


/* Return the reg reference or UNSET */
uint64_t SymbolicEngine::getRegSymbolicID(uint64_t regID) {
  if (regID >= (sizeof(this->symbolicReg) / sizeof(this->symbolicReg[0])))
    return UNSET;
  return this->symbolicReg[regID];
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
  if (id > this->symbolicVector.size())
    return NULL;
  return this->symbolicVector[id];
}


/* Replace a symbolic element ID by its source expression */
std::string SymbolicEngine::replaceEq(std::string str, const std::string from, const std::string to)
{
  size_t start_pos = str.find(from);
  if(start_pos == std::string::npos)
      return NULL;
  str.replace(start_pos, from.length(), to);
  return str;
}


std::string SymbolicEngine::deepReplace(std::stringstream &formula)
{
  int               value;
  size_t            found;
  std::stringstream from;
  std::stringstream to;

  found = formula.str().find("#") + 1;
  std::string subs = formula.str().substr(found, std::string::npos);
  value = atoi(subs.c_str());
  from << "#" << value;

  to.str(this->getElementFromId(value)->getSource()->str());

  formula.str(this->replaceEq(formula.str(), from.str(), to.str()));
  return formula.str();
}


/* Returns the symbolic expression backtracked from an ID. */
std::string SymbolicEngine::getBacktrackedExpressionFromId(uint64_t id)
{
  SymbolicElement   *element;
  std::stringstream formula;

  element = this->getElementFromId(id);
  if (element == NULL)
    return "";

  formula.str(element->getSource()->str());
  while (formula.str().find("#") != std::string::npos)
    formula.str(this->deepReplace(formula));

  return formula.str();
}


/* Returns the list of the symbolic variables declared in the trace */
std::string SymbolicEngine::getSmt2LibVarsDecl()
{
  std::list<std::string>::iterator i;
  std::stringstream stream;

  for(i = this->symVarDeclaration.begin(); i != this->symVarDeclaration.end(); i++)
    stream << *i;

  return stream.str();
}


/* Returns an unique ID for symbolic variable
 * Mainly used when a symbolic variable is created */
uint64_t SymbolicEngine::getUniqueSymVarID()
{
  return this->numberOfSymVar++;
}


/* Convert an expression ID to a symbolic variable */
/* e.g:
 * #43 = (_ bv10 8)
 * convertExprToSymVar(43, 8)
 * #43 = SymVar_4
 */
bool SymbolicEngine::convertExprToSymVar(uint64_t exprId, uint64_t symVarSize)
{
  SymbolicElement   *element = this->getElementFromId(exprId);
  std::stringstream newExpr;
  uint64_t          symVarID;

  if (element == NULL)
    return false;

  if (symVarSize != 1 && symVarSize != 2 && symVarSize != 4 && symVarSize != 8)
    throw std::runtime_error("SymbolicEngine::createSymVarFromExprID() - Invalid symVarSize");

  symVarID = this->getUniqueSymVarID();
  this->addSmt2LibVarDecl(symVarID, symVarSize);

  newExpr << "SymVar_" << std::dec << symVarID;
  element->setSrcExpr(newExpr);
  return true;
}


/* Assigns a memory address to a symbolic variable
 * Mainly used to know where come from a symbolic variable */
void SymbolicEngine::addSymVarMemoryReference(uint64_t mem, uint64_t symVarID)
{
  this->symVarMemoryReference.insert(std::make_pair(mem, symVarID));
}


/* Add a new symbolic variable */
void SymbolicEngine::addSmt2LibVarDecl(uint64_t symVarID, uint64_t readSize)
{
  this->symVarDeclaration.push_front(smt2lib::declare(symVarID, readSize));
}


/* Add and assign a new memory reference */
void SymbolicEngine::addMemoryReference(uint64_t mem, uint64_t id)
{
  this->memoryReference[mem] = id;
}

