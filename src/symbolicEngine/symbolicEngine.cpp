
#include "SymbolicEngine.h"
#include "Registers.h"




SymbolicEngine::SymbolicEngine()
{
  /* Init all symbolic registers/flags to UNSET (init state) */
  for (uint64_t i = 0; i < ID_LAST_ITEM; i++)
    this->symbolicReg[i] = UNSET;

  /* Init the number of symbolic variable used */
  this->numberOfSymVar = 0;
}


void SymbolicEngine::init(const SymbolicEngine &other)
{
  for (uint64_t i = 0; i < ID_LAST_ITEM; i++)
    this->symbolicReg[i] = other.symbolicReg[i];

  this->memoryReference               = other.memoryReference;
  this->numberOfSymVar                = other.numberOfSymVar;
  this->pathConstaints                = other.pathConstaints;
  this->symVarDeclaration             = other.symVarDeclaration;
  this->symVarMemoryReference         = other.symVarMemoryReference;
  this->symVarMemoryReferenceInverse  = other.symVarMemoryReferenceInverse;
  this->symVarSizeReference           = other.symVarSizeReference;
  this->symbolicVector                = other.symbolicVector;
  this->uniqueID                      = other.uniqueID;
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
    tmp = nullptr;
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


/* Returns the symbolic variable ID from the memory address */
uint64_t SymbolicEngine::getSymVarFromMemory(uint64_t addr)
{
  std::map<uint64_t, uint64_t>::iterator it;
  if ((it = this->symVarMemoryReference.find(addr)) != this->symVarMemoryReference.end())
    return it->second;
  return UNSET;
}


/* Returns the size of the symbolic variable otherwise returns UNSET */
uint64_t SymbolicEngine::getSymVarSize(uint64_t symVarId)
{
  std::map<uint64_t, uint64_t>::iterator it;
  if ((it = this->symVarSizeReference.find(symVarId)) != this->symVarSizeReference.end())
    return it->second;
  return UNSET;
}


/* Returns the address from the symbolic variable ID */
uint64_t SymbolicEngine::getMemoryFromSymVar(uint64_t symVar)
{
  std::map<uint64_t, uint64_t>::iterator it;
  if ((it = this->symVarMemoryReferenceInverse.find(symVar)) != this->symVarMemoryReferenceInverse.end())
    return it->second;
  return UNSET;
}


/* Return the reg reference or UNSET */
uint64_t SymbolicEngine::getRegSymbolicID(uint64_t regID) {
  if (regID >= ID_LAST_ITEM)
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


/* Create a new symbolic element with comment */
SymbolicElement *SymbolicEngine::newSymbolicElement(std::stringstream &src, std::string &comment)
{
  std::stringstream dst;
  uint64_t          id;

  id = this->getUniqueID();
  dst << "#" << std::dec << id;
  SymbolicElement *elem = new SymbolicElement(dst, src, id, comment);
  this->symbolicVector.push_back(elem);
  return elem;
}


/* Get the symbolic element pointer from a symbolic ID */
SymbolicElement *SymbolicEngine::getElementFromId(uint64_t id)
{
  if (id > this->symbolicVector.size())
    return nullptr;
  return this->symbolicVector[id];
}


/* Replace a symbolic element ID by its source expression */
std::string SymbolicEngine::replaceEq(std::string str, const std::string from, const std::string to)
{
  size_t start_pos = str.find(from);
  if(start_pos == std::string::npos)
      return nullptr;
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
  if (element == nullptr)
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


/*
 * Converts an expression ID to a symbolic variable.
 * e.g:
 * #43 = (_ bv10 8)
 * convertExprToSymVar(43, 8)
 * #43 = SymVar_4
 */
bool SymbolicEngine::convertExprToSymVar(uint64_t exprId, uint64_t symVarSize)
{
  SymbolicElement   *element = this->getElementFromId(exprId);
  std::stringstream newExpr;
  uint64_t          symVarID;

  if (element == nullptr)
    return false;

  if (symVarSize != 1 && symVarSize != 2 && symVarSize != 4 && symVarSize != 8 && symVarSize != 16)
    throw std::runtime_error("SymbolicEngine::createSymVarFromExprID() - Invalid symVarSize");

  symVarID = this->getUniqueSymVarID();
  this->addSmt2LibVarDecl(symVarID, symVarSize);

  newExpr << SYMVAR_NAME << std::dec << symVarID;
  element->setSrcExpr(newExpr);

  return true;
}

/*
 * Assigns a symbolic variable to an expression.
 * Unlike convertExprToSymVar(), this fonction doesn't
 * create a new symbolic variable.
 */
bool SymbolicEngine::assignExprToSymVar(uint64_t exprId, uint64_t symVarId)
{
  SymbolicElement   *element = this->getElementFromId(exprId);
  std::stringstream newExpr;

  if (element == nullptr)
    return false;

  if (symVarId >= this->numberOfSymVar)
    return false;

  newExpr << SYMVAR_NAME << std::dec << symVarId;
  element->setSrcExpr(newExpr);

  return true;
}


/* Assigns a memory address to a symbolic variable
 * Mainly used to know where come from a symbolic variable */
void SymbolicEngine::addSymVarMemoryReference(uint64_t mem, uint64_t symVarID)
{
  this->symVarMemoryReference.insert(std::make_pair(mem, symVarID));
  this->symVarMemoryReferenceInverse.insert(std::make_pair(symVarID, mem));
}


/* Add a new symbolic variable */
void SymbolicEngine::addSmt2LibVarDecl(uint64_t symVarID, uint64_t size)
{
  this->symVarSizeReference.insert(std::make_pair(symVarID, size));
  this->symVarDeclaration.push_front(smt2lib::declare(symVarID, size));
}


/* Add and assign a new memory reference */
void SymbolicEngine::addMemoryReference(uint64_t mem, uint64_t id)
{
  this->memoryReference[mem] = id;
}


/* The a path constraint in the PC list */
void SymbolicEngine::addPathConstraint(uint64_t exprId)
{
  this->pathConstaints.push_back(exprId);
}


/* Returns the path constrains list */
std::list<uint64_t> SymbolicEngine::getPathConstraints(void)
{
  return this->pathConstaints;
}


