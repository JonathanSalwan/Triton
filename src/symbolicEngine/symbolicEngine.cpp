
#include <SymbolicEngine.h>
#include <Registers.h>




SymbolicEngine::SymbolicEngine()
{
  /* Init all symbolic registers/flags to UNSET (init state) */
  for (uint64_t i = 0; i < ID_LAST_ITEM; i++)
    this->symbolicReg[i] = UNSET;
  this->uniqueID = 0;
}


void SymbolicEngine::init(const SymbolicEngine &other)
{
  for (uint64_t i = 0; i < ID_LAST_ITEM; i++)
    this->symbolicReg[i] = other.symbolicReg[i];

  this->uniqueID                      = other.uniqueID;
  this->memoryReference               = other.memoryReference;
  this->pathConstaints                = other.pathConstaints;
  this->symbolicExpressions           = other.symbolicExpressions;
  this->symbolicVariables             = other.symbolicVariables;
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
  std::vector<SymbolicElement *>::iterator it = this->symbolicExpressions.begin();

  for (; it != this->symbolicExpressions.end(); ++it) {
    SymbolicElement *tmp = *it;
    delete tmp;
    tmp = nullptr;
  }
}


/*
 * Concretize a register. If the register is setup at UNSETthe next assignment
 * will be over the concretization. This method must be called before symbolic
 * processing.
 */
void SymbolicEngine::concretizeReg(uint64_t regID) {
  if (regID >= ID_LAST_ITEM)
    return ;
  this->symbolicReg[regID] = UNSET;
}


/*
 * Concretize a memory. If the memory is not found into the map, the next
 * assignment will be over the concretization. This method must be called
 * before symbolic processing.
 */
void SymbolicEngine::concretizeMem(uint64_t mem)
{
  this->memoryReference.erase(mem);
}


/* Returns the reference memory if it's referenced otherwise returns UNSET */
uint64_t SymbolicEngine::getMemSymbolicID(uint64_t addr)
{
  std::map<uint64_t, uint64_t>::iterator it;
  if ((it = this->memoryReference.find(addr)) != this->memoryReference.end())
    return it->second;
  return UNSET;
}

/* Returns the symbolic variable otherwise returns nullptr */
SymbolicVariable *SymbolicEngine::getSymVar(uint64_t symVarId)
{
  if (symVarId >= this->symbolicVariables.size())
    return nullptr;
  return this->symbolicVariables[symVarId];
}


/* Returns the symbolic variable otherwise returns nullptr */
SymbolicVariable *SymbolicEngine::getSymVar(std::string symVarName)
{
  std::vector<SymbolicVariable *>::iterator it;

  for (it = this->symbolicVariables.begin(); it != this->symbolicVariables.end(); it++){
    if ((*it)->getSymVarName() == symVarName)
      return *it;
  }

  return nullptr;
}


/* Returns all symbolic variables */
std::vector<SymbolicVariable *> SymbolicEngine::getSymVars(void)
{
  return this->symbolicVariables;
}


/* Return the reg reference or UNSET */
uint64_t SymbolicEngine::getRegSymbolicID(uint64_t regID) {
  if (regID >= ID_LAST_ITEM)
    return UNSET;
  return this->symbolicReg[regID];
}

/* Create a new symbolic element */
/* Get an unique ID.
 * Mainly used when a new symbolic element is created */
uint64_t SymbolicEngine::getUniqueID()
{
  return this->uniqueID++;
}


SymbolicElement *SymbolicEngine::newSymbolicElement(std::stringstream &src)
{
  std::stringstream dst;
  uint64_t          id;

  id = this->getUniqueID();
  dst << "#" << std::dec << id;
  SymbolicElement *elem = new SymbolicElement(dst, src, id);
  this->symbolicExpressions.push_back(elem);
  return elem;
}


/* Create a new symbolic element with comment */
SymbolicElement *SymbolicEngine::newSymbolicElement(std::stringstream &src, std::string comment)
{
  std::stringstream dst;
  uint64_t          id;

  id = this->getUniqueID();
  dst << "#" << std::dec << id;
  SymbolicElement *elem = new SymbolicElement(dst, src, id, comment);
  this->symbolicExpressions.push_back(elem);
  return elem;
}


/* Get the symbolic element pointer from a symbolic ID */
SymbolicElement *SymbolicEngine::getElementFromId(uint64_t id)
{
  if (id > this->symbolicExpressions.size())
    return nullptr;
  return this->symbolicExpressions[id];
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
std::string SymbolicEngine::getVariablesDeclaration(void)
{
  std::vector<SymbolicVariable*>::iterator it;
  std::stringstream stream;

  for(it = this->symbolicVariables.begin(); it != this->symbolicVariables.end(); it++)
    stream << smt2lib::declare((*it)->getSymVarName(), (*it)->getSymVarSize());

  return stream.str();
}


/*
 * Converts an expression ID to a symbolic variable.
 * e.g:
 * #43 = (_ bv10 8)
 * convertExprToSymVar(43, 8)
 * #43 = SymVar_4
 */
uint64_t SymbolicEngine::convertExprToSymVar(uint64_t exprId, uint64_t symVarSize)
{
  SymbolicVariable   *symVar  = nullptr;
  SymbolicElement    *element = this->getElementFromId(exprId);
  std::stringstream  newExpr;

  if (element == nullptr)
    return UNSET;

  if (symVarSize != 1 && symVarSize != 2 && symVarSize != 4 && symVarSize != 8 && symVarSize != 16)
    throw std::runtime_error("SymbolicEngine::createSymVarFromExprID() - Invalid symVarSize");

  symVar = this->addSymbolicVariable(symVarSize);

  newExpr << symVar->getSymVarName();
  element->setSrcExpr(newExpr);

  return symVar->getSymVarId();
}


/* Add a new symbolic variable */
SymbolicVariable *SymbolicEngine::addSymbolicVariable(uint64_t symVarSize)
{
  uint64_t uniqueID = this->symbolicVariables.size();
  SymbolicVariable *symVar = new SymbolicVariable(uniqueID, symVarSize);

  if (symVar == nullptr)
    throw std::runtime_error("SymbolicEngine::addSymbolicVariable() - Cannot allocate a new symbolic variable");

  this->symbolicVariables.push_back(symVar);
  return symVar;
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


