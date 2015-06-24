
#include <SymbolicEngine.h>
#include <Registers.h>




SymbolicEngine::SymbolicEngine()
{
  /* Init all symbolic registers/flags to UNSET (init state) */
  for (uint64 i = 0; i < ID_LAST_ITEM; i++)
    this->symbolicReg[i] = UNSET;
  this->uniqueID = 0;
}


void SymbolicEngine::init(const SymbolicEngine &other)
{
  for (uint64 i = 0; i < ID_LAST_ITEM; i++)
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
  std::vector<SymbolicElement *>::iterator it1 = this->symbolicExpressions.begin();
  std::vector<SymbolicVariable *>::iterator it2 = this->symbolicVariables.begin();

  /* Delete all symbolic expressions */
  for (; it1 != this->symbolicExpressions.end(); ++it1) {
    SymbolicElement *tmp = *it1;
    delete tmp;
    tmp = nullptr;
  }

  /* Delete all symbolic variables */
  for (; it2 != this->symbolicVariables.end(); ++it2) {
    SymbolicVariable *tmp = *it2;
    delete tmp;
    tmp = nullptr;
  }
}


/*
 * Concretize a register. If the register is setup at UNSETthe next assignment
 * will be over the concretization. This method must be called before symbolic
 * processing.
 */
void SymbolicEngine::concretizeReg(uint64 regID) {
  if (regID >= ID_LAST_ITEM)
    return ;
  this->symbolicReg[regID] = UNSET;
}


/*
 * Concretize a memory. If the memory is not found into the map, the next
 * assignment will be over the concretization. This method must be called
 * before symbolic processing.
 */
void SymbolicEngine::concretizeMem(uint64 mem)
{
  this->memoryReference.erase(mem);
}


/* Returns the reference memory if it's referenced otherwise returns UNSET */
uint64 SymbolicEngine::getMemSymbolicID(uint64 addr)
{
  std::map<uint64, uint64>::iterator it;
  if ((it = this->memoryReference.find(addr)) != this->memoryReference.end())
    return it->second;
  return UNSET;
}


/* Returns the symbolic variable otherwise returns nullptr */
SymbolicVariable *SymbolicEngine::getSymVar(uint64 symVarId)
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
uint64 SymbolicEngine::getRegSymbolicID(uint64 regID) {
  if (regID >= ID_LAST_ITEM)
    return UNSET;
  return this->symbolicReg[regID];
}


/* Create a new symbolic element */
/* Get an unique ID.
 * Mainly used when a new symbolic element is created */
uint64 SymbolicEngine::getUniqueID()
{
  return this->uniqueID++;
}


SymbolicElement *SymbolicEngine::newSymbolicElement(std::stringstream &src)
{
  std::stringstream dst;
  uint64            id;

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
  uint64            id;

  id = this->getUniqueID();
  dst << "#" << std::dec << id;
  SymbolicElement *elem = new SymbolicElement(dst, src, id, comment);
  this->symbolicExpressions.push_back(elem);
  return elem;
}


/* Get the symbolic element pointer from a symbolic ID */
SymbolicElement *SymbolicEngine::getElementFromId(uint64 id)
{
  if (id >= this->symbolicExpressions.size())
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
std::string SymbolicEngine::getBacktrackedExpressionFromId(uint64 id)
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
uint64 SymbolicEngine::convertExprToSymVar(uint64 exprId, uint64 symVarSize, std::string symVarComment)
{
  SymbolicVariable   *symVar  = nullptr;
  SymbolicElement    *element = this->getElementFromId(exprId);
  std::stringstream  newExpr;

  if (element == nullptr)
    return UNSET;

  if (symVarSize != BYTE_SIZE && symVarSize != WORD_SIZE && symVarSize != DWORD_SIZE && symVarSize != QWORD_SIZE && symVarSize != DQWORD_SIZE)
    throw std::runtime_error("SymbolicEngine::convertExprToSymVar() - Invalid symVarSize");

  symVar = this->addSymbolicVariable(SymVar::kind::UNDEF, 0, symVarSize, symVarComment);

  newExpr << symVar->getSymVarName();
  element->setSrcExpr(newExpr);

  return symVar->getSymVarId();
}


uint64 SymbolicEngine::convertMemToSymVar(uint64 memAddr, uint64 symVarSize, std::string symVarComment)
{
  SymbolicVariable   *symVar  = nullptr;
  SymbolicElement    *element = nullptr;
  std::stringstream  newExpr;
  uint64             memSymId = UNSET;

  memSymId = this->getMemSymbolicID(memAddr);
  if (memSymId == UNSET)
    throw std::runtime_error("SymbolicEngine::convertMemToSymVar() - This memory address is UNSET");

  element = this->getElementFromId(memSymId);

  if (element == nullptr)
    return UNSET;

  if (symVarSize != BYTE_SIZE && symVarSize != WORD_SIZE && symVarSize != DWORD_SIZE && symVarSize != QWORD_SIZE && symVarSize != DQWORD_SIZE)
    throw std::runtime_error("SymbolicEngine::convertMemToSymVar() - Invalid symVarSize");

  symVar = this->addSymbolicVariable(SymVar::kind::MEM, memAddr, symVarSize, symVarComment);

  newExpr << symVar->getSymVarName();
  element->setSrcExpr(newExpr);

  return symVar->getSymVarId();
}


uint64 SymbolicEngine::convertRegToSymVar(uint64 regId, uint64 symVarSize, std::string symVarComment)
{
  SymbolicVariable   *symVar  = nullptr;
  SymbolicElement    *element = nullptr;
  std::stringstream  newExpr;
  uint64             regSymId = UNSET;

  if (regId >= ID_LAST_ITEM)
    throw std::runtime_error("SymbolicEngine::convertRegToSymVar() - Invalid register ID");

  regSymId = this->getRegSymbolicID(regId);
  if (regSymId == UNSET)
    throw std::runtime_error("SymbolicEngine::convertRegToSymVar() - This register ID is UNSET");

  element = this->getElementFromId(regSymId);

  if (element == nullptr)
    return UNSET;

  if (symVarSize != BYTE_SIZE && symVarSize != WORD_SIZE && symVarSize != DWORD_SIZE && symVarSize != QWORD_SIZE && symVarSize != DQWORD_SIZE)
    throw std::runtime_error("SymbolicEngine::convertRegToSymVar() - Invalid symVarSize");

  symVar = this->addSymbolicVariable(SymVar::kind::REG, regId, symVarSize, symVarComment);

  newExpr << symVar->getSymVarName();
  element->setSrcExpr(newExpr);

  return symVar->getSymVarId();
}


/* Add a new symbolic variable */
SymbolicVariable *SymbolicEngine::addSymbolicVariable(SymVar::kind kind, uint64 kindValue, uint64 size, std::string comment)
{
  uint64 uniqueID = this->symbolicVariables.size();
  SymbolicVariable *symVar = new SymbolicVariable(kind, kindValue, uniqueID, size, comment);

  if (symVar == nullptr)
    throw std::runtime_error("SymbolicEngine::addSymbolicVariable() - Cannot allocate a new symbolic variable");

  this->symbolicVariables.push_back(symVar);
  return symVar;
}


/* Add and assign a new memory reference */
void SymbolicEngine::addMemoryReference(uint64 mem, uint64 id)
{
  this->memoryReference[mem] = id;
}


/* The a path constraint in the PC list */
void SymbolicEngine::addPathConstraint(uint64 exprId)
{
  this->pathConstaints.push_back(exprId);
}


/* Returns the path constrains list */
std::list<uint64> SymbolicEngine::getPathConstraints(void)
{
  return this->pathConstaints;
}


