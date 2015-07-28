/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


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
  std::vector<SymbolicExpression *>::iterator it1 = this->symbolicExpressions.begin();
  std::vector<SymbolicVariable *>::iterator it2 = this->symbolicVariables.begin();

  /* Delete all symbolic expressions */
  for (; it1 != this->symbolicExpressions.end(); ++it1)
    delete *it1;

  /* Delete all symbolic variables */
  for (; it2 != this->symbolicVariables.end(); ++it2)
    delete *it2;
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


/* Same as concretizeReg but with all registers */
void SymbolicEngine::concretizeAllReg(void) {
  for (uint64 i = 0; i < ID_LAST_ITEM; i++)
    this->symbolicReg[i] = UNSET;
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


/* Same as concretizeMem but with all address memory */
void SymbolicEngine::concretizeAllMem(void)
{
  this->memoryReference.clear();
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


/* Create a new symbolic expression */
/* Get an unique ID.
 * Mainly used when a new symbolic expression is created */
uint64 SymbolicEngine::getUniqueID()
{
  return this->uniqueID++;
}


SymbolicExpression *SymbolicEngine::newSymbolicExpression(smt2lib::smtAstAbstractNode *node)
{
  uint64 id = this->getUniqueID();
  SymbolicExpression *expr = new SymbolicExpression(node, id);
  this->symbolicExpressions.push_back(expr);
  return expr;
}


/* Create a new symbolic expression with comment */
SymbolicExpression *SymbolicEngine::newSymbolicExpression(smt2lib::smtAstAbstractNode *node, std::string comment)
{
  uint64 id = this->getUniqueID();
  SymbolicExpression *expr = new SymbolicExpression(node, id, comment);
  this->symbolicExpressions.push_back(expr);
  return expr;
}


/* Get the symbolic expression pointer from a symbolic ID */
SymbolicExpression *SymbolicEngine::getExpressionFromId(uint64 id)
{
  if (id >= this->symbolicExpressions.size())
    return nullptr;
  return this->symbolicExpressions[id];
}


/* Returns all symbolic expressions */
std::vector<SymbolicExpression *> SymbolicEngine::getExpressions(void)
{
  return this->symbolicExpressions;
}


/* Returns the full symbolic expression backtracked. */
smt2lib::smtAstAbstractNode *SymbolicEngine::getFullExpression(smt2lib::smtAstAbstractNode *node)
{
  uint64 index = 0;
  std::vector<smt2lib::smtAstAbstractNode *> &childs = node->getChilds();

  for ( ; index < childs.size(); index++) {
    if (childs[index]->getKind() == smt2lib::REFERENCE_NODE) {
      uint64 id = reinterpret_cast<smt2lib::smtAstReferenceNode*>(childs[index])->getValue();
      smt2lib::smtAstAbstractNode *ref = this->getExpressionFromId(id)->getExpression();
      childs[index] = smt2lib::newInstance(ref);
    }
    this->getFullExpression(childs[index]);
  }

  return node;
}


/* Returns a list which contains all tainted expressions */
std::list<SymbolicExpression *> SymbolicEngine::getTaintedExpressions(void)
{
  uint64 index = 0;
  std::list<SymbolicExpression *> taintedExprs;

  for ( ; index < this->symbolicExpressions.size(); index++) {
    if (symbolicExpressions[index]->isTainted == true)
      taintedExprs.push_back(symbolicExpressions[index]);
  }
  return taintedExprs;
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
SymbolicVariable *SymbolicEngine::convertExprToSymVar(uint64 exprId, uint64 symVarSize, std::string symVarComment)
{
  SymbolicVariable    *symVar = nullptr;
  SymbolicExpression  *expression = this->getExpressionFromId(exprId);

  if (expression == nullptr)
    return nullptr;

  symVar = this->addSymbolicVariable(SymVar::kind::UNDEF, 0, symVarSize, symVarComment);

  expression->setExpression(smt2lib::variable(symVar->getSymVarName()));

  return symVar;
}


SymbolicVariable *SymbolicEngine::convertMemToSymVar(uint64 memAddr, uint64 symVarSize, std::string symVarComment)
{
  SymbolicVariable   *symVar = nullptr;
  SymbolicExpression *expression = nullptr;
  uint64             memSymId = UNSET;

  memSymId = this->getMemSymbolicID(memAddr);
  if (memSymId == UNSET)
    throw std::runtime_error("SymbolicEngine::convertMemToSymVar() - This memory address is UNSET");

  expression = this->getExpressionFromId(memSymId);

  if (expression == nullptr)
    return nullptr;

  symVar = this->addSymbolicVariable(SymVar::kind::MEM, memAddr, symVarSize, symVarComment);

  expression->setExpression(smt2lib::variable(symVar->getSymVarName()));

  return symVar;
}


SymbolicVariable *SymbolicEngine::convertRegToSymVar(uint64 regId, uint64 symVarSize, std::string symVarComment)
{
  SymbolicVariable   *symVar = nullptr;
  SymbolicExpression *expression = nullptr;
  uint64             regSymId = UNSET;

  if (regId >= ID_LAST_ITEM)
    throw std::runtime_error("SymbolicEngine::convertRegToSymVar() - Invalid register ID");

  regSymId = this->getRegSymbolicID(regId);
  if (regSymId == UNSET)
    throw std::runtime_error("SymbolicEngine::convertRegToSymVar() - This register ID is UNSET");

  expression = this->getExpressionFromId(regSymId);

  if (expression == nullptr)
    return nullptr;

  symVar = this->addSymbolicVariable(SymVar::kind::REG, regId, symVarSize, symVarComment);

  expression->setExpression(smt2lib::variable(symVar->getSymVarName()));

  return symVar;
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

