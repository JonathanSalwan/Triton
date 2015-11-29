
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <SymbolicEngine.h>
#include <Registers.h>




SymbolicEngine::SymbolicEngine() {
  /* Init all symbolic registers/flags to UNSET (init state) */
  for (__uint i = 0; i < ID_LAST_ITEM; i++)
    this->symbolicReg[i] = UNSET;
  this->uniqueID = 0;
  this->enableFlag = true;
}


void SymbolicEngine::init(const SymbolicEngine &other) {
  for (__uint i = 0; i < ID_LAST_ITEM; i++)
    this->symbolicReg[i] = other.symbolicReg[i];

  this->enableFlag                    = other.enableFlag;
  this->memoryReference               = other.memoryReference;
  this->pathConstaints                = other.pathConstaints;
  this->symbolicExpressions           = other.symbolicExpressions;
  this->symbolicVariables             = other.symbolicVariables;
  this->uniqueID                      = other.uniqueID;
}


SymbolicEngine::SymbolicEngine(const SymbolicEngine &copy) {
  this->init(copy);
}


void SymbolicEngine::operator=(const SymbolicEngine &other) {
  this->init(other);
}


SymbolicEngine::~SymbolicEngine() {
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
void SymbolicEngine::concretizeReg(__uint regID) {
  if (regID >= ID_LAST_ITEM)
    return ;
  this->symbolicReg[regID] = UNSET;
}


/* Same as concretizeReg but with all registers */
void SymbolicEngine::concretizeAllReg(void) {
  for (__uint i = 0; i < ID_LAST_ITEM; i++)
    this->symbolicReg[i] = UNSET;
}


/*
 * Concretize a memory. If the memory is not found into the map, the next
 * assignment will be over the concretization. This method must be called
 * before symbolic processing.
 */
void SymbolicEngine::concretizeMem(__uint mem) {
  this->memoryReference.erase(mem);
}


/* Same as concretizeMem but with all address memory */
void SymbolicEngine::concretizeAllMem(void) {
  this->memoryReference.clear();
}


/* Returns the reference memory if it's referenced otherwise returns UNSET */
__uint SymbolicEngine::getMemSymbolicID(__uint addr) {
  std::map<__uint, __uint>::iterator it;
  if ((it = this->memoryReference.find(addr)) != this->memoryReference.end())
    return it->second;
  return UNSET;
}


/* Returns the symbolic variable otherwise returns nullptr */
SymbolicVariable *SymbolicEngine::getSymVar(__uint symVarId) {
  if (symVarId >= this->symbolicVariables.size())
    return nullptr;
  return this->symbolicVariables[symVarId];
}


/* Returns the symbolic variable otherwise returns nullptr */
SymbolicVariable *SymbolicEngine::getSymVar(std::string symVarName) {
  std::vector<SymbolicVariable *>::iterator it;

  for (it = this->symbolicVariables.begin(); it != this->symbolicVariables.end(); it++){
    if ((*it)->getSymVarName() == symVarName)
      return *it;
  }
  return nullptr;
}


/* Returns all symbolic variables */
std::vector<SymbolicVariable *> SymbolicEngine::getSymVars(void) {
  return this->symbolicVariables;
}


/* Return the reg reference or UNSET */
__uint SymbolicEngine::getRegSymbolicID(__uint regID) {
  if (regID >= ID_LAST_ITEM)
    return UNSET;
  return this->symbolicReg[regID];
}


/* Create a new symbolic expression */
/* Get an unique ID.
 * Mainly used when a new symbolic expression is created */
__uint SymbolicEngine::getUniqueID() {
  return this->uniqueID++;
}


/* Create a new symbolic expression with comment */
SymbolicExpression *SymbolicEngine::newSymbolicExpression(smt2lib::smtAstAbstractNode *node, enum SymExpr::kind kind, std::string comment) {
  __uint id = this->getUniqueID();
  SymbolicExpression *expr = new SymbolicExpression(node, id, kind, comment);
  this->symbolicExpressions.push_back(expr);
  return expr;
}


/* Get the symbolic expression pointer from a symbolic ID */
SymbolicExpression *SymbolicEngine::getExpressionFromId(__uint id) {
  if (id >= this->symbolicExpressions.size())
    return nullptr;
  return this->symbolicExpressions[id];
}


/* Returns all symbolic expressions */
std::vector<SymbolicExpression *> SymbolicEngine::getExpressions(void) {
  return this->symbolicExpressions;
}


/* Returns the full symbolic expression backtracked. */
smt2lib::smtAstAbstractNode *SymbolicEngine::getFullExpression(smt2lib::smtAstAbstractNode *node) {
  __uint index = 0;
  std::vector<smt2lib::smtAstAbstractNode *> &childs = node->getChilds();

  for ( ; index < childs.size(); index++) {
    if (childs[index]->getKind() == smt2lib::REFERENCE_NODE) {
      __uint id = reinterpret_cast<smt2lib::smtAstReferenceNode*>(childs[index])->getValue();
      smt2lib::smtAstAbstractNode *ref = this->getExpressionFromId(id)->getExpression();
      childs[index] = ref;
    }
    this->getFullExpression(childs[index]);
  }

  return node;
}


/* Returns a list which contains all tainted expressions */
std::list<SymbolicExpression *> SymbolicEngine::getTaintedExpressions(void) {
  __uint index = 0;
  std::list<SymbolicExpression *> taintedExprs;

  for ( ; index < this->symbolicExpressions.size(); index++) {
    if (symbolicExpressions[index]->isTainted == true)
      taintedExprs.push_back(symbolicExpressions[index]);
  }
  return taintedExprs;
}


/* Returns the list of the symbolic variables declared in the trace */
std::string SymbolicEngine::getVariablesDeclaration(void) {
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
SymbolicVariable *SymbolicEngine::convertExprToSymVar(__uint exprId, __uint symVarSize, std::string symVarComment) {
  SymbolicVariable    *symVar = nullptr;
  SymbolicExpression  *expression = this->getExpressionFromId(exprId);

  if (expression == nullptr)
    return nullptr;

  symVar = this->addSymbolicVariable(SymVar::kind::UNDEF, 0, symVarSize, symVarComment);

  expression->setExpression(smt2lib::variable(symVar->getSymVarName()));

  return symVar;
}


/* Note: symVarSize is in BYTE. */
SymbolicVariable *SymbolicEngine::convertMemToSymVar(__uint memAddr, __uint symVarSize, std::string symVarComment)
{
  SymbolicVariable   *symVar       = nullptr;
  SymbolicExpression *expression   = nullptr;
  smt2lib::smtAstAbstractNode *tmp = nullptr;
  __uint memSymId                  = UNSET;

  __uint size_quotient   = symVarSize;
  memSymId = this->getMemSymbolicID(memAddr);

  // First we create a symbolic variable
  symVar = this->addSymbolicVariable(SymVar::kind::MEM, memAddr, symVarSize * BYTE_SIZE_BIT, symVarComment);
  smt2lib::smtAstAbstractNode *symVarNode = smt2lib::variable(symVar->getSymVarName());

  if (symVarNode == nullptr)
    throw std::runtime_error("convertMemToSymVar can't create smtAstAbstractNode (nullptr)");

  std::list<smt2lib::smtAstAbstractNode *> symMemChunk;
  while (size_quotient) {
      tmp = smt2lib::extract(((BYTE_SIZE_BIT * size_quotient) - 1), ((BYTE_SIZE_BIT * size_quotient) - BYTE_SIZE_BIT), symVarNode);
      symMemChunk.push_back(tmp);

      if (tmp == nullptr)
        throw std::runtime_error("convertMemToSymVar can't create extract (nullptr)");

      if (memSymId == UNSET) {
        if (size_quotient > 1 or symVarSize == 1) {
          expression = this->newSymbolicExpression(tmp, SymExpr::MEM, "byte reference");
        } else {
          smt2lib::smtAstAbstractNode *concat = smt2lib::concat(symMemChunk);
          expression = this->newSymbolicExpression(concat, SymExpr::MEM);
        }
      } else {
        expression = this->getExpressionFromId(memSymId);
        expression->setExpression(tmp);
      }

      if (expression == nullptr)
        throw std::runtime_error("convertMemToSymVar can't create symbolic expression (nullptr)");

      this->addMemoryReference((memAddr + size_quotient) - 1, expression->getID());

      size_quotient--;
  }

  return symVar;
}


SymbolicVariable *SymbolicEngine::convertRegToSymVar(__uint regId, __uint symVarSize, std::string symVarComment) {
  SymbolicVariable   *symVar = nullptr;
  SymbolicExpression *expression = nullptr;
  __uint             regSymId = UNSET;

  if (regId >= ID_LAST_ITEM)
    throw std::runtime_error("SymbolicEngine::convertRegToSymVar() - Invalid register ID");

  regSymId = this->getRegSymbolicID(regId);
  if (regSymId == UNSET) {
    symVar = this->addSymbolicVariable(SymVar::kind::REG, regId, symVarSize, symVarComment);

    smt2lib::smtAstAbstractNode *tmp = smt2lib::variable(symVar->getSymVarName());
    if (tmp == nullptr)
      throw std::runtime_error("convertRegToSymVar can't create smtAstAbstractNode (nullptr)");

    SymbolicExpression *se = this->newSymbolicExpression(tmp, SymExpr::REG);
    if (se == nullptr)
      throw std::runtime_error("convertRegToSymVar can't create symbolic expression (nullptr)");

    this->symbolicReg[regId] = se->getID();
  }

  else {
    expression = this->getExpressionFromId(regSymId);
    if (expression == nullptr)
      return nullptr;
    symVar = this->addSymbolicVariable(SymVar::kind::REG, regId, symVarSize, symVarComment);
    expression->setExpression(smt2lib::variable(symVar->getSymVarName()));
  }

  return symVar;
}


/* Add a new symbolic variable */
SymbolicVariable *SymbolicEngine::addSymbolicVariable(SymVar::kind kind, __uint kindValue, __uint size, std::string comment) {
  __uint uniqueID = this->symbolicVariables.size();
  SymbolicVariable *symVar = new SymbolicVariable(kind, kindValue, uniqueID, size, comment);

  if (symVar == nullptr)
    throw std::runtime_error("SymbolicEngine::addSymbolicVariable() - Cannot allocate a new symbolic variable");

  this->symbolicVariables.push_back(symVar);
  return symVar;
}


/* Add and assign a new memory reference */
void SymbolicEngine::addMemoryReference(__uint mem, __uint id) {
  this->memoryReference[mem] = id;
}


/* The a path constraint in the PC list */
void SymbolicEngine::addPathConstraint(__uint exprId) {
  this->pathConstaints.push_back(exprId);
}


/* Returns the path constrains list */
std::list<__uint> SymbolicEngine::getPathConstraints(void) {
  return this->pathConstaints;
}


/* Returns true if the symbolic engine is enable. Otherwise returns false. */
bool SymbolicEngine::isEnabled(void) {
  return this->enableFlag;
}


/* Locks the symbolic engine */
void SymbolicEngine::disable(void) {
  this->enableFlag = false;
}


/* Unlocks the symbolic engine */
void SymbolicEngine::enable(void) {
  this->enableFlag = true;
}


#endif /* LIGHT_VERSION */

