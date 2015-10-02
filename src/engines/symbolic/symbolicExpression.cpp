/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <SymbolicEngine.h>


SymbolicExpression::SymbolicExpression(smt2lib::smtAstAbstractNode *expr, uint64 id) {
  this->expression  = expr;
  this->id          = id;
  this->isTainted   = false;
}


SymbolicExpression::SymbolicExpression(smt2lib::smtAstAbstractNode *expr, uint64 id, std::string comment) {
  this->comment     = comment;
  this->expression  = expr;
  this->id          = id;
  this->isTainted   = false;
}


SymbolicExpression::~SymbolicExpression() {
  delete this->expression;
}


/* Returns the SMT expression of the symbolic expression */
smt2lib::smtAstAbstractNode *SymbolicExpression::getExpression(void) {
  return this->expression;
}


/* Returns the comment of the expression */
std::string SymbolicExpression::getComment(void) {
  return this->comment;
}


/* Returns the ID of the symbolic expression */
uint64 SymbolicExpression::getID(void) {
  return this->id;
}


/* Returns a std::string ID of the symbolic expression */
std::string SymbolicExpression::getID2Str(void) {
  return "#" + std::to_string(this->id);
}


/* Set the destination expression */
void SymbolicExpression::setExpression(smt2lib::smtAstAbstractNode *expr) {
  delete this->expression;
  this->expression = expr;
}

#endif /* LIGHT_VERSION */

