
#include "TaintEngine.h"
#include "SymbolicEngine.h"


symbolicElement::symbolicElement(std::stringstream &dst, std::stringstream &src, uint64_t id)
{
  this->isTainted   = !TAINTED;
  this->source      = new std::stringstream(src.str());
  this->destination = new std::stringstream(dst.str());
  this->expression  = new std::stringstream();

  *this->expression << (*this->destination).str() << " = " << (*this->source).str();

  this->id = id;
}


symbolicElement::~symbolicElement()
{
  delete this->source;
  delete this->destination;
  delete this->expression;
}


std::string symbolicElement::getExpression()
{
  return this->expression->str();
}


std::string symbolicElement::getSource()
{
  return this->source->str();
}


uint64_t symbolicElement::getID()
{
  return this->id;
}

