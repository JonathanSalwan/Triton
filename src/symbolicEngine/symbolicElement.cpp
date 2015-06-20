
#include <SymbolicEngine.h>


SymbolicElement::SymbolicElement(std::stringstream &dst, std::stringstream &src, uint64 id)
{
  this->isTainted   = false;
  this->source      = new std::stringstream(src.str());
  this->destination = new std::stringstream(dst.str());
  this->expression  = new std::stringstream();
  this->comment     = new std::string();

  *this->expression << (*this->destination).str() << " = " << (*this->source).str();

  this->id = id;
}


SymbolicElement::SymbolicElement(std::stringstream &dst, std::stringstream &src, uint64 id, std::string &comment)
{
  this->isTainted   = false;
  this->source      = new std::stringstream(src.str());
  this->destination = new std::stringstream(dst.str());
  this->expression  = new std::stringstream();
  this->comment     = new std::string(comment);

  *this->expression << (*this->destination).str() << " = " << (*this->source).str();

  this->id = id;
}


SymbolicElement::~SymbolicElement()
{
  delete this->comment;
  delete this->destination;
  delete this->expression;
  delete this->source;
}


/* Returns the SMT dst and src expression of the symbolic element */
std::stringstream *SymbolicElement::getExpression(void)
{
  return this->expression;
}


/* Returns the comment of the element */
std::string *SymbolicElement::getComment(void)
{
  return this->comment;
}


/* Returns the SMT src expression of the symbolic element */
std::stringstream *SymbolicElement::getSource(void)
{
  return this->source;
}


/* Returns the SMT dst expression of the symbolic element */
std::stringstream *SymbolicElement::getDestination(void)
{
  return this->destination;
}


/* Returns the ID of the symbolic element */
uint64 SymbolicElement::getID(void)
{
  return this->id;
}


/* Returns a std::string ID of the symbolic element */
std::string SymbolicElement::getID2Str(void)
{
  std::stringstream expr;
  expr << "#" << std::dec << this->id;
  return expr.str();
}


/* Set the destination expression */
void SymbolicElement::setSrcExpr(std::stringstream &src)
{
  delete this->expression;
  delete this->source;

  this->expression  = new std::stringstream();
  this->source      = new std::stringstream(src.str());

  *this->expression << (*this->destination).str() << " = " << (*this->source).str();
}

