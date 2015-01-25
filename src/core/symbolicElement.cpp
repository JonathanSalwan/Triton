
#include "pin.H"
#include "dse.h"



symbolicElement::symbolicElement(std::stringstream &dst, std::stringstream &src, UINT64 uniqueID)
{
  this->isTainted = 0;
  this->symSrc  = new std::stringstream(src.str());
  this->symDst  = new std::stringstream(dst.str());
  this->symExpr = new std::stringstream();

  *this->symExpr << (*this->symDst).str() << " = " << (*this->symSrc).str();
  this->uniqueID = uniqueID;
}


symbolicElement::~symbolicElement()
{
  delete this->symDst;
  delete this->symSrc;
  delete this->symExpr;
}

