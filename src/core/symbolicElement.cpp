//
//  Jonathan Salwan - 2015-01-24
// 
//  http://shell-storm.org
//  http://twitter.com/JonathanSalwan
// 
//  This program is free software: you can redistribute it and/or modify
//  it under the terms of the GNU General Public License as published by
//  the Free Software  Foundation, either  version 3 of  the License, or
//  (at your option) any later version.
//

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

