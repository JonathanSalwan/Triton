
#include <Smodel.h>


Smodel::Smodel(std::string name, uint64 value)
{
  this->name = name;
  this->value = value;
}


Smodel::~Smodel()
{
}


std::string Smodel::getName(void)
{
  return this->name;
}


uint64 Smodel::getValue(void)
{
  return this->value;
}

