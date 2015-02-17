#include "Trigger.h"

Trigger::Trigger(): state(false) { }


void Trigger::toggle()
{
  this->state = !this->state;
}


bool Trigger::getState()
{
  return this->state;
}
