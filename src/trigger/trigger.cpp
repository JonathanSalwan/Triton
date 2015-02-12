#include "trigger.h"

Trigger::Trigger(): _state(false) { }


void Trigger::toggle()
{
  _state = !_state;
}


bool Trigger::getState()
{
  return _state;
}
