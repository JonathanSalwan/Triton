//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include "trigger.hpp"



namespace tracer {
  namespace pintool {

    Trigger::Trigger()
      : state(false) {
    }


    void Trigger::toggle() {
      this->state = !this->state;
    }


    bool Trigger::getState() {
      return this->state;
    }


    void Trigger::enable(void) {
      this->state = true;
    }


    void Trigger::disable(void) {
      this->state = false;
    }


    void Trigger::update(bool flag) {
      this->state = flag;
    }

  };
};
