//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <iostream>
#include <triton/modes.hpp>



namespace triton {
  namespace modes {

    Modes::Modes() {
      this->setMode(triton::modes::PC_TRACKING_SYMBOLIC, true); /* This mode is enabled by default */
    }


    Modes::Modes(const Modes& other) {
      this->copy(other);
    }


    Modes& Modes::operator=(const Modes& other) {
      this->copy(other);
      return *this;
    }


    void Modes::copy(const Modes& other) {
      this->enabledModes = other.enabledModes;
    }


    bool Modes::isModeEnabled(triton::modes::mode_e mode) const {
      if (this->enabledModes.find(mode) != this->enabledModes.end())
        return true;
      return false;
    }


    void Modes::setMode(triton::modes::mode_e mode, bool flag) {
      if (flag == true)
        this->enabledModes.insert(mode);
      else
        this->enabledModes.erase(mode);
    }


    void Modes::clearModes(void) {
      this->enabledModes.clear();
    }

  }; /* modes namespace */
}; /*triton namespace */
