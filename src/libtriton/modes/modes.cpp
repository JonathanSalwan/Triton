//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/modes.hpp>



namespace triton {
  namespace modes {

    Modes::Modes() {
      this->enableMode(triton::modes::PC_TRACKING_SYMBOLIC, true); /* This mode is enabled by default */
    }


    Modes::Modes(const Modes& copy) {
      this->copy(copy);
    }


    Modes::~Modes() {
    }


    void Modes::copy(const Modes& other) {
      this->enabledModes = other.enabledModes;
    }


    bool Modes::isModeEnabled(enum mode_e mode) const {
      if (this->enabledModes.find(mode) != this->enabledModes.end())
        return true;
      return false;
    }


    void Modes::enableMode(enum mode_e mode, bool flag) {
      if (flag == true)
        this->enabledModes.insert(mode);
      else
        this->enabledModes.erase(mode);
    }


    void Modes::operator=(const Modes& other) {
      this->copy(other);
    }

  }; /* modes namespace */
}; /*triton namespace */

