//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/exceptions.hpp>
#include <triton/covTag.hpp>


namespace triton {
  namespace engines {
    namespace taint {

      CovTag::CovTag() {
        this->addr = 0;
        this->truth = false;
      }

      CovTag::CovTag(CovTag& tag): TagType(tag) {
        this->addr = tag.addr;
        this->truth = tag.truth;
      }

      CovTag::CovTag(triton::uint64 addr, bool truth) {
        this->addr = addr;
        this->truth = truth;
      }

      triton::uint64 CovTag::getAddress() {
        return this->addr;
      }

      bool CovTag::getTruthValue() {
        return this->truth;
      }

    }; /* taint namespace */
  }; /* engines namespace */
}; /* triton namespace */

