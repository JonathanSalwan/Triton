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

      CovTag::CovTag() : TagType() {
        this->addr = 0;
        this->truth = false;
      }

      CovTag::~CovTag() {
      }

      CovTag::CovTag(CovTag const& tag) : TagType() {
        this->addr = tag.addr;
        this->truth = tag.truth;
      }

      CovTag::CovTag(triton::uint64 addr, bool truth) {
        this->addr = addr;
        this->truth = truth;
      }

      triton::uint64 CovTag::getAddress() const {
        return this->addr;
      }

      bool CovTag::getTruthValue() const {
        return this->truth;
      }

      std::string CovTag::toString() const {
        std::stringstream ss;
        ss << "CovTag(addr: " << this->getAddress()
          << ", truth: " << this->getTruthValue() << ")";
        return ss.str();
      }

      long CovTag::getHash() const {
        triton::uint64 hash = this->getAddress() * 10;
        int b = this->getTruthValue() ? 1 : 0;
        return hash + b;
      }

    }; /* taint namespace */
  }; /* engines namespace */
}; /* triton namespace */

