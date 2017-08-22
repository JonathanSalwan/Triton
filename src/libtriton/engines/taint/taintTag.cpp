//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/exceptions.hpp>
#include <triton/taintTag.hpp>


namespace triton {
  namespace engines {
    namespace taint {

      TaintTag::TaintTag() {
      }

      TaintTag::~TaintTag() {
      }

      TaintTag::TaintTag(TaintTag const& tag) {
        this->data = tag.data;
      }

      TaintTag::TaintTag(void * data) {
        this->data = data;
      }

      void* TaintTag::getData() {
        return this->data;
      }

    }; /* taint namespace */
  }; /* engines namespace */
}; /* triton namespace */

