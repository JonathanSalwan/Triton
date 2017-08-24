//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/exceptions.hpp>
#include <triton/tag.hpp>


namespace triton {
  namespace engines {
    namespace taint {

      Tag::Tag() {
      }

      Tag::~Tag() {
      }

      Tag::Tag(Tag const& tag) {
        this->data = tag.data;
      }

      Tag::Tag(void * data) {
        this->data = data;
      }

      void* Tag::getData() {
        return this->data;
      }

    }; /* taint namespace */
  }; /* engines namespace */
}; /* triton namespace */

