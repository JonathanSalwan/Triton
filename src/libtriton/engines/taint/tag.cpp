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

      Tag::Tag(char* data) {
        /* I first thought of keeping the char* as it is for a better performance, but gave it up since the Python's
         * resource management scheme * is totally different from C++ that the stored char* does not always point to
         * the same string as it was at the time when the pointer was stored. */
        this->data = std::make_shared<std::string>(data);
      }

      Tag::~Tag() {
        /* the shared pointer `this->data` shall not be deleted. */
      }

      std::shared_ptr<std::string> Tag::getData() const {
        return this->data;
      }

      bool Tag::operator<(const Tag &rhs) const {
        // pointer-based comparison. cheaper than string comparison
        return this->data < rhs.data;
      }

      bool Tag::operator==(const Tag &rhs) const {
        /* pointer-based comparison */
        return this->data == rhs.data;
      }

    }; /* taint namespace */
  }; /* engines namespace */
}; /* triton namespace */

