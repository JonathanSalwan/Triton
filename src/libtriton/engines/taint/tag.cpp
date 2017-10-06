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

      std::map<std::string, Tag> Tag::tagMap = std::map<std::string, Tag>();

      Tag::Tag(char* data) {
        this->data = std::make_shared<std::string>(data);
      }

      Tag Tag::createTag(char *data) {
        auto tag = Tag::tagMap.find(std::string(data));
        if (tag != Tag::tagMap.end()) {
          return tag->second;
        } else {
          return Tag(data);
        }
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

