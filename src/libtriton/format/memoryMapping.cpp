//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/exceptions.hpp>
#include <triton/memoryMapping.hpp>



namespace triton {
  namespace format {

    MemoryMapping::MemoryMapping(const triton::uint8* binary) {
      this->binary          = binary;
      this->offset          = 0;
      this->virtualAddress  = 0;
      this->size            = 0;

      if (!this->binary)
        throw triton::exceptions::Format("MemoryMapping::MemoryMapping(): The binary pointer cannot be null");
    }


    MemoryMapping::MemoryMapping(const MemoryMapping& copy) {
      this->binary          = copy.binary;
      this->offset          = copy.offset;
      this->virtualAddress  = copy.virtualAddress;
      this->size            = copy.size;
    }


    MemoryMapping::~MemoryMapping() {
    }


    void MemoryMapping::operator=(const MemoryMapping& copy) {
      this->binary          = copy.binary;
      this->offset          = copy.offset;
      this->virtualAddress  = copy.virtualAddress;
      this->size            = copy.size;
    }


    const triton::uint8* MemoryMapping::getBinary(void) const {
      return this->binary;
    }


    triton::uint64 MemoryMapping::getOffset(void) const {
      return this->offset;
    }


    triton::uint64 MemoryMapping::getVirtualAddress(void) const {
      return this->virtualAddress;
    }


    const triton::uint8* MemoryMapping::getMemoryArea(void) const {
      return (this->binary + this->offset);
    }


    triton::uint64 MemoryMapping::getSize(void) const {
      return this->size;
    }


    void MemoryMapping::setOffset(triton::uint64 offset) {
      this->offset = offset;
    }


    void MemoryMapping::setVirtualAddress(triton::uint64 virtualAddress) {
      this->virtualAddress = virtualAddress;
    }


    void MemoryMapping::setSize(triton::uint64 size) {
      this->size = size;
    }

  }; /* format namespace */
}; /* triton namespace */
