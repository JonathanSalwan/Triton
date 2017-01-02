//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstdio>

#include <exceptions.hpp>
#include <peSectionHeader.hpp>



namespace triton {
  namespace format {
    namespace pe {

      PeSectionHeader::PeSectionHeader() {
        std::memset(this->st.name, 0x00, sizeof(this->st.name));

        this->st.virtualSize          = 0;
        this->st.virtualAddress       = 0;
        this->st.rawSize              = 0;
        this->st.rawAddress           = 0;
        this->st.pointerToRelocations = 0;
        this->st.pointerToLinenumbers = 0;
        this->st.numberOfRelocations  = 0;
        this->st.numberOfLinenumbers  = 0;
        this->st.characteristics      = 0;
        this->name                    = "";
      }


      PeSectionHeader::PeSectionHeader(const PeSectionHeader& copy) {
        std::memcpy(this->st.name, copy.st.name, sizeof(this->st.name));

        this->st.virtualSize          = copy.st.virtualSize;
        this->st.virtualAddress       = copy.st.virtualAddress;
        this->st.rawSize              = copy.st.rawSize;
        this->st.rawAddress           = copy.st.rawAddress;
        this->st.pointerToRelocations = copy.st.pointerToRelocations;
        this->st.pointerToLinenumbers = copy.st.pointerToLinenumbers;
        this->st.numberOfRelocations  = copy.st.numberOfRelocations;
        this->st.numberOfLinenumbers  = copy.st.numberOfLinenumbers;
        this->st.characteristics      = copy.st.characteristics;
        this->name                    = copy.name;
      }


      PeSectionHeader::~PeSectionHeader() {
      }


      PeSectionHeader& PeSectionHeader::operator=(const PeSectionHeader& copy) {
        if (this == &copy)
          return *this;

        std::memcpy(this->st.name, copy.st.name, sizeof(this->st.name));

        this->st.virtualSize          = copy.st.virtualSize;
        this->st.virtualAddress       = copy.st.virtualAddress;
        this->st.rawSize              = copy.st.rawSize;
        this->st.rawAddress           = copy.st.rawAddress;
        this->st.pointerToRelocations = copy.st.pointerToRelocations;
        this->st.pointerToLinenumbers = copy.st.pointerToLinenumbers;
        this->st.numberOfRelocations  = copy.st.numberOfRelocations;
        this->st.numberOfLinenumbers  = copy.st.numberOfLinenumbers;
        this->st.characteristics      = copy.st.characteristics;
        this->name                    = copy.name;

        return *this;
      }


      triton::uint32 PeSectionHeader::parse(const triton::uint8* raw) {
        std::memcpy(&this->st, raw, sizeof(this->st));
        name = std::string(reinterpret_cast<const char*>(&this->st.name[0]), 8).c_str();

        return sizeof(st);
      }


      std::string PeSectionHeader::getName(void) const {
        return this->name;
      }


      triton::uint32 PeSectionHeader::getVirtualSize(void) const {
        return this->st.virtualSize;
      }


      triton::uint32 PeSectionHeader::getVirtualAddress(void) const {
        return this->st.virtualAddress;
      }


      triton::uint32 PeSectionHeader::getRawSize(void) const {
        return this->st.rawSize;
      }


      triton::uint32 PeSectionHeader::getRawAddress(void) const {
        return this->st.rawAddress;
      }


      triton::uint32 PeSectionHeader::getPointerToRelocations(void) const {
        return this->st.pointerToRelocations;
      }


      triton::uint32 PeSectionHeader::getPointerToLinenumbers(void) const {
        return this->st.pointerToLinenumbers;
      }


      triton::uint16 PeSectionHeader::getNumberOfRelocations(void) const {
        return this->st.numberOfRelocations;
      }


      triton::uint16 PeSectionHeader::getNumberOfLinenumbers(void) const {
        return this->st.numberOfLinenumbers;
      }


      triton::uint32 PeSectionHeader::getCharacteristics(void) const {
        return this->st.characteristics;
      }

    }; /* pe namespace */
  }; /* format namespace */
}; /* triton namespace */


