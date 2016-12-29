//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstdio>

#include <peSectionHeader.hpp>
#include <exceptions.hpp>



namespace triton {
  namespace format {
    namespace pe {

      PeSectionHeader::PeSectionHeader() {
        this->name = "";
        this->virtualSize = 0;
        this->virtualAddress = 0;
        this->rawSize = 0;
        this->rawAddress = 0;
        this->pointerToRelocations = 0;
        this->pointerToLinenumbers = 0;
        this->numberOfRelocations = 0;
        this->numberOfLinenumbers = 0;
        this->characteristics = 0;
      }


      PeSectionHeader::PeSectionHeader(const PeSectionHeader& copy) {
        this->name                 = copy.name;
        this->virtualSize          = copy.virtualSize;
        this->virtualAddress       = copy.virtualAddress;
        this->rawSize              = copy.rawSize;
        this->rawAddress           = copy.rawAddress;
        this->pointerToRelocations = copy.pointerToRelocations;
        this->pointerToLinenumbers = copy.pointerToLinenumbers;
        this->numberOfRelocations  = copy.numberOfRelocations;
        this->numberOfLinenumbers  = copy.numberOfLinenumbers;
        this->characteristics      = copy.characteristics;
      }


      PeSectionHeader::~PeSectionHeader() {
      }


      PeSectionHeader &PeSectionHeader::operator=(const PeSectionHeader& copy) {
        if (this == &copy)
            return *this;
        this->name                 = copy.name;
        this->virtualSize          = copy.virtualSize;
        this->virtualAddress       = copy.virtualAddress;
        this->rawSize              = copy.rawSize;
        this->rawAddress           = copy.rawAddress;
        this->pointerToRelocations = copy.pointerToRelocations;
        this->pointerToLinenumbers = copy.pointerToLinenumbers;
        this->numberOfRelocations  = copy.numberOfRelocations;
        this->numberOfLinenumbers  = copy.numberOfLinenumbers;
        this->characteristics      = copy.characteristics;
        return *this;
      }


      triton::uint32 PeSectionHeader::parse(const triton::uint8* raw) {
        char tmpname[8];
        std::memcpy(&tmpname[0], raw, 8);
        name = std::string(tmpname,8).c_str();
        
        std::memcpy(&virtualSize, raw+8, 32);
        return 40;
      }

      std::string PeSectionHeader::getName(void) const {
        return this->name;
      }


      triton::uint32 PeSectionHeader::getVirtualSize(void) const {
        return this->virtualSize;
      }


      triton::uint32 PeSectionHeader::getVirtualAddress(void) const {
        return this->virtualAddress;
      }


      triton::uint32 PeSectionHeader::getRawSize(void) const {
        return this->rawSize;
      }


      triton::uint32 PeSectionHeader::getRawAddress(void) const {
        return this->rawAddress;
      }


      triton::uint32 PeSectionHeader::getPointerToRelocations(void) const {
        return this->pointerToRelocations;
      }


      triton::uint32 PeSectionHeader::getPointerToLinenumbers(void) const {
        return this->pointerToLinenumbers;
      }


      triton::uint16 PeSectionHeader::getNumberOfRelocations(void) const {
        return this->numberOfRelocations;
      }


      triton::uint16 PeSectionHeader::getNumberOfLinenumbers(void) const {
        return this->numberOfLinenumbers;
      }


      triton::uint32 PeSectionHeader::getCharacteristics(void) const {
        return this->characteristics;
      }

    }; /* pe namespace */
  }; /* format namespace */
}; /* triton namespace */


