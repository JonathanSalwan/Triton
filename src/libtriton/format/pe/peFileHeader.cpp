//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstdio>

#include <peFileHeader.hpp>
#include <exceptions.hpp>



namespace triton {
  namespace format {
    namespace pe {

      PeFileHeader::PeFileHeader() {
        this->machine = 0;
        this->numberOfSections = 0;
        this->timeDateStamp = 0;
        this->pointerToSymbolTable = 0;
        this->numberOfSymbolTable = 0;
        this->sizeOfOptionalHeader = 0;
        this->characteristics = 0;
      }


      PeFileHeader::PeFileHeader(const PeFileHeader& copy) {
        this->machine              = copy.machine;
        this->numberOfSections     = copy.numberOfSections;
        this->timeDateStamp        = copy.timeDateStamp;
        this->pointerToSymbolTable = copy.pointerToSymbolTable;
        this->numberOfSymbolTable  = copy.numberOfSymbolTable;
        this->sizeOfOptionalHeader = copy.sizeOfOptionalHeader;
        this->characteristics      = copy.characteristics;
      }


      PeFileHeader::~PeFileHeader() {
      }


      PeFileHeader &PeFileHeader::operator=(const PeFileHeader& copy) {
        if (this == &copy)
            return *this;
        this->machine              = copy.machine;
        this->numberOfSections     = copy.numberOfSections;
        this->timeDateStamp        = copy.timeDateStamp;
        this->pointerToSymbolTable = copy.pointerToSymbolTable;
        this->numberOfSymbolTable  = copy.numberOfSymbolTable;
        this->sizeOfOptionalHeader = copy.sizeOfOptionalHeader;
        this->characteristics      = copy.characteristics;
        return *this;
      }


      void PeFileHeader::parse(const triton::uint8* raw) {
        std::memcpy(&this->machine, raw, 20);
      }

      triton::uint16 PeFileHeader::getMachine(void) const {
        return this->machine;
      }


      triton::uint16 PeFileHeader::getNumberOfSections(void) const {
        return this->numberOfSections;
      }


      triton::uint32 PeFileHeader::getTimeDateStamp(void) const {
        return this->timeDateStamp;
      }


      triton::uint32 PeFileHeader::getPointerToSymbolTable(void) const {
        return this->pointerToSymbolTable;
      }


      triton::uint32 PeFileHeader::getNumberOfSymbolTable(void) const {
        return this->numberOfSymbolTable;
      }


      triton::uint16 PeFileHeader::getSizeOfOptionalHeader(void) const {
        return this->sizeOfOptionalHeader;
      }


      triton::uint16 PeFileHeader::getCharacteristics(void) const {
        return this->characteristics;
      }

    }; /* pe namespace */
  }; /* format namespace */
}; /* triton namespace */

