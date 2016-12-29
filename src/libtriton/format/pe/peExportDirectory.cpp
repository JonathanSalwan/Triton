//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstdio>

#include <peExportDirectory.hpp>
#include <exceptions.hpp>



namespace triton {
  namespace format {
    namespace pe {

      PeExportDirectory::PeExportDirectory() {
        this->exportFlags = 0;
        this->timeDateStamp = 0;
        this->majorVersion = 0;
        this->minorVersion = 0;
        this->nameRVA = 0;
        this->ordinalBase = 0;
        this->addressTableEntries = 0;
        this->numberOfNamePointers = 0;
        this->exportAddressTableRVA = 0;
        this->namePointerRVA = 0;
        this->ordinalTableRVA = 0;
      }


      PeExportDirectory::PeExportDirectory(const PeExportDirectory& copy) {
        this->exportFlags           = copy.exportFlags;
        this->timeDateStamp         = copy.timeDateStamp;
        this->majorVersion          = copy.majorVersion;
        this->minorVersion          = copy.minorVersion;
        this->nameRVA               = copy.nameRVA;
        this->ordinalBase           = copy.ordinalBase;
        this->addressTableEntries   = copy.addressTableEntries;
        this->numberOfNamePointers  = copy.numberOfNamePointers;
        this->exportAddressTableRVA = copy.exportAddressTableRVA;
        this->namePointerRVA        = copy.namePointerRVA;
        this->ordinalTableRVA       = copy.ordinalTableRVA;
        this->name                  = copy.name;
        this->entries               = copy.entries;
      }


      PeExportDirectory::~PeExportDirectory() {
      }


      PeExportDirectory &PeExportDirectory::operator=(const PeExportDirectory& copy) {
        if (this == &copy)
            return *this;
        this->exportFlags           = copy.exportFlags;
        this->timeDateStamp         = copy.timeDateStamp;
        this->majorVersion          = copy.majorVersion;
        this->minorVersion          = copy.minorVersion;
        this->nameRVA               = copy.nameRVA;
        this->ordinalBase           = copy.ordinalBase;
        this->addressTableEntries   = copy.addressTableEntries;
        this->numberOfNamePointers  = copy.numberOfNamePointers;
        this->exportAddressTableRVA = copy.exportAddressTableRVA;
        this->namePointerRVA        = copy.namePointerRVA;
        this->ordinalTableRVA       = copy.ordinalTableRVA;
        this->name                  = copy.name;
        this->entries               = copy.entries;
        return *this;
      }


      void PeExportDirectory::parse(const triton::uint8* raw) {
        std::memcpy(&exportFlags, raw, 40);
      }

      triton::uint32 PeExportDirectory::getExportFlags(void) const {
        return this->exportFlags;
      }


      triton::uint32 PeExportDirectory::getTimeDateStamp(void) const {
        return this->timeDateStamp;
      }


      triton::uint16 PeExportDirectory::getMajorVersion(void) const {
        return this->majorVersion;
      }


      triton::uint16 PeExportDirectory::getMinorVersion(void) const {
        return this->minorVersion;
      }


      triton::uint32 PeExportDirectory::getNameRVA(void) const {
        return this->nameRVA;
      }


      triton::uint32 PeExportDirectory::getOrdinalBase(void) const {
        return this->ordinalBase;
      }


      triton::uint32 PeExportDirectory::getAddressTableEntries(void) const {
        return this->addressTableEntries;
      }


      triton::uint32 PeExportDirectory::getNumberOfNamePointers(void) const {
        return this->numberOfNamePointers;
      }


      triton::uint32 PeExportDirectory::getExportAddressTableRVA(void) const {
        return this->exportAddressTableRVA;
      }


      triton::uint32 PeExportDirectory::getNamePointerRVA(void) const {
        return this->namePointerRVA;
      }


      triton::uint32 PeExportDirectory::getOrdinalTableRVA(void) const {
        return this->ordinalTableRVA;
      }


      void PeExportDirectory::setName(const std::string &name) {
        this->name = name;
      }


      std::string PeExportDirectory::getName(void) const {
        return this->name;
      }


      void PeExportDirectory::addEntry(const PeExportEntry &entry) {
        entries.push_back(entry);
      }

      std::vector<PeExportEntry> PeExportDirectory::getEntries(void) const {
        return this->entries;
      }

    }; /* pe namespace */
  }; /* format namespace */
}; /* triton namespace */


