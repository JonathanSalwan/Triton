//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstdio>

#include <triton/exceptions.hpp>
#include <triton/peExportDirectory.hpp>



namespace triton {
  namespace format {
    namespace pe {

      PeExportDirectory::PeExportDirectory() {
        this->st.exportFlags            = 0;
        this->st.timeDateStamp          = 0;
        this->st.majorVersion           = 0;
        this->st.minorVersion           = 0;
        this->st.nameRVA                = 0;
        this->st.ordinalBase            = 0;
        this->st.addressTableEntries    = 0;
        this->st.numberOfNamePointers   = 0;
        this->st.exportAddressTableRVA  = 0;
        this->st.namePointerRVA         = 0;
        this->st.ordinalTableRVA        = 0;
      }


      PeExportDirectory::PeExportDirectory(const PeExportDirectory& copy) {
        this->st.exportFlags            = copy.st.exportFlags;
        this->st.timeDateStamp          = copy.st.timeDateStamp;
        this->st.majorVersion           = copy.st.majorVersion;
        this->st.minorVersion           = copy.st.minorVersion;
        this->st.nameRVA                = copy.st.nameRVA;
        this->st.ordinalBase            = copy.st.ordinalBase;
        this->st.addressTableEntries    = copy.st.addressTableEntries;
        this->st.numberOfNamePointers   = copy.st.numberOfNamePointers;
        this->st.exportAddressTableRVA  = copy.st.exportAddressTableRVA;
        this->st.namePointerRVA         = copy.st.namePointerRVA;
        this->st.ordinalTableRVA        = copy.st.ordinalTableRVA;
        this->name                      = copy.name;
        this->entries                   = copy.entries;
      }


      PeExportDirectory::~PeExportDirectory() {
      }


      PeExportDirectory& PeExportDirectory::operator=(const PeExportDirectory& copy) {
        if (this == &copy)
            return *this;

        this->st.exportFlags            = copy.st.exportFlags;
        this->st.timeDateStamp          = copy.st.timeDateStamp;
        this->st.majorVersion           = copy.st.majorVersion;
        this->st.minorVersion           = copy.st.minorVersion;
        this->st.nameRVA                = copy.st.nameRVA;
        this->st.ordinalBase            = copy.st.ordinalBase;
        this->st.addressTableEntries    = copy.st.addressTableEntries;
        this->st.numberOfNamePointers   = copy.st.numberOfNamePointers;
        this->st.exportAddressTableRVA  = copy.st.exportAddressTableRVA;
        this->st.namePointerRVA         = copy.st.namePointerRVA;
        this->st.ordinalTableRVA        = copy.st.ordinalTableRVA;
        this->name                      = copy.name;
        this->entries                   = copy.entries;

        return *this;
      }


      void PeExportDirectory::parse(const triton::uint8* raw) {
        std::memcpy(&this->st, raw, sizeof(this->st));
      }


      triton::uint32 PeExportDirectory::getExportFlags(void) const {
        return this->st.exportFlags;
      }


      triton::uint32 PeExportDirectory::getTimeDateStamp(void) const {
        return this->st.timeDateStamp;
      }


      triton::uint16 PeExportDirectory::getMajorVersion(void) const {
        return this->st.majorVersion;
      }


      triton::uint16 PeExportDirectory::getMinorVersion(void) const {
        return this->st.minorVersion;
      }


      triton::uint32 PeExportDirectory::getNameRVA(void) const {
        return this->st.nameRVA;
      }


      triton::uint32 PeExportDirectory::getOrdinalBase(void) const {
        return this->st.ordinalBase;
      }


      triton::uint32 PeExportDirectory::getAddressTableEntries(void) const {
        return this->st.addressTableEntries;
      }


      triton::uint32 PeExportDirectory::getNumberOfNamePointers(void) const {
        return this->st.numberOfNamePointers;
      }


      triton::uint32 PeExportDirectory::getExportAddressTableRVA(void) const {
        return this->st.exportAddressTableRVA;
      }


      triton::uint32 PeExportDirectory::getNamePointerRVA(void) const {
        return this->st.namePointerRVA;
      }


      triton::uint32 PeExportDirectory::getOrdinalTableRVA(void) const {
        return this->st.ordinalTableRVA;
      }


      void PeExportDirectory::setName(const std::string& name) {
        this->name = name;
      }


      const std::string& PeExportDirectory::getName(void) const {
        return this->name;
      }


      void PeExportDirectory::addEntry(const PeExportEntry& entry) {
        this->entries.push_back(entry);
      }


      const std::vector<PeExportEntry>& PeExportDirectory::getEntries(void) const {
        return this->entries;
      }

    }; /* pe namespace */
  }; /* format namespace */
}; /* triton namespace */


