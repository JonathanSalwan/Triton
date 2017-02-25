//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstdio>

#include <triton/exceptions.hpp>
#include <triton/peImportDirectory.hpp>



namespace triton {
  namespace format {
    namespace pe {

      PeImportDirectory::PeImportDirectory() {
        this->st.importLookupTableRVA   = 0;
        this->st.timeDateStamp          = 0;
        this->st.forwarderChain         = 0;
        this->st.nameRVA                = 0;
        this->st.importAddressTableRVA  = 0;
      }


      PeImportDirectory::PeImportDirectory(const PeImportDirectory& copy) {
        this->st.importLookupTableRVA   = copy.st.importLookupTableRVA;
        this->st.timeDateStamp          = copy.st.timeDateStamp;
        this->st.forwarderChain         = copy.st.forwarderChain;
        this->st.nameRVA                = copy.st.nameRVA;
        this->st.importAddressTableRVA  = copy.st.importAddressTableRVA;
        this->name                      = copy.name;
        this->entries                   = copy.entries;
      }


      PeImportDirectory::~PeImportDirectory() {
      }


      PeImportDirectory& PeImportDirectory::operator=(const PeImportDirectory& copy) {
        if (this == &copy)
          return *this;

        this->st.importLookupTableRVA   = copy.st.importLookupTableRVA;
        this->st.timeDateStamp          = copy.st.timeDateStamp;
        this->st.forwarderChain         = copy.st.forwarderChain;
        this->st.nameRVA                = copy.st.nameRVA;
        this->st.importAddressTableRVA  = copy.st.importAddressTableRVA;
        this->name                      = copy.name;
        this->entries                   = copy.entries;

        return *this;
      }


      bool PeImportDirectory::parse(const triton::uint8* raw) {
        std::memcpy(&this->st, raw, sizeof(this->st));
        return (this->st.importLookupTableRVA ? true : false);
      }


      triton::uint32 PeImportDirectory::getImportLookupTableRVA(void) const {
        return this->st.importLookupTableRVA;
      }


      triton::uint32 PeImportDirectory::getTimeDateStamp(void) const {
        return this->st.timeDateStamp;
      }


      triton::uint32 PeImportDirectory::getForwarderChain(void) const {
        return this->st.forwarderChain;
      }


      triton::uint32 PeImportDirectory::getNameRVA(void) const {
        return this->st.nameRVA;
      }


      triton::uint32 PeImportDirectory::getImportAddressTableRVA(void) const {
        return this->st.importAddressTableRVA;
      }


      void PeImportDirectory::setName(const std::string& name) {
        this->name = name;
      }


      const std::string& PeImportDirectory::getName(void) const {
        return this->name;
      }


      void PeImportDirectory::addEntry(const PeImportLookup& entry) {
        this->entries.push_back(entry);
      }


      const std::vector<PeImportLookup>& PeImportDirectory::getEntries(void) const {
        return this->entries;
      }

    }; /* pe namespace */
  }; /* format namespace */
}; /* triton namespace */

