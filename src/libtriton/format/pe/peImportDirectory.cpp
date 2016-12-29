//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstdio>

#include <peImportDirectory.hpp>
#include <exceptions.hpp>



namespace triton {
  namespace format {
    namespace pe {

      PeImportDirectory::PeImportDirectory() {
        this->importLookupTableRVA = 0;
        this->timeDateStamp = 0;
        this->forwarderChain = 0;
        this->nameRVA = 0;
        this->importAddressTableRVA = 0;
      }


      PeImportDirectory::PeImportDirectory(const PeImportDirectory& copy) {
        this->importLookupTableRVA  = copy.importLookupTableRVA;
        this->timeDateStamp         = copy.timeDateStamp;
        this->forwarderChain        = copy.forwarderChain;
        this->nameRVA               = copy.nameRVA;
        this->importAddressTableRVA = copy.importAddressTableRVA;
        this->name                  = copy.name;
        this->entries               = copy.entries;
      }


      PeImportDirectory::~PeImportDirectory() {
      }


      PeImportDirectory &PeImportDirectory::operator=(const PeImportDirectory& copy) {
        if (this == &copy)
            return *this;
        this->importLookupTableRVA  = copy.importLookupTableRVA;
        this->timeDateStamp         = copy.timeDateStamp;
        this->forwarderChain        = copy.forwarderChain;
        this->nameRVA               = copy.nameRVA;
        this->importAddressTableRVA = copy.importAddressTableRVA;
        this->name                  = copy.name;
        this->entries               = copy.entries;
        return *this;
      }


      bool PeImportDirectory::parse(const triton::uint8* raw) {
        std::memcpy(&importLookupTableRVA, raw, 20);
        return this->importLookupTableRVA;
      }

      triton::uint32 PeImportDirectory::getImportLookupTableRVA(void) const {
        return this->importLookupTableRVA;
      }


      triton::uint32 PeImportDirectory::getTimeDateStamp(void) const {
        return this->timeDateStamp;
      }


      triton::uint32 PeImportDirectory::getForwarderChain(void) const {
        return this->forwarderChain;
      }


      triton::uint32 PeImportDirectory::getNameRVA(void) const {
        return this->nameRVA;
      }


      triton::uint32 PeImportDirectory::getImportAddressTableRVA(void) const {
        return this->importAddressTableRVA;
      }


      void PeImportDirectory::setName(std::string name) {
        this->name = name;
      }


      std::string PeImportDirectory::getName(void) const {
        return this->name;
      }


      void PeImportDirectory::addEntry(const PeImportLookup &entry) {
        entries.push_back(entry);
      }


      const std::vector<PeImportLookup> &PeImportDirectory::getEntries(void) const {
        return this->entries;
      }


    }; /* pe namespace */
  }; /* format namespace */
}; /* triton namespace */


