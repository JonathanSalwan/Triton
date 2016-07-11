//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstdio>
#include <stdexcept>

#include <elfDynamicTable.hpp>



namespace triton {
  namespace format {
    namespace elf {

      ELFDynamicTable::ELFDynamicTable() {
        this->tag   = 0;
        this->value = 0;
      }


      ELFDynamicTable::ELFDynamicTable(const ELFDynamicTable& copy) {
        this->tag   = copy.tag;
        this->value = copy.value;
      }


      ELFDynamicTable::~ELFDynamicTable() {
      }


      void ELFDynamicTable::operator=(const ELFDynamicTable& copy) {
        this->tag   = copy.tag;
        this->value = copy.value;
      }


      triton::uint32 ELFDynamicTable::parse(const triton::uint8* raw, triton::uint8 EIClass) {
        triton::format::elf::Elf32_Dyn_t dyn32;
        triton::format::elf::Elf64_Dyn_t dyn64;

        switch (EIClass) {
          case triton::format::elf::ELFCLASS32:
            memcpy(&dyn32, raw, sizeof(triton::format::elf::Elf32_Dyn_t));
            this->tag   = dyn32.d_tag;
            this->value = dyn32.d_val;
            return sizeof(triton::format::elf::Elf32_Dyn_t);

          case triton::format::elf::ELFCLASS64:
            memcpy(&dyn64, raw, sizeof(triton::format::elf::Elf64_Dyn_t));
            this->tag   = dyn64.d_tag;
            this->value = dyn64.d_val;
            return sizeof(triton::format::elf::Elf64_Dyn_t);

          default:
            throw std::runtime_error("ELFDynamicTable::parse(): Invalid EI_CLASS.");
        }
        return 0;
      }


      triton::sint64 ELFDynamicTable::getTag(void) const {
        return this->tag;
      }


      triton::uint64 ELFDynamicTable::getValue(void) const {
        return this->value;
      }

    }; /* elf namespace */
  }; /* format namespace */
}; /* triton namespace */

