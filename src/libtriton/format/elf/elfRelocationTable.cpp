//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstdio>

#include <triton/elfRelocationTable.hpp>
#include <triton/exceptions.hpp>



namespace triton {
  namespace format {
    namespace elf {

      ElfRelocationTable::ElfRelocationTable() {
        this->addendFlag = false;
        this->offset     = 0;
        this->info       = 0;
        this->addend     = 0;
        this->type       = 0;
        this->symidx     = 0;
      }


      ElfRelocationTable::ElfRelocationTable(const ElfRelocationTable& copy) {
        this->addendFlag = copy.addendFlag;
        this->offset     = copy.offset;
        this->info       = copy.info;
        this->addend     = copy.addend;
        this->type       = copy.type;
        this->symidx     = copy.symidx;
      }


      ElfRelocationTable::~ElfRelocationTable() {
      }


      void ElfRelocationTable::operator=(const ElfRelocationTable& copy) {
        this->addendFlag = copy.addendFlag;
        this->offset     = copy.offset;
        this->info       = copy.info;
        this->addend     = copy.addend;
        this->type       = copy.type;
        this->symidx     = copy.symidx;
      }


      triton::uint32 ElfRelocationTable::parseRel(const triton::uint8* raw, triton::uint8 EIClass) {
        triton::format::elf::Elf32_Rel_t rel32;
        triton::format::elf::Elf64_Rel_t rel64;

        switch (EIClass) {
          case triton::format::elf::ELFCLASS32:
            std::memcpy(&rel32, raw, sizeof(triton::format::elf::Elf32_Rel_t));
            this->addendFlag = false;
            this->offset     = rel32.r_offset;
            this->info       = rel32.r_info;
            this->addend     = 0;
            this->type       = rel32.r_info & 0xff;
            this->symidx     = rel32.r_info >> 8;
            return sizeof(triton::format::elf::Elf32_Rel_t);

          case triton::format::elf::ELFCLASS64:
            std::memcpy(&rel64, raw, sizeof(triton::format::elf::Elf64_Rel_t));
            this->addendFlag = false;
            this->offset     = rel64.r_offset;
            this->info       = rel64.r_info;
            this->addend     = 0;
            this->type       = rel64.r_info & 0xffffffff;
            this->symidx     = rel64.r_info >> 32;
            return sizeof(triton::format::elf::Elf64_Rel_t);

          default:
            throw triton::exceptions::Elf("ElfRelocationTable::parseRel(): Invalid EI_CLASS.");
        }
        return 0;
      }


      triton::uint32 ElfRelocationTable::parseRela(const triton::uint8* raw, triton::uint8 EIClass) {
        triton::format::elf::Elf32_Rela_t rela32;
        triton::format::elf::Elf64_Rela_t rela64;

        switch (EIClass) {
          case triton::format::elf::ELFCLASS32:
            std::memcpy(&rela32, raw, sizeof(triton::format::elf::Elf32_Rela_t));
            this->addendFlag = true;
            this->offset     = rela32.r_offset;
            this->info       = rela32.r_info;
            this->addend     = rela32.r_addend;
            this->type       = rela32.r_info & 0xff;
            this->symidx     = rela32.r_info >> 8;
            return sizeof(triton::format::elf::Elf32_Rela_t);

          case triton::format::elf::ELFCLASS64:
            std::memcpy(&rela64, raw, sizeof(triton::format::elf::Elf64_Rela_t));
            this->addendFlag = true;
            this->offset     = rela64.r_offset;
            this->info       = rela64.r_info;
            this->addend     = rela64.r_addend;
            this->type       = rela64.r_info & 0xffffffff;
            this->symidx     = rela64.r_info >> 32;
            return sizeof(triton::format::elf::Elf64_Rela_t);

          default:
            throw triton::exceptions::Elf("ElfRelocationTable::parseRela(): Invalid EI_CLASS.");
        }
        return 0;
      }


      bool ElfRelocationTable::isAddend(void) const {
        return this->addendFlag;
      }


      triton::uint64 ElfRelocationTable::getOffset(void) const {
        return this->offset;
      }


      triton::uint64 ElfRelocationTable::getInfo(void) const {
        return this->info;
      }


      triton::sint64 ElfRelocationTable::getAddend(void) const {
        return this->addend;
      }


      triton::uint64 ElfRelocationTable::getType(void) const {
        return this->type;
      }


      triton::uint64 ElfRelocationTable::getSymidx(void) const {
        return this->symidx;
      }

    }; /* elf namespace */
  }; /* format namespace */
}; /* triton namespace */

