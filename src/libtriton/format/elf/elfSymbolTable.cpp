//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <cstdio>
#include <stdexcept>

#include <elfSymbolTable.hpp>



namespace triton {
  namespace format {
    namespace elf {

      ELFSymbolTable::ELFSymbolTable() {
        this->idxname = 0;
        this->info    = 0;
        this->other   = 0;
        this->shndx   = 0;
        this->value   = 0;
        this->size    = 0;
      }


      ELFSymbolTable::ELFSymbolTable(const ELFSymbolTable& copy) {
        this->idxname = copy.idxname;
        this->name    = copy.name;
        this->info    = copy.info;
        this->other   = copy.other;
        this->shndx   = copy.shndx;
        this->value   = copy.value;
        this->size    = copy.size;
      }


      ELFSymbolTable::~ELFSymbolTable() {
      }


      void ELFSymbolTable::operator=(const ELFSymbolTable& copy) {
        this->idxname = copy.idxname;
        this->name    = copy.name;
        this->info    = copy.info;
        this->other   = copy.other;
        this->shndx   = copy.shndx;
        this->value   = copy.value;
        this->size    = copy.size;
      }


      triton::uint32 ELFSymbolTable::parse(const triton::uint8* raw, triton::uint8 EIClass) {
        triton::format::elf::Elf32_Sym_t sym32;
        triton::format::elf::Elf64_Sym_t sym64;

        switch (EIClass) {
          case triton::format::elf::ELFCLASS32:
            memcpy(&sym32, raw, sizeof(triton::format::elf::Elf32_Sym_t));
            this->idxname = sym32.st_name;
            this->info    = sym32.st_info;
            this->other   = sym32.st_other;
            this->shndx   = sym32.st_shndx;
            this->value   = sym32.st_value;
            this->size    = sym32.st_size;
            return sizeof(triton::format::elf::Elf32_Sym_t);

          case triton::format::elf::ELFCLASS64:
            memcpy(&sym64, raw, sizeof(triton::format::elf::Elf64_Sym_t));
            this->idxname = sym64.st_name;
            this->info    = sym64.st_info;
            this->other   = sym64.st_other;
            this->shndx   = sym64.st_shndx;
            this->value   = sym64.st_value;
            this->size    = sym64.st_size;
            return sizeof(triton::format::elf::Elf64_Sym_t);

          default:
            throw std::runtime_error("ELFSymbolTable::parse(): Invalid EI_CLASS.");
        }
        return 0;
      }


      triton::uint32 ELFSymbolTable::getIdxname(void) const {
        return this->idxname;
      }


      const std::string& ELFSymbolTable::getName(void) const {
        return this->name;
      }


      void ELFSymbolTable::setName(const triton::uint8 *str) {
        this->setName(std::string(reinterpret_cast<const char*>(str)));
      }


      void ELFSymbolTable::setName(const std::string& name) {
        this->name = name;
      }


      triton::uint8 ELFSymbolTable::getInfo(void) const {
        return this->info;
      }


      triton::uint8 ELFSymbolTable::getOther(void) const {
        return this->other;
      }


      triton::uint16 ELFSymbolTable::getShndx(void) const {
        return this->shndx;
      }


      triton::uint64 ELFSymbolTable::getValue(void) const {
        return this->value;
      }


      triton::uint64 ELFSymbolTable::getSize(void) const {
        return this->size;
      }

    }; /* elf namespace */
  }; /* format namespace */
}; /* triton namespace */

