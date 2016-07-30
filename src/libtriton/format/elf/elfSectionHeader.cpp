//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstdio>

#include <elfSectionHeader.hpp>
#include <exceptions.hpp>



namespace triton {
  namespace format {
    namespace elf {

      ELFSectionHeader::ELFSectionHeader() {
        this->idxname   = 0;
        this->type      = 0;
        this->flags     = 0;
        this->addr      = 0;
        this->offset    = 0;
        this->size      = 0;
        this->link      = 0;
        this->info      = 0;
        this->addralign = 0;
        this->entsize   = 0;
      }


      ELFSectionHeader::ELFSectionHeader(const ELFSectionHeader& copy) {
        this->idxname   = copy.idxname;
        this->name      = copy.name;
        this->type      = copy.type;
        this->flags     = copy.flags;
        this->addr      = copy.addr;
        this->offset    = copy.offset;
        this->size      = copy.size;
        this->link      = copy.link;
        this->info      = copy.info;
        this->addralign = copy.addralign;
        this->entsize   = copy.entsize;
      }


      ELFSectionHeader::~ELFSectionHeader() {
      }


      void ELFSectionHeader::operator=(const ELFSectionHeader& copy) {
        this->idxname   = copy.idxname;
        this->name      = copy.name;
        this->type      = copy.type;
        this->flags     = copy.flags;
        this->addr      = copy.addr;
        this->offset    = copy.offset;
        this->size      = copy.size;
        this->link      = copy.link;
        this->info      = copy.info;
        this->addralign = copy.addralign;
        this->entsize   = copy.entsize;
      }


      triton::uint32 ELFSectionHeader::parse(const triton::uint8* raw, triton::uint8 EIClass) {
        triton::format::elf::Elf32_Shdr_t shdr32;
        triton::format::elf::Elf64_Shdr_t shdr64;

        switch (EIClass) {
          case triton::format::elf::ELFCLASS32:
            memcpy(&shdr32, raw, sizeof(triton::format::elf::Elf32_Shdr_t));
            this->idxname   = shdr32.sh_name;
            this->type      = shdr32.sh_type;
            this->flags     = shdr32.sh_flags;
            this->addr      = shdr32.sh_addr;
            this->offset    = shdr32.sh_offset;
            this->size      = shdr32.sh_size;
            this->link      = shdr32.sh_link;
            this->info      = shdr32.sh_info;
            this->addralign = shdr32.sh_addralign;
            this->entsize   = shdr32.sh_entsize;
            return sizeof(triton::format::elf::Elf32_Shdr_t);

          case triton::format::elf::ELFCLASS64:
            memcpy(&shdr64, raw, sizeof(triton::format::elf::Elf64_Shdr_t));
            this->idxname   = shdr64.sh_name;
            this->type      = shdr64.sh_type;
            this->flags     = shdr64.sh_flags;
            this->addr      = shdr64.sh_addr;
            this->offset    = shdr64.sh_offset;
            this->size      = shdr64.sh_size;
            this->link      = shdr64.sh_link;
            this->info      = shdr64.sh_info;
            this->addralign = shdr64.sh_addralign;
            this->entsize   = shdr64.sh_entsize;
            return sizeof(triton::format::elf::Elf64_Shdr_t);

          default:
            throw triton::exceptions::ELF("ELFSectionHeader::parse(): Invalid EI_CLASS.");
        }
        return 0;
      }


      triton::uint32 ELFSectionHeader::getIdxname(void) const {
        return this->idxname;
      }


      const std::string& ELFSectionHeader::getName(void) const {
        return this->name;
      }


      void ELFSectionHeader::setName(const triton::uint8 *str) {
        this->setName(std::string(reinterpret_cast<const char*>(str)));
      }


      void ELFSectionHeader::setName(const std::string& name) {
        this->name = name;
      }


      triton::uint32 ELFSectionHeader::getType(void) const {
        return this->type;
      }


      triton::uint64 ELFSectionHeader::getFlags(void) const {
        return this->flags;
      }


      triton::uint64 ELFSectionHeader::getAddr(void) const {
        return this->addr;
      }


      triton::uint64 ELFSectionHeader::getOffset(void) const {
        return this->offset;
      }


      triton::uint64 ELFSectionHeader::getSize(void) const {
        return this->size;
      }


      triton::uint32 ELFSectionHeader::getLink(void) const {
        return this->link;
      }


      triton::uint32 ELFSectionHeader::getInfo(void) const {
        return this->info;
      }


      triton::uint64 ELFSectionHeader::getAddralign(void) const {
        return this->addralign;
      }


      triton::uint64 ELFSectionHeader::getEntsize(void) const {
        return this->entsize;
      }

    }; /* elf namespace */
  }; /* format namespace */
}; /* triton namespace */

