//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstdio>

#include <triton/elfHeader.hpp>
#include <triton/exceptions.hpp>



namespace triton {
  namespace format {
    namespace elf {

      ElfHeader::ElfHeader() {
        this->type      = 0;
        this->machine   = 0;
        this->version   = 0;
        this->entry     = 0;
        this->phoff     = 0;
        this->shoff     = 0;
        this->flags     = 0;
        this->ehsize    = 0;
        this->phentsize = 0;
        this->phnum     = 0;
        this->shentsize = 0;
        this->shnum     = 0;
        this->shstrndx  = 0;

        std::memset(this->ident, 0x00, sizeof(this->ident));
      }


      ElfHeader::ElfHeader(const ElfHeader& copy) {
        this->type      = copy.type;
        this->machine   = copy.machine;
        this->version   = copy.version;
        this->entry     = copy.entry;
        this->phoff     = copy.phoff;
        this->shoff     = copy.shoff;
        this->flags     = copy.flags;
        this->ehsize    = copy.ehsize;
        this->phentsize = copy.phentsize;
        this->phnum     = copy.phnum;
        this->shentsize = copy.shentsize;
        this->shnum     = copy.shnum;
        this->shstrndx  = copy.shstrndx;

        std::memcpy(this->ident, copy.ident, sizeof(this->ident));
      }


      ElfHeader::~ElfHeader() {
      }


      void ElfHeader::operator=(const ElfHeader& copy) {
        this->type      = copy.type;
        this->machine   = copy.machine;
        this->version   = copy.version;
        this->entry     = copy.entry;
        this->phoff     = copy.phoff;
        this->shoff     = copy.shoff;
        this->flags     = copy.flags;
        this->ehsize    = copy.ehsize;
        this->phentsize = copy.phentsize;
        this->phnum     = copy.phnum;
        this->shentsize = copy.shentsize;
        this->shnum     = copy.shnum;
        this->shstrndx  = copy.shstrndx;

        std::memcpy(this->ident, copy.ident, sizeof(this->ident));
      }


      triton::uint32 ElfHeader::parse(const triton::uint8* raw) {
        triton::format::elf::Elf32_Ehdr_t ehdr32;
        triton::format::elf::Elf64_Ehdr_t ehdr64;

        // Copy the ident field
        std::memcpy(this->ident, raw, sizeof(this->ident));

        // Only support little-endian
        if (this->getEIData() != triton::format::elf::ELFDATA2LSB)
            throw triton::exceptions::Elf("ElfHeader::parse(): Unsupported endianness (EI_DATA).");

        switch (this->getEIClass()) {
          case triton::format::elf::ELFCLASS32:
            std::memcpy(&ehdr32, raw, sizeof(triton::format::elf::Elf32_Ehdr_t));
            this->type      = ehdr32.e_type;
            this->machine   = ehdr32.e_machine;
            this->version   = ehdr32.e_version;
            this->entry     = ehdr32.e_entry;
            this->phoff     = ehdr32.e_phoff;
            this->shoff     = ehdr32.e_shoff;
            this->flags     = ehdr32.e_flags;
            this->ehsize    = ehdr32.e_ehsize;
            this->phentsize = ehdr32.e_phentsize;
            this->phnum     = ehdr32.e_phnum;
            this->shentsize = ehdr32.e_shentsize;
            this->shnum     = ehdr32.e_shnum;
            this->shstrndx  = ehdr32.e_shstrndx;
            return sizeof(triton::format::elf::Elf32_Ehdr_t);

          case triton::format::elf::ELFCLASS64:
            std::memcpy(&ehdr64, raw, sizeof(triton::format::elf::Elf64_Ehdr_t));
            this->type      = ehdr64.e_type;
            this->machine   = ehdr64.e_machine;
            this->version   = ehdr64.e_version;
            this->entry     = ehdr64.e_entry;
            this->phoff     = ehdr64.e_phoff;
            this->shoff     = ehdr64.e_shoff;
            this->flags     = ehdr64.e_flags;
            this->ehsize    = ehdr64.e_ehsize;
            this->phentsize = ehdr64.e_phentsize;
            this->phnum     = ehdr64.e_phnum;
            this->shentsize = ehdr64.e_shentsize;
            this->shnum     = ehdr64.e_shnum;
            this->shstrndx  = ehdr64.e_shstrndx;
            return sizeof(triton::format::elf::Elf64_Ehdr_t);

          default:
            throw triton::exceptions::Elf("ElfHeader::parse(): Invalid EI_CLASS.");
        }
        return 0;
      }


      triton::uint8 ElfHeader::getEIClass(void) const {
        return this->ident[4];
      }


      triton::uint8 ElfHeader::getEIData(void) const {
        return this->ident[5];
      }


      triton::uint16 ElfHeader::getType(void) const {
        return this->type;
      }


      triton::uint16 ElfHeader::getMachine(void) const {
        return this->machine;
      }


      triton::uint32 ElfHeader::getVersion(void) const {
        return this->version;
      }


      triton::uint64 ElfHeader::getEntry(void) const {
        return this->entry;
      }


      triton::uint64 ElfHeader::getPhoff(void) const {
        return this->phoff;
      }


      triton::uint64 ElfHeader::getShoff(void) const {
        return this->shoff;
      }


      triton::uint32 ElfHeader::getFlags(void) const {
        return this->flags;
      }


      triton::uint16 ElfHeader::getEhsize(void) const {
        return this->ehsize;
      }


      triton::uint16 ElfHeader::getPhentsize(void) const {
        return this->phentsize;
      }


      triton::uint16 ElfHeader::getPhnum(void) const {
        return this->phnum;
      }


      triton::uint16 ElfHeader::getShentsize(void) const {
        return this->shentsize;
      }


      triton::uint16 ElfHeader::getShnum(void) const {
        return this->shnum;
      }


      triton::uint16 ElfHeader::getShstrndx(void) const {
        return this->shstrndx;
      }


      triton::uint32 ElfHeader::getMaxHeaderSize() const {
        return sizeof(struct triton::format::elf::Elf64_Ehdr);
      }

    }; /* elf namespace */
  }; /* format namespace */
}; /* triton namespace */

