//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <cstdio>
#include <stdexcept>

#include <elfHeader.hpp>



namespace triton {
  namespace format {
    namespace elf {

      ELFHeader::ELFHeader() {
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

        memset(this->ident, 0x00, sizeof(this->ident));
      }


      ELFHeader::ELFHeader(const ELFHeader& copy) {
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

        memcpy(this->ident, copy.ident, sizeof(this->ident));
      }


      ELFHeader::~ELFHeader() {
      }


      void ELFHeader::operator=(const ELFHeader& copy) {
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

        memcpy(this->ident, copy.ident, sizeof(this->ident));
      }


      triton::uint32 ELFHeader::parse(const triton::uint8* raw) {
        triton::format::elf::Elf32_Ehdr_t ehdr32;
        triton::format::elf::Elf64_Ehdr_t ehdr64;

        // Copy the ident field
        memcpy(this->ident, raw, sizeof(this->ident));

        // Only support little-endian
        if (this->getEIData() != triton::format::elf::ELFDATA2LSB)
            throw std::runtime_error("ELFHeader::parse(): Unsupported endianness (EI_DATA).");

        switch (this->getEIClass()) {
          case triton::format::elf::ELFCLASS32:
            memcpy(&ehdr32, raw, sizeof(triton::format::elf::Elf32_Ehdr_t));
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
            memcpy(&ehdr64, raw, sizeof(triton::format::elf::Elf64_Ehdr_t));
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
            throw std::runtime_error("ELFHeader::parse(): Invalid EI_CLASS.");
        }
        return 0;
      }


      triton::uint8 ELFHeader::getEIClass(void) const {
        return this->ident[4];
      }


      triton::uint8 ELFHeader::getEIData(void) const {
        return this->ident[5];
      }


      triton::uint16 ELFHeader::getType(void) const {
        return this->type;
      }


      triton::uint16 ELFHeader::getMachine(void) const {
        return this->machine;
      }


      triton::uint32 ELFHeader::getVersion(void) const {
        return this->version;
      }


      triton::uint64 ELFHeader::getEntry(void) const {
        return this->entry;
      }


      triton::uint64 ELFHeader::getPhoff(void) const {
        return this->phoff;
      }


      triton::uint64 ELFHeader::getShoff(void) const {
        return this->shoff;
      }


      triton::uint32 ELFHeader::getFlags(void) const {
        return this->flags;
      }


      triton::uint16 ELFHeader::getEhsize(void) const {
        return this->ehsize;
      }


      triton::uint16 ELFHeader::getPhentsize(void) const {
        return this->phentsize;
      }


      triton::uint16 ELFHeader::getPhnum(void) const {
        return this->phnum;
      }


      triton::uint16 ELFHeader::getShentsize(void) const {
        return this->shentsize;
      }


      triton::uint16 ELFHeader::getShnum(void) const {
        return this->shnum;
      }


      triton::uint16 ELFHeader::getShstrndx(void) const {
        return this->shstrndx;
      }


      triton::uint32 ELFHeader::getMaxHeaderSize() const {
        return sizeof(struct triton::format::elf::Elf64_Ehdr);
      }

    }; /* elf namespace */
  }; /* format namespace */
}; /* triton namespace */

