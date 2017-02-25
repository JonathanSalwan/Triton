//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstdio>

#include <triton/elfProgramHeader.hpp>
#include <triton/exceptions.hpp>



namespace triton {
  namespace format {
    namespace elf {

      ElfProgramHeader::ElfProgramHeader() {
        this->type    = 0;
        this->flags   = 0;
        this->offset  = 0;
        this->vaddr   = 0;
        this->paddr   = 0;
        this->filesz  = 0;
        this->memsz   = 0;
        this->align   = 0;
      }


      ElfProgramHeader::ElfProgramHeader(const ElfProgramHeader& copy) {
        this->type    = copy.type;
        this->flags   = copy.flags;
        this->offset  = copy.offset;
        this->vaddr   = copy.vaddr;
        this->paddr   = copy.paddr;
        this->filesz  = copy.filesz;
        this->memsz   = copy.memsz;
        this->align   = copy.align;
      }


      ElfProgramHeader::~ElfProgramHeader() {
      }


      void ElfProgramHeader::operator=(const ElfProgramHeader& copy) {
        this->type    = copy.type;
        this->flags   = copy.flags;
        this->offset  = copy.offset;
        this->vaddr   = copy.vaddr;
        this->paddr   = copy.paddr;
        this->filesz  = copy.filesz;
        this->memsz   = copy.memsz;
        this->align   = copy.align;
      }


      triton::uint32 ElfProgramHeader::parse(const triton::uint8* raw, triton::uint8 EIClass) {
        triton::format::elf::Elf32_Phdr_t phdr32;
        triton::format::elf::Elf64_Phdr_t phdr64;

        switch (EIClass) {
          case triton::format::elf::ELFCLASS32:
            std::memcpy(&phdr32, raw, sizeof(triton::format::elf::Elf32_Phdr_t));
            this->type    = phdr32.p_type;
            this->flags   = phdr32.p_flags;
            this->offset  = phdr32.p_offset;
            this->vaddr   = phdr32.p_vaddr;
            this->paddr   = phdr32.p_paddr;
            this->filesz  = phdr32.p_filesz;
            this->memsz   = phdr32.p_memsz;
            this->align   = phdr32.p_align;
            return sizeof(triton::format::elf::Elf32_Phdr_t);

          case triton::format::elf::ELFCLASS64:
            std::memcpy(&phdr64, raw, sizeof(triton::format::elf::Elf64_Phdr_t));
            this->type    = phdr64.p_type;
            this->flags   = phdr64.p_flags;
            this->offset  = phdr64.p_offset;
            this->vaddr   = phdr64.p_vaddr;
            this->paddr   = phdr64.p_paddr;
            this->filesz  = phdr64.p_filesz;
            this->memsz   = phdr64.p_memsz;
            this->align   = phdr64.p_align;
            return sizeof(triton::format::elf::Elf64_Phdr_t);

          default:
            throw triton::exceptions::Elf("ElfProgramHeader::parse(): Invalid EI_CLASS.");
        }
        return 0;
      }


      triton::uint32 ElfProgramHeader::getType(void) const {
        return this->type;
      }


      triton::uint32 ElfProgramHeader::getFlags(void) const {
        return this->flags;
      }


      triton::uint64 ElfProgramHeader::getOffset(void) const {
        return this->offset;
      }


      triton::uint64 ElfProgramHeader::getVaddr(void) const {
        return this->vaddr;
      }


      triton::uint64 ElfProgramHeader::getPaddr(void) const {
        return this->paddr;
      }


      triton::uint64 ElfProgramHeader::getFilesz(void) const {
        return this->filesz;
      }


      triton::uint64 ElfProgramHeader::getMemsz(void) const {
        return this->memsz;
      }


      triton::uint64 ElfProgramHeader::getAlign(void) const {
        return this->align;
      }

    }; /* elf namespace */
  }; /* format namespace */
}; /* triton namespace */

