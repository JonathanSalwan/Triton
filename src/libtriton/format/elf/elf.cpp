//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <cstdio>
#include <stdexcept>

#include <elf.hpp>



namespace triton {
  namespace format {
    namespace elf {

      ELF::ELF(const std::string& path) {
        this->path      = path;
        this->raw       = nullptr;
        this->totalSize = 0;

        this->open();
        this->parse();
        this->initMemoryMapping();
      }


      ELF::~ELF() {
        delete[] this->raw;
      }


      void ELF::open(void) {
        FILE* fd = nullptr;

        // Open the file
        fd = fopen(this->path.c_str(), "rb");
        if (fd == nullptr)
          throw std::runtime_error("ELF::open(): Cannot open the binary file.");

        // Get the binary size
        fseek(fd, 0, SEEK_END);
        this->totalSize = ftell(fd);
        rewind(fd);

        this->raw = new triton::uint8[this->totalSize];
        if(!this->raw)
          throw std::runtime_error("ELF::open(): Not enough memory.");

        // Read only the magic number
        if (fread(this->raw, 1, this->totalSize, fd) != this->totalSize)
          throw std::runtime_error("ELF::open(): Cannot read the file binary.");

        // Close the file
        fclose(fd);
      }


      void ELF::parse(void) {
        triton::uint8  EIClass  = triton::format::elf::ELFCLASSNONE;
        triton::uint64 phOffset = 0;
        triton::uint16 phNum    = 0;
        triton::uint16 phSize   = 0;
        triton::uint64 shOffset = 0;
        triton::uint16 shNum    = 0;
        triton::uint16 shSize   = 0;
        triton::uint16 shstrndx = 0;
        triton::uint64 strtable = 0;

        // Parse the ELF Header
        if (this->totalSize < this->elfHeader.getMaxHeaderSize())
          throw std::runtime_error("ELF::parse(): The ELF Header of the binary file is corrupted.");

        this->elfHeader.parse(this->raw);

        // Parse Program Headers
        EIClass  = this->elfHeader.getEIClass();
        phOffset = this->elfHeader.getPhoff();
        phNum    = this->elfHeader.getPhnum();
        phSize   = this->elfHeader.getPhentsize();

        if (this->totalSize < (phOffset + (phNum * phSize)))
          throw std::runtime_error("ELF::parse(): Some ELF Program Headers of the binary file are corrupted.");

        for (triton::uint16 entry = 0; entry < phNum; entry++) {
          triton::format::elf::ELFProgramHeader phdr;
          phdr.parse((this->raw + (phOffset + (entry * phSize))), EIClass);
          this->elfProgramHeaders.push_back(phdr);
        }

        // Parse Section Headers - Stage 1 (entities parsing)
        shOffset = this->elfHeader.getShoff();
        shNum    = this->elfHeader.getShnum();
        shSize   = this->elfHeader.getShentsize();

        if (this->totalSize < (shOffset + (shNum * shSize)))
          throw std::runtime_error("ELF::parse(): Some ELF Section Headers of the binary file are corrupted.");

        for (triton::uint16 entry = 0; entry < shNum; entry++) {
          triton::format::elf::ELFSectionHeader shdr;
          shdr.parse((this->raw + (shOffset + (entry * shSize))), EIClass);
          this->elfSectionHeaders.push_back(shdr);
        }

        // Parse Section Headers - Stage 2 (section name setup)
        shstrndx = this->elfHeader.getShstrndx();
        if (shstrndx != triton::format::elf::SHN_XINDEX) {
          if (shstrndx >= this->elfSectionHeaders.size())
            throw std::runtime_error("ELF::parse(): The string table index of the binary file is corrupted.");

          strtable = this->elfSectionHeaders[shstrndx].getOffset();
          for (auto it = this->elfSectionHeaders.begin(); it != this->elfSectionHeaders.end(); it++) {
            it->setName(this->raw + strtable + it->getIdxname());
          }
        }
      }


      void ELF::initMemoryMapping(void) {
        for (auto it = this->elfProgramHeaders.begin(); it != this->elfProgramHeaders.end(); it++) {
          triton::format::MemoryMapping area(this->raw);

          if (this->totalSize < (it->getOffset() + it->getFilesz()))
            throw std::runtime_error("ELF::parse(): Some ELF Section Headers of the binary file are corrupted.");

          area.setOffset(it->getOffset());
          area.setSize(it->getFilesz());
          area.setVirtualAddress(it->getVaddr());

          this->memoryMapping.push_back(area);
        }
      }


      const std::string& ELF::getPath(void) const {
        return this->path;
      }


      const std::list<triton::format::MemoryMapping>& ELF::getMemoryMapping(void) const {
        return this->memoryMapping;
      }



    }; /* elf namespace */
  }; /* format namespace */
}; /* triton namespace */
