//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
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
        this->initDynamicTable();
        this->initSharedLibraries();
        this->initSymbolsTableViaProgramHeaders();  // .dyntab
        this->initSymbolsTableViaSectionHeaders();  // .symtab
        this->initRelTable();                       // DT_REL
        this->initRelaTable();                      // DT_RELA
        this->initJmprelTable();                    // DT_JMPREL
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


      bool ELF::parse(void) {
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
        if (this->totalSize < this->header.getMaxHeaderSize())
          throw std::runtime_error("ELF::parse(): The ELF Header of the binary file is corrupted.");

        this->header.parse(this->raw);

        // Parse Program Headers
        EIClass  = this->header.getEIClass();
        phOffset = this->header.getPhoff();
        phNum    = this->header.getPhnum();
        phSize   = this->header.getPhentsize();

        if (this->totalSize < (phOffset + (phNum * phSize))) {
          std::cerr << "Warning ELF::parse(): Some ELF Program Headers of the binary file are corrupted." << std::endl;
          return false;
        }

        for (triton::uint16 entry = 0; entry < phNum; entry++) {
          triton::format::elf::ELFProgramHeader phdr;
          phdr.parse((this->raw + (phOffset + (entry * phSize))), EIClass);
          this->programHeaders.push_back(phdr);
        }

        // Parse Section Headers - Stage 1 (entities parsing)
        shOffset = this->header.getShoff();
        shNum    = this->header.getShnum();
        shSize   = this->header.getShentsize();

        if (!shOffset)
          return false;

        if (this->totalSize < (shOffset + (shNum * shSize))) {
          std::cerr << "Warning ELF::parse(): Some ELF Section Headers of the binary file are corrupted." << std::endl;
          return false;
        }

        for (triton::uint16 entry = 0; entry < shNum; entry++) {
          triton::format::elf::ELFSectionHeader shdr;
          shdr.parse((this->raw + (shOffset + (entry * shSize))), EIClass);
          this->sectionHeaders.push_back(shdr);
        }

        // Parse Section Headers - Stage 2 (section name setup)
        shstrndx = this->header.getShstrndx();
        if (shstrndx != triton::format::elf::SHN_XINDEX) {
          if (shstrndx >= this->sectionHeaders.size()) {
            std::cerr << "Warning ELF::parse(): The string table index (shstrndx) of the binary file is corrupted." << std::endl;
            return false;
          }

          strtable = this->sectionHeaders[shstrndx].getOffset();
          for (auto it = this->sectionHeaders.begin(); it != this->sectionHeaders.end(); it++) {
            it->setName(this->raw + strtable + it->getIdxname());
          }
        }

        return true;
      }


      void ELF::initMemoryMapping(void) {
        for (auto it = this->programHeaders.begin(); it != this->programHeaders.end(); it++) {
          triton::format::MemoryMapping area(this->raw);

          if (this->totalSize < (it->getOffset() + it->getFilesz())) {
            std::cerr << "Warning ELF::initMemoryMapping(): Some ELF Program Headers of the binary file are corrupted." << std::endl;
            continue;
          }

          area.setOffset(it->getOffset());
          area.setSize(it->getFilesz());
          area.setVirtualAddress(it->getVaddr());

          this->memoryMapping.push_back(area);
        }
      }


      void ELF::initDynamicTable(void) {
        triton::uint64 dynOffset = 0;
        triton::uint64 dynSize   = 0;

        // Get the Dynamic Table offset.
        for (auto it = this->programHeaders.begin(); it != this->programHeaders.end(); it++) {
          if (it->getType() == triton::format::elf::PT_DYNAMIC) {
            dynOffset = it->getOffset();
            dynSize   = it->getFilesz();
          }
        }

        if (!dynOffset || this->totalSize < dynOffset + dynSize) {
          std::cerr << "Warning ELF::initDynamicTable(): The Dynamic Table offset of the binary file is corrupted." << std::endl;
          return;
        }

        // Parse Dynamic Table.
        for (triton::uint32 read = 0; read < dynSize;) {
          triton::format::elf::ELFDynamicTable dyn;
          read += dyn.parse(this->raw + dynOffset + read, this->header.getEIClass());
          this->dynamicTable.push_back(dyn);
        }
      }


      void ELF::initSharedLibraries(void) {
        triton::uint64 strTabOffset = 0;

        strTabOffset = this->getOffsetFromDTValue(triton::format::elf::DT_STRTAB);
        if (!strTabOffset || this->totalSize < strTabOffset) {
          std::cerr << "Warning ELF::initSharedLibraries(): The String Table offset of the binary file is corrupted." << std::endl;
          return;
        }

        for (auto it = this->dynamicTable.begin(); it != this->dynamicTable.end(); it++) {
          if (it->getTag() == triton::format::elf::DT_NEEDED) {
            this->sharedLibraries.push_back(reinterpret_cast<char*>(this->raw + strTabOffset + it->getValue()));
          }
        }
      }


      void ELF::initSymbolsTableViaProgramHeaders(void) {
        triton::uint64 strTabOffset = 0;
        triton::uint64 strTabSize   = 0;
        triton::uint64 symTabOffset = 0;
        triton::uint64 read         = 0;

        strTabOffset = this->getOffsetFromDTValue(triton::format::elf::DT_STRTAB);
        if (!strTabOffset || this->totalSize < strTabOffset) {
          std::cerr << "Warning ELF::initSymbolsTableViaProgramHeaders(): The String Table offset of the binary file is corrupted." << std::endl;
          return;
        }

        strTabSize = this->getDTValue(triton::format::elf::DT_STRSZ);
        if (!strTabSize || this->totalSize < strTabOffset + strTabSize) {
          std::cerr << "Warning ELF::initSymbolsTableViaProgramHeaders(): The String Table offset of the binary file is corrupted." << std::endl;
          return;
        }

        symTabOffset = this->getOffsetFromDTValue(triton::format::elf::DT_SYMTAB);
        if (!symTabOffset || this->totalSize < symTabOffset) {
          std::cerr << "Warning ELF::initSymbolsTableViaProgramHeaders(): The Symbol Table offset of the binary file is corrupted." << std::endl;
          return;
        }

        while (true) {
          triton::format::elf::ELFSymbolTable sym;
          read += sym.parse(this->raw + symTabOffset + read, this->header.getEIClass());

          if (sym.getOther() != triton::format::elf::STV_DEFAULT)
            break;

          if (sym.getIdxname() > strTabSize)
            break;

          if (this->totalSize < read)
            break;

          sym.setName(this->raw + strTabOffset + sym.getIdxname());
          this->symbolsTable.push_back(sym);
        }
      }


      void ELF::initSymbolsTableViaSectionHeaders(void) {
        triton::uint64 strTabOffset = 0;
        triton::uint64 symTabOffset = 0;
        triton::uint64 symTabSize   = 0;

        // Get sections.
        for (auto it = this->sectionHeaders.begin(); it != this->sectionHeaders.end(); it++) {
          // Get the Symbol Table offset and size.
          if (it->getName() == ".symtab" && it->getType() == triton::format::elf::SHT_SYMTAB) {
            symTabOffset = it->getOffset();
            symTabSize   = it->getSize();
          }

          // Get the String Table offset.
          if (it->getName() == ".strtab" && it->getType() == triton::format::elf::SHT_STRTAB) {
            strTabOffset = it->getOffset();
          }
        }

        if (!symTabOffset || !strTabOffset)
          return;

        if (this->totalSize < symTabOffset + symTabSize)
          return;

        // Parse Symbol Table.
        for (triton::uint32 read = 0; read < symTabSize;) {
          triton::format::elf::ELFSymbolTable sym;

          read += sym.parse(this->raw + symTabOffset + read, this->header.getEIClass());
          if (this->totalSize < strTabOffset + sym.getIdxname())
            continue;

          sym.setName(this->raw + strTabOffset + sym.getIdxname());
          this->symbolsTable.push_back(sym);
        }
      }


      void ELF::initRelTable(void) {
        triton::uint64 relTabOffset = 0;
        triton::uint64 relTabSize   = 0;

        // Parse DT_REL table.
        relTabOffset = this->getOffsetFromDTValue(triton::format::elf::DT_REL);
        if (!relTabOffset || this->totalSize < relTabOffset)
          return;

        relTabSize = this->getDTValue(triton::format::elf::DT_RELSZ);
        if (!relTabSize || this->totalSize < relTabOffset + relTabSize)
          return;

        for (triton::uint32 read = 0; read < relTabSize;) {
          triton::format::elf::ELFRelocationTable rel;
          read += rel.parseRel(this->raw + relTabOffset + read, this->header.getEIClass());
          this->relocationsTable.push_back(rel);
        }
      }


      void ELF::initRelaTable(void) {
        triton::uint64 relaTabOffset = 0;
        triton::uint64 relaTabSize   = 0;

        // Parse DT_RELA table.
        relaTabOffset = this->getOffsetFromDTValue(triton::format::elf::DT_RELA);
        if (!relaTabOffset || this->totalSize < relaTabOffset)
          return;

        relaTabSize = this->getDTValue(triton::format::elf::DT_RELASZ);
        if (!relaTabSize || this->totalSize < relaTabOffset + relaTabSize)
          return;

        for (triton::uint32 read = 0; read < relaTabSize;) {
          triton::format::elf::ELFRelocationTable rela;
          read += rela.parseRela(this->raw + relaTabOffset + read, this->header.getEIClass());
          this->relocationsTable.push_back(rela);
        }
      }


      void ELF::initJmprelTable(void) {
        triton::uint64 jmprelTabOffset = 0;
        triton::uint64 jmprelTabSize   = 0;

        // Parse DT_JMPREL table.
        jmprelTabOffset = this->getOffsetFromDTValue(triton::format::elf::DT_JMPREL);
        if (!jmprelTabOffset || this->totalSize < jmprelTabOffset)
          return;

        jmprelTabSize = this->getDTValue(triton::format::elf::DT_PLTRELSZ);
        if (!jmprelTabSize || this->totalSize < jmprelTabOffset + jmprelTabSize)
          return;

        for (triton::uint32 read = 0; read < jmprelTabSize;) {
          triton::format::elf::ELFRelocationTable jmprel;
          if (this->header.getEIClass() == triton::format::elf::ELFCLASS32)
            read += jmprel.parseRel(this->raw + jmprelTabOffset + read, this->header.getEIClass());
          else if (this->header.getEIClass() == triton::format::elf::ELFCLASS64)
            read += jmprel.parseRela(this->raw + jmprelTabOffset + read, this->header.getEIClass());
          else
            throw std::runtime_error("ELF::initJmprelTable(): Invalid EI_CLASS.");
          this->relocationsTable.push_back(jmprel);
        }
      }


      triton::uint64 ELF::getOffsetFromAddress(triton::uint64 vaddr) {
        for (auto it = this->programHeaders.begin(); it != this->programHeaders.end(); it++) {
          if (it->getType() == triton::format::elf::PT_LOAD) {
            if (vaddr >= it->getVaddr() && vaddr < (it->getVaddr() + it->getFilesz())) {
              return ((vaddr - it->getVaddr()) + it->getOffset());
            }
          }
        }
        return 0;
      }


      triton::uint64 ELF::getOffsetFromDTValue(triton::format::elf::elf_e dt) {
        triton::uint64 offset = 0;
        triton::uint64 vaddr  = 0;

        for (auto it = this->dynamicTable.begin(); it != this->dynamicTable.end(); it++) {
          if (it->getTag() == dt) {
            vaddr  = it->getValue();
            offset = this->getOffsetFromAddress(vaddr);
          }
        }

        return offset;
      }


      triton::uint64 ELF::getDTValue(triton::format::elf::elf_e dt) {
        for (auto it = this->dynamicTable.begin(); it != this->dynamicTable.end(); it++) {
          if (it->getTag() == dt) {
            return it->getValue();
          }
        }
        return 0;
      }


      const std::string& ELF::getPath(void) const {
        return this->path;
      }


      const triton::format::elf::ELFHeader& ELF::getHeader(void) const {
        return this->header;
      }


      const std::vector<triton::format::elf::ELFProgramHeader>& ELF::getProgramHeaders(void) const {
        return this->programHeaders;
      }


      const std::vector<triton::format::elf::ELFSectionHeader>& ELF::getSectionHeaders(void) const {
        return this->sectionHeaders;
      }


      const std::vector<triton::format::elf::ELFDynamicTable>& ELF::getDynamicTable(void) const {
        return this->dynamicTable;
      }


      const std::vector<triton::format::elf::ELFSymbolTable>& ELF::getSymbolsTable(void) const {
        return this->symbolsTable;
      }


      const std::vector<triton::format::elf::ELFRelocationTable>& ELF::getRelocationTable(void) const {
        return this->relocationsTable;
      }


      const std::vector<std::string>& ELF::getSharedLibraries(void) const {
        return this->sharedLibraries;
      }


      const std::list<triton::format::MemoryMapping>& ELF::getMemoryMapping(void) const {
        return this->memoryMapping;
      }

    }; /* elf namespace */
  }; /* format namespace */
}; /* triton namespace */
