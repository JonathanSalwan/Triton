//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstdio>
#include <fstream>
#include <new>

#include <triton/elf.hpp>
#include <triton/exceptions.hpp>



namespace triton {
  namespace format {
    namespace elf {

      Elf::Elf(const std::string& path) {
        this->path      = path;
        this->raw       = std::vector<triton::uint8>();
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


      Elf::~Elf() {
      }


      void Elf::open(void) {
        std::ifstream ifs(this->path, std::ifstream::binary);

        if(!ifs)
          throw triton::exceptions::Elf("Elf::open(): Cannot open the binary file.");

       ifs.unsetf(std::ios::skipws);

       // get its size:
       std::streampos fileSize;

       ifs.seekg(0, std::ios::end);
       fileSize = ifs.tellg();
       ifs.seekg(0, std::ios::beg);

       // reserve capacity
       this->raw.reserve(fileSize);

       // read the data:
       this->raw.insert(this->raw.begin(),
           std::istream_iterator<triton::uint8>(ifs),
           std::istream_iterator<triton::uint8>());

      // FIXME : This attribute is useless
      this->totalSize = this->raw.size();
      }


      bool Elf::parse(void) {
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
          throw triton::exceptions::Elf("Elf::parse(): The ELF Header of the binary file is corrupted.");

        this->header.parse(this->raw.data());

        // Parse Program Headers
        EIClass  = this->header.getEIClass();
        phOffset = this->header.getPhoff();
        phNum    = this->header.getPhnum();
        phSize   = this->header.getPhentsize();

        if (this->totalSize < (phOffset + (phNum * phSize))) {
          std::cerr << "Warning Elf::parse(): Some ELF Program Headers of the binary file are corrupted." << std::endl;
          return false;
        }

        for (triton::uint16 entry = 0; entry < phNum; entry++) {
          triton::format::elf::ElfProgramHeader phdr;
          phdr.parse((this->raw.data() + (phOffset + (entry * phSize))), EIClass);
          this->programHeaders.push_back(phdr);
        }

        // Parse Section Headers - Stage 1 (entities parsing)
        shOffset = this->header.getShoff();
        shNum    = this->header.getShnum();
        shSize   = this->header.getShentsize();

        if (!shOffset)
          return false;

        if (this->totalSize < (shOffset + (shNum * shSize))) {
          std::cerr << "Warning Elf::parse(): Some ELF Section Headers of the binary file are corrupted." << std::endl;
          return false;
        }

        for (triton::uint16 entry = 0; entry < shNum; entry++) {
          triton::format::elf::ElfSectionHeader shdr;
          shdr.parse((this->raw.data() + (shOffset + (entry * shSize))), EIClass);
          this->sectionHeaders.push_back(shdr);
        }

        // Parse Section Headers - Stage 2 (section name setup)
        shstrndx = this->header.getShstrndx();
        if (shstrndx != triton::format::elf::SHN_XINDEX) {
          if (shstrndx >= this->sectionHeaders.size()) {
            std::cerr << "Warning Elf::parse(): The string table index (shstrndx) of the binary file is corrupted." << std::endl;
            return false;
          }

          strtable = this->sectionHeaders[shstrndx].getOffset();
          for (auto it = this->sectionHeaders.begin(); it != this->sectionHeaders.end(); it++) {
            it->setName(this->raw.data() + strtable + it->getIdxname());
          }
        }

        return true;
      }


      void Elf::initMemoryMapping(void) {
        for (auto it = this->programHeaders.begin(); it != this->programHeaders.end(); it++) {
          triton::format::MemoryMapping area(this->raw.data());

          if (this->totalSize < (it->getOffset() + it->getFilesz())) {
            std::cerr << "Warning Elf::initMemoryMapping(): Some ELF Program Headers of the binary file are corrupted." << std::endl;
            continue;
          }

          area.setOffset(it->getOffset());
          area.setSize(it->getFilesz());
          area.setVirtualAddress(it->getVaddr());

          this->memoryMapping.push_back(area);
        }
      }


      void Elf::initDynamicTable(void) {
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
          std::cerr << "Warning Elf::initDynamicTable(): The Dynamic Table offset of the binary file is corrupted." << std::endl;
          return;
        }

        // Parse Dynamic Table.
        for (triton::uint32 read = 0; read < dynSize;) {
          triton::format::elf::ElfDynamicTable dyn;
          read += dyn.parse(this->raw.data() + dynOffset + read, this->header.getEIClass());
          this->dynamicTable.push_back(dyn);
        }
      }


      void Elf::initSharedLibraries(void) {
        triton::uint64 strTabOffset = 0;

        strTabOffset = this->getOffsetFromDTValue(triton::format::elf::DT_STRTAB);
        if (!strTabOffset || this->totalSize < strTabOffset) {
          std::cerr << "Warning Elf::initSharedLibraries(): The String Table offset of the binary file is corrupted." << std::endl;
          return;
        }

        for (auto it = this->dynamicTable.begin(); it != this->dynamicTable.end(); it++) {
          if (it->getTag() == triton::format::elf::DT_NEEDED) {
            this->sharedLibraries.push_back(reinterpret_cast<const char*>(this->raw.data() + strTabOffset + it->getValue()));
          }
        }
      }


      void Elf::initSymbolsTableViaProgramHeaders(void) {
        triton::uint64 strTabOffset = 0;
        triton::uint64 strTabSize   = 0;
        triton::uint64 symTabOffset = 0;
        triton::uint64 read         = 0;

        strTabOffset = this->getOffsetFromDTValue(triton::format::elf::DT_STRTAB);
        if (!strTabOffset || this->totalSize < strTabOffset) {
          std::cerr << "Warning Elf::initSymbolsTableViaProgramHeaders(): The String Table offset of the binary file is corrupted." << std::endl;
          return;
        }

        strTabSize = this->getDTValue(triton::format::elf::DT_STRSZ);
        if (!strTabSize || this->totalSize < strTabOffset + strTabSize) {
          std::cerr << "Warning Elf::initSymbolsTableViaProgramHeaders(): The String Table offset of the binary file is corrupted." << std::endl;
          return;
        }

        symTabOffset = this->getOffsetFromDTValue(triton::format::elf::DT_SYMTAB);
        if (!symTabOffset || this->totalSize < symTabOffset) {
          std::cerr << "Warning Elf::initSymbolsTableViaProgramHeaders(): The Symbol Table offset of the binary file is corrupted." << std::endl;
          return;
        }

        while (true) {
          triton::format::elf::ElfSymbolTable sym;
          read += sym.parse(this->raw.data() + symTabOffset + read, this->header.getEIClass());

          if (sym.getOther() != triton::format::elf::STV_DEFAULT)
            break;

          if (sym.getIdxname() > strTabSize)
            break;

          if (this->totalSize < read)
            break;

          sym.setName(this->raw.data() + strTabOffset + sym.getIdxname());
          this->symbolsTable.push_back(sym);
        }
      }


      void Elf::initSymbolsTableViaSectionHeaders(void) {
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
          triton::format::elf::ElfSymbolTable sym;

          read += sym.parse(this->raw.data() + symTabOffset + read, this->header.getEIClass());
          if (this->totalSize < strTabOffset + sym.getIdxname())
            continue;

          sym.setName(this->raw.data() + strTabOffset + sym.getIdxname());
          this->symbolsTable.push_back(sym);
        }
      }


      void Elf::initRelTable(void) {
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
          triton::format::elf::ElfRelocationTable rel;
          read += rel.parseRel(this->raw.data() + relTabOffset + read, this->header.getEIClass());
          this->relocationsTable.push_back(rel);
        }
      }


      void Elf::initRelaTable(void) {
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
          triton::format::elf::ElfRelocationTable rela;
          read += rela.parseRela(this->raw.data() + relaTabOffset + read, this->header.getEIClass());
          this->relocationsTable.push_back(rela);
        }
      }


      void Elf::initJmprelTable(void) {
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
          triton::format::elf::ElfRelocationTable jmprel;
          if (this->header.getEIClass() == triton::format::elf::ELFCLASS32)
            read += jmprel.parseRel(this->raw.data() + jmprelTabOffset + read, this->header.getEIClass());
          else if (this->header.getEIClass() == triton::format::elf::ELFCLASS64)
            read += jmprel.parseRela(this->raw.data() + jmprelTabOffset + read, this->header.getEIClass());
          else
            throw triton::exceptions::Elf("Elf::initJmprelTable(): Invalid EI_CLASS.");
          this->relocationsTable.push_back(jmprel);
        }
      }


      triton::uint64 Elf::getOffsetFromAddress(triton::uint64 vaddr) const {
        for (auto it = this->programHeaders.begin(); it != this->programHeaders.end(); it++) {
          if (it->getType() == triton::format::elf::PT_LOAD) {
            if (vaddr >= it->getVaddr() && vaddr < (it->getVaddr() + it->getFilesz())) {
              return ((vaddr - it->getVaddr()) + it->getOffset());
            }
          }
        }
        return 0;
      }


      triton::uint64 Elf::getOffsetFromDTValue(triton::format::elf::elf_e dt) const {
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


      triton::uint64 Elf::getDTValue(triton::format::elf::elf_e dt) const {
        for (auto it = this->dynamicTable.begin(); it != this->dynamicTable.end(); it++) {
          if (it->getTag() == dt) {
            return it->getValue();
          }
        }
        return 0;
      }


      const triton::uint8* Elf::getRaw(void) const {
        return this->raw.data();
      }


      triton::usize Elf::getSize(void) const {
        return this->totalSize;
      }


      const std::string& Elf::getPath(void) const {
        return this->path;
      }


      const triton::format::elf::ElfHeader& Elf::getHeader(void) const {
        return this->header;
      }


      const std::vector<triton::format::elf::ElfProgramHeader>& Elf::getProgramHeaders(void) const {
        return this->programHeaders;
      }


      const std::vector<triton::format::elf::ElfSectionHeader>& Elf::getSectionHeaders(void) const {
        return this->sectionHeaders;
      }


      const std::vector<triton::format::elf::ElfDynamicTable>& Elf::getDynamicTable(void) const {
        return this->dynamicTable;
      }


      const std::vector<triton::format::elf::ElfSymbolTable>& Elf::getSymbolsTable(void) const {
        return this->symbolsTable;
      }


      const std::vector<triton::format::elf::ElfRelocationTable>& Elf::getRelocationTable(void) const {
        return this->relocationsTable;
      }


      const std::vector<std::string>& Elf::getSharedLibraries(void) const {
        return this->sharedLibraries;
      }


      const std::list<triton::format::MemoryMapping>& Elf::getMemoryMapping(void) const {
        return this->memoryMapping;
      }

    }; /* elf namespace */
  }; /* format namespace */
}; /* triton namespace */
