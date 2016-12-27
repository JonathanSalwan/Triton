//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstdio>
#include <new>

#include <pe.hpp>
#include <exceptions.hpp>



namespace triton {
  namespace format {
    namespace pe {

      PE::PE(const std::string& path) {
        this->path      = path;
        this->raw       = nullptr;
        this->totalSize = 0;

        this->open();
        this->parse();
        this->initMemoryMapping();
        this->initImportTable();
        this->initExportTable();
      }


      PE::~PE() {
        delete[] this->raw;
      }


      void PE::open(void) {
        FILE* fd = nullptr;

        // Open the file
        fd = fopen(this->path.c_str(), "rb");
        if (fd == nullptr)
          throw triton::exceptions::PE("PE::open(): Cannot open the binary file.");

        // Get the binary size
        fseek(fd, 0, SEEK_END);
        this->totalSize = ftell(fd);
        rewind(fd);

        this->raw = new(std::nothrow) triton::uint8[this->totalSize];
        if(!this->raw)
          throw triton::exceptions::PE("PE::open(): Not enough memory.");

        // Read the file contents
        if (fread(this->raw, 1, this->totalSize, fd) != this->totalSize)
          throw triton::exceptions::PE("PE::open(): Cannot read the binary file.");

        // Close the file
        fclose(fd);
      }


      bool PE::parse(void) {
        this->header.parse(this->raw, this->totalSize);
        return true;
      }


      void PE::initMemoryMapping(void) {
        for (auto section : header.getSectionHeaders()) {
          triton::format::MemoryMapping area(this->raw);

          if (this->totalSize < (section.rawAddress + section.rawSize)) {
            std::cerr << "Warning PE::initMemoryMapping(): Some PE Section Headers of the binary file are corrupted." << std::endl;
            continue;
          }

          area.setOffset(section.rawAddress);
          area.setSize(section.rawSize);
          area.setVirtualAddress(section.virtualAddress);

          this->memoryMapping.push_back(area);
        }
      }


      triton::uint64 PE::getOffsetFromAddress(triton::uint64 vaddr) const {
        for (auto section : this->header.getSectionHeaders()) {
          if (vaddr >= section.virtualAddress && vaddr < (section.virtualAddress + section.rawSize)) {
              return ((vaddr - section.virtualAddress) + section.rawAddress);
          }
        }
        return 0;
      }

      void PE::initExportTable(void) {
          triton::uint32 exportStart = header.getDataDirectory().exportTable_rva;
          triton::uint32 exportSize = header.getDataDirectory().exportTable_size;
          if (0 == exportStart) {
              std::memset(&exportTable, '\0', 40);
              return;
          }
          std::memcpy(&exportTable, raw+getOffsetFromAddress(exportStart), 40);
          exportTable.name = std::string((char*)raw+getOffsetFromAddress(exportTable.nameRVA));
          triton::uint32 addrTableStart = getOffsetFromAddress(exportTable.exportAddressTableRVA);
          for (triton::usize i=0; i<exportTable.addressTableEntries; ++i) {
              PEExportEntry entry;
              triton::uint32 exportRVA;
              std::memcpy(&exportRVA, raw+addrTableStart+4*i,4);
              if (exportRVA >= exportStart && exportRVA < exportStart+exportSize) {
                  entry.isForward = true;
                  entry.forwarderRVA = exportRVA;
                  entry.forwarderName = std::string((char*)raw+getOffsetFromAddress(exportRVA));
              } else {
                  entry.isForward = false;
                  entry.exportRVA = exportRVA;
              }
              exportTable.entries.push_back(entry);
          }
          triton::uint32 nameTableStart = getOffsetFromAddress(exportTable.namePointerRVA);
          triton::uint32 ordTableStart = getOffsetFromAddress(exportTable.ordinalTableRVA);
          for (triton::usize i=0;i<exportTable.numberOfNamePointers; ++i) {
              triton::uint16 ordinal;
              std::memcpy(&ordinal, raw+ordTableStart+2*i,2);
              triton::uint32 nameRVA;
              std::memcpy(&nameRVA, raw+nameTableStart+4*i,4);
              exportTable.entries[ordinal].ordinal = ordinal;
              exportTable.entries[ordinal].exportNameRVA = nameRVA;
              exportTable.entries[ordinal].exportName = std::string((char*)raw+getOffsetFromAddress(nameRVA));
          }
      }

      void PE::initImportTable(void) {
          triton::uint32 importStart = header.getDataDirectory().importTable_rva;
          if (0 == importStart) return;
          triton::uint32 importOffset = getOffsetFromAddress(importStart);
          triton::uint64 byNameMask = (header.getOptionalHeader().magic == PE_FORMAT_PE32PLUS ?
            0x8000000000000000 : 0x80000000);
          triton::uint32 entrySize = (header.getOptionalHeader().magic == PE_FORMAT_PE32PLUS ? 8 : 4);
          triton::uint32 pos = importOffset;
          PEImportDirectory impdt;
          std::memcpy(&impdt, raw+pos, 20);
          while(impdt.importLookupTableRVA) {
            impdt.entries.clear();
            impdt.name = std::string((char*)raw+getOffsetFromAddress(impdt.nameRVA));
            triton::uint32 impLookupTable = getOffsetFromAddress(impdt.importLookupTableRVA);
            triton::uint64 importEntry  = 0;
            std::memcpy(&importEntry, raw+impLookupTable, entrySize);
            while (importEntry > 0) {
                PEImportLookup entry;
                entry.importByName = !(importEntry & byNameMask);
                if (entry.importByName) {
                    triton::uint32 hintNameStart = getOffsetFromAddress(importEntry & ((1u<<31)-1));
                    std::memcpy(&entry.ordinalNumber, raw+hintNameStart, 2);
                    entry.name = std::string((char*)raw+hintNameStart+2);
                } else {
                    entry.ordinalNumber = importEntry & ((1<<16)-1);
                }
                impdt.entries.push_back(entry);
                impLookupTable += entrySize;
                std::memcpy(&importEntry, raw+impLookupTable, entrySize);
            }
            importTable.push_back(impdt);
            pos+=20;
            std::memcpy(&impdt, raw+pos, 20);
          }
      }

      const triton::uint8* PE::getRaw(void) const {
        return this->raw;
      }


      triton::usize PE::getSize(void) const {
        return this->totalSize;
      }


      const std::string& PE::getPath(void) const {
        return this->path;
      }


      const triton::format::pe::PEHeader& PE::getHeader(void) const {
        return this->header;
      }

      const PEExportDirectory& PE::getExportTable(void) const {
        return this->exportTable;
      }

      const std::vector<PEImportDirectory>& PE::getImportTable(void) const {
        return this->importTable;
      }


      const std::list<triton::format::MemoryMapping>& PE::getMemoryMapping(void) const {
        return this->memoryMapping;
      }

    }; /* pe namespace */
  }; /* format namespace */
}; /* triton namespace */
