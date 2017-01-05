//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstdio>
#include <new>

#include <exceptions.hpp>
#include <pe.hpp>



namespace triton {
  namespace format {
    namespace pe {

      Pe::Pe(const std::string& path) {
        this->path      = path;
        this->raw       = nullptr;
        this->totalSize = 0;

        this->open();
        this->parse();
        this->initMemoryMapping();
        this->initImportTable();
        this->initExportTable();
      }


      Pe::~Pe() {
        delete[] this->raw;
      }


      void Pe::open(void) {
        FILE* fd = nullptr;

        // Open the file
        fd = fopen(this->path.c_str(), "rb");
        if (fd == nullptr)
          throw triton::exceptions::Pe("Pe::open(): Cannot open the binary file.");

        // Get the binary size
        fseek(fd, 0, SEEK_END);
        this->totalSize = ftell(fd);
        rewind(fd);

        this->raw = new(std::nothrow) triton::uint8[this->totalSize];
        if(!this->raw)
          throw triton::exceptions::Pe("Pe::open(): Not enough memory.");

        // Read the file contents
        if (fread(this->raw, 1, this->totalSize, fd) != this->totalSize)
          throw triton::exceptions::Pe("Pe::open(): Cannot read the binary file.");

        // Close the file
        fclose(fd);
      }


      bool Pe::parse(void) {
        this->header.parse(this->raw, this->totalSize);
        return true;
      }


      void Pe::initMemoryMapping(void) {
        for (auto&& section : this->header.getSectionHeaders()) {
          triton::format::MemoryMapping area(this->raw);

          triton::uint32 rawAddr  = section.getRawAddress();
          triton::uint32 rawSize  = section.getRawSize();
          triton::uint32 virtAddr = section.getVirtualAddress();

          if (this->totalSize < (rawAddr + rawSize))
            std::cerr << "Warning Pe::initMemoryMapping(): Some PE Section Headers of the binary file are corrupted." << std::endl;

          area.setOffset(rawAddr);
          area.setSize(rawSize);
          area.setVirtualAddress(virtAddr);

          this->memoryMapping.push_back(area);
        }
      }


      triton::uint64 Pe::getOffsetFromAddress(triton::uint64 vaddr) const {
        std::ostringstream os;

        for (auto&& section : this->header.getSectionHeaders()) {
          if (vaddr >= section.getVirtualAddress() && vaddr < (section.getVirtualAddress() + section.getRawSize())) {
            triton::uint64 offset = ((vaddr - section.getVirtualAddress()) + section.getRawAddress());
            if (offset >= section.getRawAddress()+section.getRawSize()) {
              os << "Pe::getOffsetFromAddress(): address " << std::hex << vaddr << " out of bounds in the " << section.getName() << " section";
              throw triton::exceptions::Pe(os.str());
            }
            return offset;
          }
        }

        os << "Pe::getOffsetFromAddress(): address " << std::hex << vaddr << " not found in any section";
        throw triton::exceptions::Pe(os.str());
      }


      void Pe::initExportTable(void) {
        triton::uint32 exportStart = this->header.getDataDirectory().getExportTable_rva();
        triton::uint32 exportSize  = this->header.getDataDirectory().getExportTable_size();

        if (exportStart == 0)
          return; // no export table, leave it blank

        this->exportTable.parse(raw + this->getOffsetFromAddress(exportStart));
        this->exportTable.setName(reinterpret_cast<const char*>(raw + this->getOffsetFromAddress(this->exportTable.getNameRVA())));
        triton::uint32 addrTableStart = this->getOffsetFromAddress(this->exportTable.getExportAddressTableRVA());
        if (addrTableStart + (this->exportTable.getAddressTableEntries() * sizeof(triton::uint32)) >= totalSize)
          throw triton::exceptions::Pe("Pe::initExportTable(): export address table runs past end of file");

        std::vector<PeExportEntry> entries;
        for (triton::usize i = 0; i < this->exportTable.getAddressTableEntries(); ++i) {
          PeExportEntry entry;
          triton::uint32 exportRVA;
          std::memcpy(&exportRVA, raw + addrTableStart + (sizeof(exportRVA) * i), sizeof(exportRVA));
          if (exportRVA >= exportStart && exportRVA < exportStart + exportSize) {
            entry.isForward     = true;
            entry.forwarderRVA  = exportRVA;
            entry.forwarderName = std::string(reinterpret_cast<const char*>(raw + this->getOffsetFromAddress(exportRVA)));
          }
          else {
            entry.isForward = false;
            entry.exportRVA = exportRVA;
          }
          entries.push_back(std::move(entry));
        }

        triton::uint32 nameTableStart = this->getOffsetFromAddress(this->exportTable.getNamePointerRVA());
        if (nameTableStart + (this->exportTable.getNumberOfNamePointers() * sizeof(triton::uint32)) >= totalSize)
          throw triton::exceptions::Pe("Pe::initExportTable(): export name table runs past end of file");

        triton::uint32 ordTableStart = this->getOffsetFromAddress(this->exportTable.getOrdinalTableRVA());
        if (ordTableStart + (this->exportTable.getNumberOfNamePointers() * sizeof(triton::uint16)) >= totalSize)
          throw triton::exceptions::Pe("Pe::initExportTable(): export ordinal table runs past end of file");

        for (triton::usize i = 0; i < this->exportTable.getNumberOfNamePointers(); ++i) {
          triton::uint16 ordinal;
          triton::uint32 nameRVA;

          std::memcpy(&ordinal, raw + (ordTableStart + sizeof(ordinal) * i), sizeof(ordinal));
          std::memcpy(&nameRVA, raw + (nameTableStart + sizeof(nameRVA) * i), sizeof(nameRVA));

          entries[ordinal].ordinal        = ordinal;
          entries[ordinal].exportNameRVA  = nameRVA;
          entries[ordinal].exportName     = std::string(reinterpret_cast<const char *>(raw + this->getOffsetFromAddress(nameRVA)));
        }

        for (const PeExportEntry& entry : entries)
          this-> exportTable.addEntry(entry);
      }


      void Pe::initImportTable(void) {
        triton::uint32 importStart = this->header.getDataDirectory().getImportTable_rva();

        if (importStart == 0)
          return;

        triton::uint32 importOffset = this->getOffsetFromAddress(importStart);
        triton::uint32 format       = this->header.getOptionalHeader().getMagic();
        triton::uint64 byNameMask   = (format == PE_FORMAT_PE32PLUS ? 0x8000000000000000 : 0x80000000);
        triton::uint32 entrySize    = (format == PE_FORMAT_PE32PLUS ? sizeof(triton::uint64) : sizeof(triton::uint32));
        triton::uint32 pos          = importOffset;

        while (true) {
          PeImportDirectory impdt;

          if (!impdt.parse(raw+pos))
            break;

          impdt.setName(std::string(reinterpret_cast<const char*>(raw + this->getOffsetFromAddress(impdt.getNameRVA()))));
          triton::uint32 impLookupTable = this->getOffsetFromAddress(impdt.getImportLookupTableRVA());
          triton::uint64 importEntry = 0;
          std::memcpy(&importEntry, raw + impLookupTable, entrySize);

          while (importEntry > 0) {
            PeImportLookup entry;
            entry.importByName = !(importEntry & byNameMask);

            if (entry.importByName) {
              triton::uint32 hintNameStart = this->getOffsetFromAddress(importEntry & ((1u << 31) - 1));
              std::memcpy(&entry.ordinalNumber, raw + hintNameStart, sizeof(entry.ordinalNumber));
              entry.name = std::string(reinterpret_cast<const char*>(raw + hintNameStart + 2));
            }
            else {
              entry.ordinalNumber = importEntry & ((1 << 16) - 1);
            }

            impdt.addEntry(entry);
            impLookupTable += entrySize;
            std::memcpy(&importEntry, raw + impLookupTable, entrySize);
          }

          importTable.push_back(impdt);
          dlls.push_back(impdt.getName());
          pos += 20;
        }
      }


      const triton::uint8* Pe::getRaw(void) const {
        return this->raw;
      }


      triton::usize Pe::getSize(void) const {
        return this->totalSize;
      }


      const std::string& Pe::getPath(void) const {
        return this->path;
      }


      const triton::format::pe::PeHeader& Pe::getHeader(void) const {
        return this->header;
      }


      const PeExportDirectory& Pe::getExportTable(void) const {
        return this->exportTable;
      }


      const std::vector<PeImportDirectory>& Pe::getImportTable(void) const {
        return this->importTable;
      }


      const std::vector<std::string>& Pe::getSharedLibraries(void) const {
        return this->dlls;
      }


      const std::list<triton::format::MemoryMapping>& Pe::getMemoryMapping(void) const {
        return this->memoryMapping;
      }


      triton::uint32 Pe::getImageBase(void) const {
        return this->header.getOptionalHeader().getImageBase();
      }

    }; /* pe namespace */
  }; /* format namespace */
}; /* triton namespace */
