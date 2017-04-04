//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstdio>
#include <new>
#include <fstream>

#include <triton/exceptions.hpp>
#include <triton/pe.hpp>



namespace triton {
  namespace format {
    namespace pe {

      Pe::Pe(const std::string& path) {
        this->path      = path;
        this->raw       = std::vector<triton::uint8>();
        this->totalSize = 0;

        this->open();
        this->parse();
        this->initMemoryMapping();
        this->initImportTable();
        this->initExportTable();
      }


      Pe::~Pe() {
      }


      void Pe::open(void) {
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


      bool Pe::parse(void) {
        this->header.parse(this->raw.data(), this->totalSize);
        return true;
      }


      void Pe::initMemoryMapping(void) {
        for (auto&& section : this->header.getSectionHeaders()) {
          triton::format::MemoryMapping area(this->raw.data());

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

        this->exportTable.parse(raw.data() + this->getOffsetFromAddress(exportStart));
        this->exportTable.setName(reinterpret_cast<const char*>(raw.data() + this->getOffsetFromAddress(this->exportTable.getNameRVA())));

        triton::uint64 addrTableStart = this->getOffsetFromAddress(this->exportTable.getExportAddressTableRVA());
        if (addrTableStart + (this->exportTable.getAddressTableEntries() * sizeof(triton::uint32)) >= totalSize)
          throw triton::exceptions::Pe("Pe::initExportTable(): export address table runs past end of file");

        std::vector<PeExportEntry> entries;
        for (triton::usize i = 0; i < this->exportTable.getAddressTableEntries(); ++i) {
          PeExportEntry entry;
          triton::uint32 exportRVA;
          std::memcpy(&exportRVA, raw.data() + addrTableStart + (sizeof(exportRVA) * i), sizeof(exportRVA));
          if (exportRVA >= exportStart && exportRVA < exportStart + exportSize) {
            entry.isForward     = true;
            entry.forwarderRVA  = exportRVA;
            entry.forwarderName = std::string(reinterpret_cast<const char*>(raw.data() + this->getOffsetFromAddress(exportRVA)));
          }
          else {
            entry.isForward = false;
            entry.exportRVA = exportRVA;
          }
          entries.push_back(std::move(entry));
        }

        triton::uint64 nameTableStart = this->getOffsetFromAddress(this->exportTable.getNamePointerRVA());
        if (nameTableStart + (this->exportTable.getNumberOfNamePointers() * sizeof(triton::uint32)) >= totalSize)
          throw triton::exceptions::Pe("Pe::initExportTable(): export name table runs past end of file");

        triton::uint64 ordTableStart = this->getOffsetFromAddress(this->exportTable.getOrdinalTableRVA());
        if (ordTableStart + (this->exportTable.getNumberOfNamePointers() * sizeof(triton::uint16)) >= totalSize)
          throw triton::exceptions::Pe("Pe::initExportTable(): export ordinal table runs past end of file");

        for (triton::usize i = 0; i < this->exportTable.getNumberOfNamePointers(); ++i) {
          triton::uint16 ordinal;
          triton::uint32 nameRVA;

          std::memcpy(&ordinal, raw.data() + (ordTableStart + sizeof(ordinal) * i), sizeof(ordinal));
          std::memcpy(&nameRVA, raw.data() + (nameTableStart + sizeof(nameRVA) * i), sizeof(nameRVA));

          entries[ordinal].ordinal        = ordinal;
          entries[ordinal].exportNameRVA  = nameRVA;
          entries[ordinal].exportName     = std::string(reinterpret_cast<const char *>(raw.data() + this->getOffsetFromAddress(nameRVA)));
        }

        for (const PeExportEntry& entry : entries)
          this-> exportTable.addEntry(entry);
      }


      void Pe::initImportTable(void) {
        triton::uint32 importStart = this->header.getDataDirectory().getImportTable_rva();

        if (importStart == 0)
          return;

        triton::uint64 importOffset = this->getOffsetFromAddress(importStart);
        triton::uint32 format       = this->header.getOptionalHeader().getMagic();
        triton::uint64 byNameMask   = (format == PE_FORMAT_PE32PLUS ? 0x8000000000000000 : 0x80000000);
        triton::uint32 entrySize    = (format == PE_FORMAT_PE32PLUS ? sizeof(triton::uint64) : sizeof(triton::uint32));
        triton::uint64 pos          = importOffset;

        while (true) {
          PeImportDirectory impdt;

          if (!impdt.parse(raw.data() + pos))
            break;

          impdt.setName(std::string(reinterpret_cast<const char*>(raw.data() + this->getOffsetFromAddress(impdt.getNameRVA()))));
          triton::uint64 impLookupTable = this->getOffsetFromAddress(impdt.getImportLookupTableRVA());
          triton::uint64 importEntry = 0;
          std::memcpy(&importEntry, raw.data() + impLookupTable, entrySize);

          while (importEntry > 0) {
            PeImportLookup entry;
            entry.importByName = !(importEntry & byNameMask);

            if (entry.importByName) {
              triton::uint64 hintNameStart = this->getOffsetFromAddress(importEntry & ((1u << 31) - 1));
              std::memcpy(&entry.ordinalNumber, raw.data() + hintNameStart, sizeof(entry.ordinalNumber));
              entry.name = std::string(reinterpret_cast<const char*>(raw.data() + hintNameStart + 2));
            }
            else {
              entry.ordinalNumber = importEntry & ((1 << 16) - 1);
            }

            impdt.addEntry(entry);
            impLookupTable += entrySize;
            std::memcpy(&importEntry, raw.data() + impLookupTable, entrySize);
          }

          importTable.push_back(impdt);
          dlls.push_back(impdt.getName());
          pos += 20;
        }
      }


      const triton::uint8* Pe::getRaw(void) const {
        return this->raw.data();
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


      triton::uint64 Pe::getImageBase(void) const {
        return this->header.getOptionalHeader().getImageBase();
      }

    }; /* pe namespace */
  }; /* format namespace */
}; /* triton namespace */
