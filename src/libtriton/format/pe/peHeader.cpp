//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstdio>

#include <peHeader.hpp>
#include <exceptions.hpp>



namespace triton {
  namespace format {
    namespace pe {

      PEHeader::PEHeader() {
        std::memset(&this->fileHeader, 0, sizeof(this->fileHeader));
        std::memset(&this->optionalHeader, 0, sizeof(this->optionalHeader));
        std::memset(&this->dataDirectory, 0, sizeof(this->dataDirectory));
      }


      PEHeader::PEHeader(const PEHeader& copy) {
        std::memcpy(&this->fileHeader, &copy.fileHeader, sizeof(this->fileHeader));
        std::memcpy(&this->optionalHeader, &copy.optionalHeader, sizeof(this->optionalHeader));
        std::memcpy(&this->dataDirectory, &copy.dataDirectory, sizeof(this->dataDirectory));
        this->sectionHeaders = copy.sectionHeaders;
      }


      PEHeader::~PEHeader() {
      }


      void PEHeader::operator=(const PEHeader& copy) {
        if (this == &copy) return;
        std::memcpy(&this->fileHeader, &copy.fileHeader, sizeof(this->fileHeader));
        std::memcpy(&this->optionalHeader, &copy.optionalHeader, sizeof(this->optionalHeader));
        std::memcpy(&this->dataDirectory, &copy.dataDirectory, sizeof(this->dataDirectory));
        this->sectionHeaders = copy.sectionHeaders;
      }


      triton::uint32 PEHeader::parse(const triton::uint8* raw, triton::uint32 totalSize) {
        if (totalSize < 64) {
            throw triton::exceptions::PE("PEHeader::parse(): File is too small.");
        }
        triton::uint16 magic;
        triton::uint32 peHeaderStart;
        std::memcpy(&magic, raw, 2);
        if (magic != 0x5A4D) {
            throw triton::exceptions::PE("PEHeader::parse(): File doesn't start with \"MZ\".");
        }
        std::memcpy(&peHeaderStart, raw+0x3C, 4);
        if (peHeaderStart + sizeof(this->fileHeader) > totalSize) {
            throw triton::exceptions::PE("PEHeader::parse(): PE Header would extend beyond end of file.");
        }
        std::memcpy(&this->fileHeader, raw+peHeaderStart, sizeof(this->fileHeader));
        triton::uint32 optHeaderStart = peHeaderStart+sizeof(this->fileHeader);
        if (optHeaderStart+sizeof(this->fileHeader.sizeOfOptionalHeader) > totalSize) {
            throw triton::exceptions::PE("PEHeader::parse(): PE Optional Header would extend beyond end of file.");
        }
        triton::uint16 peFormat;
        triton::uint32 dataDirStart;
        std::memcpy(&peFormat, raw+optHeaderStart, sizeof(peFormat));
        if (peFormat == PE_FORMAT_PE32PLUS) {
            PE32Plus_OptionalHeader ohdr;
            std::memcpy(&ohdr, raw+optHeaderStart, sizeof(ohdr));
            this->optionalHeader = ohdr;
            dataDirStart = optHeaderStart+sizeof(ohdr);
        } else {
            PE32_OptionalHeader ohdr;
            std::memcpy(&ohdr, raw+optHeaderStart, sizeof(ohdr));
            this->optionalHeader = ohdr;
            dataDirStart = optHeaderStart+sizeof(ohdr);
        }
        if ((dataDirStart + 8*this->optionalHeader.numberOfRvaAndSizes) > totalSize) {
            throw triton::exceptions::PE("PEHeader::parse(): Data Directory would extend beyond end of file.");
        }
        std::memcpy(&this->dataDirectory, raw+dataDirStart, 8*this->optionalHeader.numberOfRvaAndSizes);
        triton::uint32 sectionStart = optHeaderStart+this->fileHeader.sizeOfOptionalHeader;
        if ((sectionStart + this->fileHeader.numberOfSections*sizeof(PESectionHeader)) > totalSize) {
            throw triton::exceptions::PE("PEHeader::parse(): Section table would extend beyond end of file.");
        }
        for (int i=0; i<this->fileHeader.numberOfSections; ++i) {
            PESectionHeader shdr;
            std::memcpy(&shdr, raw+sectionStart+i*sizeof(shdr), sizeof(shdr));
            this->sectionHeaders.push_back(shdr);
        }
        return sectionStart+this->fileHeader.numberOfSections*sizeof(PESectionHeader);
      }

      const PEFileHeader &PEHeader::getFileHeader() const {
          return fileHeader;
      }

      const PEOptionalHeader &PEHeader::getOptionalHeader() const {
          return optionalHeader;
      }

      const PEDataDirectory &PEHeader::getDataDirectory() const {
          return dataDirectory;
      }

      const std::vector<PESectionHeader> &PEHeader::getSectionHeaders() const {
          return sectionHeaders;
      }

      PEOptionalHeader &PEOptionalHeader::operator=(const PE32_OptionalHeader &other) {
          magic = other.magic;
          majorLinkerVersion = other.majorLinkerVersion;
          minorLinkerVersion = other.minorLinkerVersion;
          sizeOfCode = other.sizeOfCode;
          sizeOfInitializedData = other.sizeOfInitializedData;
          sizeOfUninitializedData = other.sizeOfUninitializedData;
          addressOfEntryPoint = other.addressOfEntryPoint;
          baseOfCode = other.baseOfCode;
          baseOfData = other.baseOfData;
          imageBase = other.imageBase;
          sectionAlignment = other.sectionAlignment;
          fileAlignment = other.fileAlignment;
          majorOperatingSystemVersion = other.majorOperatingSystemVersion;
          minorOperatingSystemVersion = other.minorOperatingSystemVersion;
          majorImageVersion = other.majorImageVersion;
          minorImageVersion = other.minorImageVersion;
          majorSubsystemVersion = other.majorSubsystemVersion;
          minorSubsystemVersion = other.minorSubsystemVersion;
          win32VersionValue = other.win32VersionValue;
          sizeOfImage = other.sizeOfImage;
          sizeOfHeaders = other.sizeOfHeaders;
          checkSum = other.checkSum;
          subsystem = other.subsystem;
          dllCharacteristics = other.dllCharacteristics;
          sizeOfStackReserve = other.sizeOfStackReserve;
          sizeOfStackCommit = other.sizeOfStackCommit;
          sizeOfHeapReserve = other.sizeOfHeapReserve;
          sizeOfHeapCommit = other.sizeOfHeapCommit;
          loaderFlags = other.loaderFlags;
          numberOfRvaAndSizes = other.numberOfRvaAndSizes;
          return *this;
      }

      PEOptionalHeader &PEOptionalHeader::operator=(const PE32Plus_OptionalHeader &other) {
          magic = other.magic;
          majorLinkerVersion = other.majorLinkerVersion;
          minorLinkerVersion = other.minorLinkerVersion;
          sizeOfCode = other.sizeOfCode;
          sizeOfInitializedData = other.sizeOfInitializedData;
          sizeOfUninitializedData = other.sizeOfUninitializedData;
          addressOfEntryPoint = other.addressOfEntryPoint;
          baseOfCode = other.baseOfCode;
          baseOfData = 0;   //not present in this format
          imageBase = other.imageBase;
          sectionAlignment = other.sectionAlignment;
          fileAlignment = other.fileAlignment;
          majorOperatingSystemVersion = other.majorOperatingSystemVersion;
          minorOperatingSystemVersion = other.minorOperatingSystemVersion;
          majorImageVersion = other.majorImageVersion;
          minorImageVersion = other.minorImageVersion;
          majorSubsystemVersion = other.majorSubsystemVersion;
          minorSubsystemVersion = other.minorSubsystemVersion;
          win32VersionValue = other.win32VersionValue;
          sizeOfImage = other.sizeOfImage;
          sizeOfHeaders = other.sizeOfHeaders;
          checkSum = other.checkSum;
          subsystem = other.subsystem;
          dllCharacteristics = other.dllCharacteristics;
          sizeOfStackReserve = other.sizeOfStackReserve;
          sizeOfStackCommit = other.sizeOfStackCommit;
          sizeOfHeapReserve = other.sizeOfHeapReserve;
          sizeOfHeapCommit = other.sizeOfHeapCommit;
          loaderFlags = other.loaderFlags;
          numberOfRvaAndSizes = other.numberOfRvaAndSizes;
          return *this;
      }
        
    }; /* pe namespace */
  }; /* format namespace */
}; /* triton namespace */

