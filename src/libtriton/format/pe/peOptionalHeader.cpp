//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstdio>

#include <triton/exceptions.hpp>
#include <triton/peOptionalHeader.hpp>



namespace triton {
  namespace format {
    namespace pe {

      PeOptionalHeader::PeOptionalHeader() {
        this->magic                       = 0;
        this->majorLinkerVersion          = 0;
        this->minorLinkerVersion          = 0;
        this->sizeOfCode                  = 0;
        this->sizeOfInitializedData       = 0;
        this->sizeOfUninitializedData     = 0;
        this->addressOfEntryPoint         = 0;
        this->baseOfCode                  = 0;
        this->baseOfData                  = 0;
        this->imageBase                   = 0;
        this->sectionAlignment            = 0;
        this->fileAlignment               = 0;
        this->majorOperatingSystemVersion = 0;
        this->minorOperatingSystemVersion = 0;
        this->majorImageVersion           = 0;
        this->minorImageVersion           = 0;
        this->majorSubsystemVersion       = 0;
        this->minorSubsystemVersion       = 0;
        this->win32VersionValue           = 0;
        this->sizeOfImage                 = 0;
        this->sizeOfHeaders               = 0;
        this->checkSum                    = 0;
        this->subsystem                   = 0;
        this->dllCharacteristics          = 0;
        this->sizeOfStackReserve          = 0;
        this->sizeOfStackCommit           = 0;
        this->sizeOfHeapReserve           = 0;
        this->sizeOfHeapCommit            = 0;
        this->loaderFlags                 = 0;
        this->numberOfRvaAndSizes         = 0;
      }


      PeOptionalHeader::PeOptionalHeader(const PeOptionalHeader& copy) {
        this->magic                       = copy.magic;
        this->majorLinkerVersion          = copy.majorLinkerVersion;
        this->minorLinkerVersion          = copy.minorLinkerVersion;
        this->sizeOfCode                  = copy.sizeOfCode;
        this->sizeOfInitializedData       = copy.sizeOfInitializedData;
        this->sizeOfUninitializedData     = copy.sizeOfUninitializedData;
        this->addressOfEntryPoint         = copy.addressOfEntryPoint;
        this->baseOfCode                  = copy.baseOfCode;
        this->baseOfData                  = copy.baseOfData;
        this->imageBase                   = copy.imageBase;
        this->sectionAlignment            = copy.sectionAlignment;
        this->fileAlignment               = copy.fileAlignment;
        this->majorOperatingSystemVersion = copy.majorOperatingSystemVersion;
        this->minorOperatingSystemVersion = copy.minorOperatingSystemVersion;
        this->majorImageVersion           = copy.majorImageVersion;
        this->minorImageVersion           = copy.minorImageVersion;
        this->majorSubsystemVersion       = copy.majorSubsystemVersion;
        this->minorSubsystemVersion       = copy.minorSubsystemVersion;
        this->win32VersionValue           = copy.win32VersionValue;
        this->sizeOfImage                 = copy.sizeOfImage;
        this->sizeOfHeaders               = copy.sizeOfHeaders;
        this->checkSum                    = copy.checkSum;
        this->subsystem                   = copy.subsystem;
        this->dllCharacteristics          = copy.dllCharacteristics;
        this->sizeOfStackReserve          = copy.sizeOfStackReserve;
        this->sizeOfStackCommit           = copy.sizeOfStackCommit;
        this->sizeOfHeapReserve           = copy.sizeOfHeapReserve;
        this->sizeOfHeapCommit            = copy.sizeOfHeapCommit;
        this->loaderFlags                 = copy.loaderFlags;
        this->numberOfRvaAndSizes         = copy.numberOfRvaAndSizes;
      }


      PeOptionalHeader::~PeOptionalHeader() {
      }


      PeOptionalHeader& PeOptionalHeader::operator=(const PeOptionalHeader& copy) {
        if (this == &copy)
          return *this;

        this->magic                       = copy.magic;
        this->majorLinkerVersion          = copy.majorLinkerVersion;
        this->minorLinkerVersion          = copy.minorLinkerVersion;
        this->sizeOfCode                  = copy.sizeOfCode;
        this->sizeOfInitializedData       = copy.sizeOfInitializedData;
        this->sizeOfUninitializedData     = copy.sizeOfUninitializedData;
        this->addressOfEntryPoint         = copy.addressOfEntryPoint;
        this->baseOfCode                  = copy.baseOfCode;
        this->baseOfData                  = copy.baseOfData;
        this->imageBase                   = copy.imageBase;
        this->sectionAlignment            = copy.sectionAlignment;
        this->fileAlignment               = copy.fileAlignment;
        this->majorOperatingSystemVersion = copy.majorOperatingSystemVersion;
        this->minorOperatingSystemVersion = copy.minorOperatingSystemVersion;
        this->majorImageVersion           = copy.majorImageVersion;
        this->minorImageVersion           = copy.minorImageVersion;
        this->majorSubsystemVersion       = copy.majorSubsystemVersion;
        this->minorSubsystemVersion       = copy.minorSubsystemVersion;
        this->win32VersionValue           = copy.win32VersionValue;
        this->sizeOfImage                 = copy.sizeOfImage;
        this->sizeOfHeaders               = copy.sizeOfHeaders;
        this->checkSum                    = copy.checkSum;
        this->subsystem                   = copy.subsystem;
        this->dllCharacteristics          = copy.dllCharacteristics;
        this->sizeOfStackReserve          = copy.sizeOfStackReserve;
        this->sizeOfStackCommit           = copy.sizeOfStackCommit;
        this->sizeOfHeapReserve           = copy.sizeOfHeapReserve;
        this->sizeOfHeapCommit            = copy.sizeOfHeapCommit;
        this->loaderFlags                 = copy.loaderFlags;
        this->numberOfRvaAndSizes         = copy.numberOfRvaAndSizes;

        return *this;
      }


      triton::uint32 PeOptionalHeader::getSize(void) const {
        if (this->magic == PE_FORMAT_PE32PLUS)
          return sizeof(PE32Plus_OptionalHeader);
        else
          return sizeof(PE32_OptionalHeader);
      }


      triton::usize PeOptionalHeader::parse(const triton::uint8* raw) {
        triton::uint16 peFormat;

        std::memcpy(&peFormat, raw, sizeof(peFormat));
        if (peFormat == PE_FORMAT_PE32PLUS) {
          PE32Plus_OptionalHeader ohdr;
          std::memcpy(&ohdr, raw, sizeof(ohdr));
          *this = ohdr;
          return sizeof(ohdr);
        }
        else {
          PE32_OptionalHeader ohdr;
          std::memcpy(&ohdr, raw, sizeof(ohdr));
          *this = ohdr;
          return sizeof(ohdr);
        }
      }


      void PeOptionalHeader::save(std::ostream& os) const {
        if (this->magic == PE_FORMAT_PE32PLUS) {
          PE32Plus_OptionalHeader ohdr;
          this->assign(ohdr);
          os.write(reinterpret_cast<char*>(&ohdr), sizeof(ohdr));
        }
        else {
          PE32_OptionalHeader ohdr;
          this->assign(ohdr);
          os.write(reinterpret_cast<char*>(&ohdr), sizeof(ohdr));
        }
      }


      triton::uint16 PeOptionalHeader::getMagic(void) const {
        return this->magic;
      }


      triton::uint8 PeOptionalHeader::getMajorLinkerVersion(void) const {
        return this->majorLinkerVersion;
      }


      triton::uint8 PeOptionalHeader::getMinorLinkerVersion(void) const {
        return this->minorLinkerVersion;
      }


      triton::uint32 PeOptionalHeader::getSizeOfCode(void) const {
        return this->sizeOfCode;
      }


      triton::uint32 PeOptionalHeader::getSizeOfInitializedData(void) const {
        return this->sizeOfInitializedData;
      }


      triton::uint32 PeOptionalHeader::getSizeOfUninitializedData(void) const {
        return this->sizeOfUninitializedData;
      }


      triton::uint32 PeOptionalHeader::getAddressOfEntryPoint(void) const {
        return this->addressOfEntryPoint;
      }


      triton::uint32 PeOptionalHeader::getBaseOfCode(void) const {
        return this->baseOfCode;
      }


      triton::uint32 PeOptionalHeader::getBaseOfData(void) const {
        return this->baseOfData;
      }


      triton::uint64 PeOptionalHeader::getImageBase(void) const {
        return this->imageBase;
      }


      triton::uint32 PeOptionalHeader::getSectionAlignment(void) const {
        return this->sectionAlignment;
      }


      triton::uint32 PeOptionalHeader::getFileAlignment(void) const {
        return this->fileAlignment;
      }


      triton::uint16 PeOptionalHeader::getMajorOperatingSystemVersion(void) const {
        return this->majorOperatingSystemVersion;
      }


      triton::uint16 PeOptionalHeader::getMinorOperatingSystemVersion(void) const {
        return this->minorOperatingSystemVersion;
      }


      triton::uint16 PeOptionalHeader::getMajorImageVersion(void) const {
        return this->majorImageVersion;
      }


      triton::uint16 PeOptionalHeader::getMinorImageVersion(void) const {
        return this->minorImageVersion;
      }


      triton::uint16 PeOptionalHeader::getMajorSubsystemVersion(void) const {
        return this->majorSubsystemVersion;
      }


      triton::uint16 PeOptionalHeader::getMinorSubsystemVersion(void) const {
        return this->minorSubsystemVersion;
      }


      triton::uint32 PeOptionalHeader::getWin32VersionValue(void) const {
        return this->win32VersionValue;
      }


      triton::uint32 PeOptionalHeader::getSizeOfImage(void) const {
        return this->sizeOfImage;
      }


      void PeOptionalHeader::setSizeOfImage(triton::uint32 sizeOfImage) {
        this->sizeOfImage = sizeOfImage;
      }


      triton::uint32 PeOptionalHeader::getSizeOfHeaders(void) const {
        return this->sizeOfHeaders;
      }


      void PeOptionalHeader::setSizeOfHeaders(triton::uint32 sizeOfHeaders) {
        this->sizeOfHeaders = sizeOfHeaders;
      }


      triton::uint32 PeOptionalHeader::getCheckSum(void) const {
        return this->checkSum;
      }


      triton::uint16 PeOptionalHeader::getSubsystem(void) const {
        return this->subsystem;
      }


      triton::uint16 PeOptionalHeader::getDllCharacteristics(void) const {
        return this->dllCharacteristics;
      }


      triton::uint64 PeOptionalHeader::getSizeOfStackReserve(void) const {
        return this->sizeOfStackReserve;
      }


      triton::uint64 PeOptionalHeader::getSizeOfStackCommit(void) const {
        return this->sizeOfStackCommit;
      }


      triton::uint64 PeOptionalHeader::getSizeOfHeapReserve(void) const {
        return this->sizeOfHeapReserve;
      }


      triton::uint64 PeOptionalHeader::getSizeOfHeapCommit(void) const {
        return this->sizeOfHeapCommit;
      }


      triton::uint32 PeOptionalHeader::getLoaderFlags(void) const {
        return this->loaderFlags;
      }


      triton::uint32 PeOptionalHeader::getNumberOfRvaAndSizes(void) const {
        return this->numberOfRvaAndSizes;
      }


      PeOptionalHeader& PeOptionalHeader::operator=(const PE32_OptionalHeader& other) {
        this->addressOfEntryPoint         = other.addressOfEntryPoint;
        this->baseOfCode                  = other.baseOfCode;
        this->baseOfData                  = other.baseOfData;
        this->checkSum                    = other.checkSum;
        this->dllCharacteristics          = other.dllCharacteristics;
        this->fileAlignment               = other.fileAlignment;
        this->imageBase                   = other.imageBase;
        this->loaderFlags                 = other.loaderFlags;
        this->magic                       = other.magic;
        this->majorImageVersion           = other.majorImageVersion;
        this->majorLinkerVersion          = other.majorLinkerVersion;
        this->majorOperatingSystemVersion = other.majorOperatingSystemVersion;
        this->majorSubsystemVersion       = other.majorSubsystemVersion;
        this->minorImageVersion           = other.minorImageVersion;
        this->minorLinkerVersion          = other.minorLinkerVersion;
        this->minorOperatingSystemVersion = other.minorOperatingSystemVersion;
        this->minorSubsystemVersion       = other.minorSubsystemVersion;
        this->numberOfRvaAndSizes         = other.numberOfRvaAndSizes;
        this->sectionAlignment            = other.sectionAlignment;
        this->sizeOfCode                  = other.sizeOfCode;
        this->sizeOfHeaders               = other.sizeOfHeaders;
        this->sizeOfHeapCommit            = other.sizeOfHeapCommit;
        this->sizeOfHeapReserve           = other.sizeOfHeapReserve;
        this->sizeOfImage                 = other.sizeOfImage;
        this->sizeOfInitializedData       = other.sizeOfInitializedData;
        this->sizeOfStackCommit           = other.sizeOfStackCommit;
        this->sizeOfStackReserve          = other.sizeOfStackReserve;
        this->sizeOfUninitializedData     = other.sizeOfUninitializedData;
        this->subsystem                   = other.subsystem;
        this->win32VersionValue           = other.win32VersionValue;

        return *this;
      }


      PeOptionalHeader& PeOptionalHeader::operator=(const PE32Plus_OptionalHeader& other) {
        this->addressOfEntryPoint         = other.addressOfEntryPoint;
        this->baseOfCode                  = other.baseOfCode;
        this->baseOfData                  = 0;   //not present in this format
        this->checkSum                    = other.checkSum;
        this->dllCharacteristics          = other.dllCharacteristics;
        this->fileAlignment               = other.fileAlignment;
        this->imageBase                   = other.imageBase;
        this->loaderFlags                 = other.loaderFlags;
        this->magic                       = other.magic;
        this->majorImageVersion           = other.majorImageVersion;
        this->majorLinkerVersion          = other.majorLinkerVersion;
        this->majorOperatingSystemVersion = other.majorOperatingSystemVersion;
        this->majorSubsystemVersion       = other.majorSubsystemVersion;
        this->minorImageVersion           = other.minorImageVersion;
        this->minorLinkerVersion          = other.minorLinkerVersion;
        this->minorOperatingSystemVersion = other.minorOperatingSystemVersion;
        this->minorSubsystemVersion       = other.minorSubsystemVersion;
        this->numberOfRvaAndSizes         = other.numberOfRvaAndSizes;
        this->sectionAlignment            = other.sectionAlignment;
        this->sizeOfCode                  = other.sizeOfCode;
        this->sizeOfHeaders               = other.sizeOfHeaders;
        this->sizeOfHeapCommit            = other.sizeOfHeapCommit;
        this->sizeOfHeapReserve           = other.sizeOfHeapReserve;
        this->sizeOfImage                 = other.sizeOfImage;
        this->sizeOfInitializedData       = other.sizeOfInitializedData;
        this->sizeOfStackCommit           = other.sizeOfStackCommit;
        this->sizeOfStackReserve          = other.sizeOfStackReserve;
        this->sizeOfUninitializedData     = other.sizeOfUninitializedData;
        this->subsystem                   = other.subsystem;
        this->win32VersionValue           = other.win32VersionValue;

        return *this;
      }


      void PeOptionalHeader::assign(PE32_OptionalHeader& other) const {
        other.addressOfEntryPoint         = this->addressOfEntryPoint;
        other.baseOfCode                  = this->baseOfCode;
        other.baseOfData                  = this->baseOfData;
        other.checkSum                    = this->checkSum;
        other.dllCharacteristics          = this->dllCharacteristics;
        other.fileAlignment               = this->fileAlignment;
        other.imageBase                   = static_cast<triton::uint32>(this->imageBase);
        other.loaderFlags                 = this->loaderFlags;
        other.magic                       = this->magic;
        other.majorImageVersion           = this->majorImageVersion;
        other.majorLinkerVersion          = this->majorLinkerVersion;
        other.majorOperatingSystemVersion = this->majorOperatingSystemVersion;
        other.majorSubsystemVersion       = this->majorSubsystemVersion;
        other.minorImageVersion           = this->minorImageVersion;
        other.minorLinkerVersion          = this->minorLinkerVersion;
        other.minorOperatingSystemVersion = this->minorOperatingSystemVersion;
        other.minorSubsystemVersion       = this->minorSubsystemVersion;
        other.numberOfRvaAndSizes         = this->numberOfRvaAndSizes;
        other.sectionAlignment            = this->sectionAlignment;
        other.sizeOfCode                  = this->sizeOfCode;
        other.sizeOfHeaders               = this->sizeOfHeaders;
        other.sizeOfHeapCommit            = static_cast<triton::uint32>(this->sizeOfHeapCommit);
        other.sizeOfHeapReserve           = static_cast<triton::uint32>(this->sizeOfHeapReserve);
        other.sizeOfImage                 = this->sizeOfImage;
        other.sizeOfInitializedData       = this->sizeOfInitializedData;
        other.sizeOfStackCommit           = static_cast<triton::uint32>(this->sizeOfStackCommit);
        other.sizeOfStackReserve          = static_cast<triton::uint32>(this->sizeOfStackReserve);
        other.sizeOfUninitializedData     = this->sizeOfUninitializedData;
        other.subsystem                   = this->subsystem;
        other.win32VersionValue           = this->win32VersionValue;
      }


      void PeOptionalHeader::assign(PE32Plus_OptionalHeader& other) const {
        other.addressOfEntryPoint         = this->addressOfEntryPoint;
        other.baseOfCode                  = this->baseOfCode;
        other.checkSum                    = this->checkSum;
        other.dllCharacteristics          = this->dllCharacteristics;
        other.fileAlignment               = this->fileAlignment;
        other.imageBase                   = this->imageBase;
        other.loaderFlags                 = this->loaderFlags;
        other.magic                       = this->magic;
        other.majorImageVersion           = this->majorImageVersion;
        other.majorLinkerVersion          = this->majorLinkerVersion;
        other.majorOperatingSystemVersion = this->majorOperatingSystemVersion;
        other.majorSubsystemVersion       = this->majorSubsystemVersion;
        other.minorImageVersion           = this->minorImageVersion;
        other.minorLinkerVersion          = this->minorLinkerVersion;
        other.minorOperatingSystemVersion = this->minorOperatingSystemVersion;
        other.minorSubsystemVersion       = this->minorSubsystemVersion;
        other.numberOfRvaAndSizes         = this->numberOfRvaAndSizes;
        other.sectionAlignment            = this->sectionAlignment;
        other.sizeOfCode                  = this->sizeOfCode;
        other.sizeOfHeaders               = this->sizeOfHeaders;
        other.sizeOfHeapCommit            = this->sizeOfHeapCommit;
        other.sizeOfHeapReserve           = this->sizeOfHeapReserve;
        other.sizeOfImage                 = this->sizeOfImage;
        other.sizeOfInitializedData       = this->sizeOfInitializedData;
        other.sizeOfStackCommit           = this->sizeOfStackCommit;
        other.sizeOfStackReserve          = this->sizeOfStackReserve;
        other.sizeOfUninitializedData     = this->sizeOfUninitializedData;
        other.subsystem                   = this->subsystem;
        other.win32VersionValue           = this->win32VersionValue;
      }

    }; /* pe namespace */
  }; /* format namespace */
}; /* triton namespace */

