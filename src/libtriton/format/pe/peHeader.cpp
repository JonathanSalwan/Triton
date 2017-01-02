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

      PeHeader::PeHeader() {
      }


      PeHeader::PeHeader(const PeHeader& copy) {
        this->dosStub        = copy.dosStub;
        this->peHeaderStart  = copy.peHeaderStart;
        this->fileHeader     = copy.fileHeader;
        this->optionalHeader = copy.optionalHeader;
        this->dataDirectory  = copy.dataDirectory;
        this->sectionHeaders = copy.sectionHeaders;
      }


      PeHeader::~PeHeader() {
      }


      PeHeader &PeHeader::operator=(const PeHeader& copy) {
        if (this == &copy)
            return *this;
        this->dosStub        = copy.dosStub;
        this->peHeaderStart  = copy.peHeaderStart;
        this->fileHeader     = copy.fileHeader;
        this->optionalHeader = copy.optionalHeader;
        this->dataDirectory  = copy.dataDirectory;
        this->sectionHeaders = copy.sectionHeaders;
        return *this;
      }


      triton::uint32 PeHeader::parse(const triton::uint8* raw, triton::usize totalSize) {
        if (totalSize < 64) {
            throw triton::exceptions::Pe("PeHeader::parse(): File is too small.");
        }

        triton::uint16 magic;
        std::memcpy(&magic, raw, sizeof(magic));
        if (magic != 0x5A4D) {
            throw triton::exceptions::Pe("PeHeader::parse(): File doesn't start with \"MZ\".");
        }

        std::memcpy(&peHeaderStart, raw+0x3C, sizeof(peHeaderStart));
        dosStub.resize(peHeaderStart);
        std::memcpy(&dosStub[0], raw, peHeaderStart);
        if (peHeaderStart + 24 > totalSize) {
            throw triton::exceptions::Pe("PeHeader::parse(): PE Header would extend beyond end of file.");
        }

        fileHeader.parse(raw+peHeaderStart+4);
        triton::uint32 optHeaderStart = peHeaderStart+24;
        triton::uint32 optHeaderSize = this->fileHeader.getSizeOfOptionalHeader();
        if (optHeaderStart+sizeof(optHeaderSize) > totalSize) {
            throw triton::exceptions::Pe("PeHeader::parse(): PE Optional Header would extend beyond end of file.");
        }

        triton::usize dataDirStart = optHeaderStart + optionalHeader.parse(raw+optHeaderStart);
        triton::usize dataDirCount = this->optionalHeader.getNumberOfRvaAndSizes();

        if ((dataDirStart + 8*dataDirCount) > totalSize) {
            throw triton::exceptions::Pe("PeHeader::parse(): Data Directory would extend beyond end of file.");
        }

        dataDirectory.parse(raw+dataDirStart);
        triton::uint32 sectionStart = optHeaderStart+optHeaderSize;
        triton::uint32 numSections = this->fileHeader.getNumberOfSections();
        if ((sectionStart + numSections*sizeof(PeSectionHeader)) > totalSize) {
            throw triton::exceptions::Pe("PeHeader::parse(): Section table would extend beyond end of file.");
        }

        triton::uint32 offset = sectionStart;
        for (triton::usize i=0; i<numSections; ++i) {
            PeSectionHeader shdr;
            offset += shdr.parse(raw+offset);
            this->sectionHeaders.push_back(shdr);
        }

        return sectionStart+numSections*sizeof(PeSectionHeader);
      }

      const PeFileHeader &PeHeader::getFileHeader() const {
          return fileHeader;
      }

      const PeOptionalHeader &PeHeader::getOptionalHeader() const {
          return optionalHeader;
      }

      const PeDataDirectory &PeHeader::getDataDirectory() const {
          return dataDirectory;
      }

      const std::vector<PeSectionHeader> &PeHeader::getSectionHeaders() const {
          return sectionHeaders;
      }

    }; /* pe namespace */
  }; /* format namespace */
}; /* triton namespace */

