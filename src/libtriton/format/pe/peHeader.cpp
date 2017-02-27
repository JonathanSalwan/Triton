//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstdio>

#include <triton/exceptions.hpp>
#include <triton/peHeader.hpp>



namespace triton {
  namespace format {
    namespace pe {

      PeHeader::PeHeader() {
      }


      PeHeader::PeHeader(const PeHeader& copy) {
        this->dataDirectory  = copy.dataDirectory;
        this->fileHeader     = copy.fileHeader;
        this->optionalHeader = copy.optionalHeader;
        this->peHeaderStart  = copy.peHeaderStart;
        this->sectionHeaders = copy.sectionHeaders;
      }


      PeHeader::~PeHeader() {
      }


      PeHeader& PeHeader::operator=(const PeHeader& copy) {
        if (this == &copy)
          return *this;

        this->dataDirectory  = copy.dataDirectory;
        this->fileHeader     = copy.fileHeader;
        this->optionalHeader = copy.optionalHeader;
        this->peHeaderStart  = copy.peHeaderStart;
        this->sectionHeaders = copy.sectionHeaders;

        return *this;
      }


      triton::uint32 PeHeader::parse(const triton::uint8* raw, triton::usize totalSize) {
        if (totalSize < 64)
          throw triton::exceptions::Pe("PeHeader::parse(): File is too small.");

        triton::uint16 magic;
        std::memcpy(&magic, raw, sizeof(magic));
        if (magic != 0x5A4D)
          throw triton::exceptions::Pe("PeHeader::parse(): File doesn't start with \"MZ\".");

        std::memcpy(&this->peHeaderStart, raw + 0x3C, sizeof(this->peHeaderStart));
        if (this->peHeaderStart + 24 > totalSize)
          throw triton::exceptions::Pe("PeHeader::parse(): PE Header would extend beyond end of file.");

        this->dosStub.resize(this->peHeaderStart);
        std::memcpy(&this->dosStub[0], raw, this->peHeaderStart);

        this->fileHeader.parse(raw + this->peHeaderStart + 4);
        triton::uint32 optHeaderStart = this->peHeaderStart + 24;
        triton::uint32 optHeaderSize  = this->fileHeader.getSizeOfOptionalHeader();
        if (optHeaderStart + sizeof(optHeaderSize) > totalSize)
          throw triton::exceptions::Pe("PeHeader::parse(): PE Optional Header would extend beyond end of file.");

        triton::usize dataDirStart = optHeaderStart + this->optionalHeader.parse(raw + optHeaderStart);
        triton::usize dataDirCount = this->optionalHeader.getNumberOfRvaAndSizes();

        if ((dataDirStart + (8 * dataDirCount)) > totalSize)
          throw triton::exceptions::Pe("PeHeader::parse(): Data Directory would extend beyond end of file.");

        this->dataDirectory.parse(raw + dataDirStart);
        triton::uint32 sectionStart = optHeaderStart + optHeaderSize;
        triton::uint32 numSections  = this->fileHeader.getNumberOfSections();
        if ((sectionStart + (numSections * sizeof(PeSectionHeader))) > totalSize)
          throw triton::exceptions::Pe("PeHeader::parse(): Section table would extend beyond end of file.");

        triton::uint32 offset = sectionStart;
        for (triton::usize i = 0; i < numSections; ++i) {
          PeSectionHeader shdr;
          offset += shdr.parse(raw + offset);
          this->sectionHeaders.push_back(shdr);
        }

        return sectionStart + (numSections * sizeof(PeSectionHeader));
      }


      void PeHeader::save(std::ostream& os) const {
        os.write(reinterpret_cast<const char*>(&this->dosStub[0]), this->peHeaderStart);

        this->fileHeader.save(os);
        this->optionalHeader.save(os);
        this->dataDirectory.save(os);

        for (const PeSectionHeader& hdr : this->sectionHeaders)
          hdr.save(os);
      }


      triton::uint32 PeHeader::fileAlign(triton::uint32 offset) const {
        triton::uint32 align = this->optionalHeader.getFileAlignment();

        return (((offset - 1) / align + 1) * align);
      }


      triton::uint32 PeHeader::sectionAlign(triton::uint32 rva) const {
        triton::uint32 align = this->optionalHeader.getSectionAlignment();

        return (((rva - 1) / align + 1) * align);
      }


      triton::uint32 PeHeader::getTotalSectionVirtualSize(void) const {
        triton::uint32 maxRva = 0;

        for (const PeSectionHeader& hdr : this->sectionHeaders) {
          triton::uint32 rva = hdr.getVirtualAddress() + hdr.getVirtualSize();
          maxRva = std::max(maxRva, rva);
        }

        return this->sectionAlign(maxRva);
      }


      triton::uint32 PeHeader::getTotalSectionRawSize(void) const {
        triton::uint32 maxOffset = 0;

        for (const PeSectionHeader& hdr : this->sectionHeaders) {
          triton::uint32 offset = hdr.getRawAddress() + hdr.getRawSize();
          maxOffset = std::max(maxOffset, offset);
        }

        return this->fileAlign(maxOffset);
      }


      triton::uint32 PeHeader::getSize(void) const {
        triton::uint32 size = this->peHeaderStart
                            + this->fileHeader.getSize()
                            + this->optionalHeader.getSize()
                            + this->dataDirectory.getSize();

        for (auto&& sectionHeader : this->sectionHeaders)
          size += sectionHeader.getSize();

        return size;
      }


      const PeFileHeader& PeHeader::getFileHeader(void) const {
        return this->fileHeader;
      }


      const PeOptionalHeader& PeHeader::getOptionalHeader(void) const {
        return this->optionalHeader;
      }


      const PeDataDirectory& PeHeader::getDataDirectory(void) const {
        return this->dataDirectory;
      }


      const std::vector<PeSectionHeader>& PeHeader::getSectionHeaders(void) const {
        return this->sectionHeaders;
      }


      void PeHeader::addSection(const std::string name, triton::uint32 vsize, triton::uint32 rawsize, triton::uint32 characteristics) {
        PeSectionHeader hdr;

        hdr.setName(name);
        hdr.setVirtualAddress(this->getTotalSectionVirtualSize());
        hdr.setVirtualSize(vsize);
        hdr.setRawAddress(this->getTotalSectionRawSize());
        hdr.setRawSize(rawsize);
        hdr.setCharacteristics(characteristics);

        this->sectionHeaders.push_back(hdr);
        this->fileHeader.setNumberOfSections(static_cast<triton::uint16>(this->sectionHeaders.size()));

        // getTotalSectionVirtualSize will now return the increased size
        this->optionalHeader.setSizeOfImage(this->getTotalSectionVirtualSize());
        this->optionalHeader.setSizeOfHeaders(this->fileAlign(this->getSize()));
      }

    }; /* pe namespace */
  }; /* format namespace */
}; /* triton namespace */

