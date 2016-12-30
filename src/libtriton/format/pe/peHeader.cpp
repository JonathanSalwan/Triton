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

      void PeHeader::save(std::ostream &os) const {
          os.write((char*)&dosStub[0],peHeaderStart);
          fileHeader.save(os);
          optionalHeader.save(os);
          dataDirectory.save(os);
          for (const PeSectionHeader &hdr : sectionHeaders)
            hdr.save(os);
      }

      triton::uint32 PeHeader::fileAlign(triton::uint32 offset) const {
          triton::uint32 align = optionalHeader.getFileAlignment();
          return ((offset-1)/align+1)*align;
      }

      triton::uint32 PeHeader::sectionAlign(triton::uint32 rva) const {
          triton::uint32 align = optionalHeader.getSectionAlignment();
          return ((rva-1)/align+1)*align;
      }

      triton::uint32 PeHeader::getTotalSectionVirtualSize() const {
          triton::uint32 maxRva = 0;
          for (const PeSectionHeader &hdr : sectionHeaders) {
              triton::uint32 rva = hdr.getVirtualAddress()+hdr.getVirtualSize();
              maxRva = std::max(maxRva,rva);
          }
          return sectionAlign(maxRva);
      }

      triton::uint32 PeHeader::getTotalSectionRawSize() const {
          triton::uint32 maxOffset = 0;
          for (const PeSectionHeader &hdr : sectionHeaders) {
              triton::uint32 offset = hdr.getRawAddress()+hdr.getRawSize();
              maxOffset = std::max(maxOffset,offset);
          }
          return fileAlign(maxOffset);
      }

      triton::uint32 PeHeader::getSize() const {
        triton::uint32 size = peHeaderStart+
            fileHeader.getSize()+
            optionalHeader.getSize()+
            dataDirectory.getSize();
        for (auto &&sectionHeader : sectionHeaders)
            size += sectionHeader.getSize();
        return size;
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

      void PeHeader::addSection(const std::string name, triton::uint32 vsize, triton::uint32 rawsize, triton::uint32 characteristics) {
          PeSectionHeader hdr;
          hdr.setName(name);
          hdr.setVirtualAddress(getTotalSectionVirtualSize());
          hdr.setVirtualSize(vsize);
          hdr.setRawAddress(getTotalSectionRawSize());
          hdr.setRawSize(rawsize);
          hdr.setCharacteristics(characteristics);
          sectionHeaders.push_back(hdr);
          fileHeader.setNumberOfSections(sectionHeaders.size());
          //getTotalSectionVirtualSize will now return the increased size
          optionalHeader.setSizeOfImage(getTotalSectionVirtualSize());
          optionalHeader.setSizeOfHeaders(fileAlign(getSize()));
      }

    }; /* pe namespace */
  }; /* format namespace */
}; /* triton namespace */

