//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstdio>
#include <new>
#include <fstream>

#include <triton/peBuilder.hpp>
#include <triton/exceptions.hpp>



namespace triton {
  namespace format {
    namespace pe {

      PeBuilder::PeBuilder(const std::string& path) : Pe(path) {
        this->sectionContent.resize(this->header.getSectionHeaders().size());

        for (triton::usize i = 0; i < this->header.getSectionHeaders().size(); ++i) {
          triton::uint32 sz = this->header.getSectionHeaders()[i].getRawSize();
          this->sectionContent[i].resize(sz);
          std::memcpy(&this->sectionContent[i][0], this->raw.data() + this->header.getSectionHeaders()[i].getRawAddress(), sz);
        }
      }


      PeBuilder::~PeBuilder() {
      }


      triton::uint32 PeBuilder::getSectionIndexForRVA(triton::uint64 vaddr) const {
        std::ostringstream os;

        for (triton::uint32 i = 0; i < this->header.getSectionHeaders().size(); ++i) {
          const PeSectionHeader& section = this->header.getSectionHeaders()[i];

          if (vaddr >= section.getVirtualAddress() && vaddr < (section.getVirtualAddress() + section.getRawSize())) {
            triton::uint64 offset = vaddr - section.getVirtualAddress();

            if (offset > this->sectionContent[i].size()) {
              os << "PeBuilder::getSectionIndexForRVA(): address " << std::hex << vaddr << " out of bounds in the " << section.getName() << " section";
              throw triton::exceptions::Pe(os.str());
            }

            return i;
          }
        }

        os << "Pe::getOffsetFromAddress(): address " << std::hex << vaddr << " not found in any section";
        throw triton::exceptions::Pe(os.str());
      }


      void PeBuilder::addSection(const std::string& name, triton::uint32 vsize, triton::uint32 rawsize, triton::uint32 characteristics) {
        this->header.addSection(name, vsize, rawsize, characteristics);
        std::vector<triton::uint8> cont;
        cont.resize(rawsize);
        this->sectionContent.push_back(cont);
      }


      const std::vector<triton::uint8> PeBuilder::getSectionContent(triton::uint32 sectionIndex) {
        if (sectionIndex >= this->sectionContent.size())
          throw triton::exceptions::Pe("PeBuilder::getSectionContent: section index out of range");

        return this->sectionContent[sectionIndex];
      }


      void PeBuilder::readFromSection(triton::uint32 sectionIndex, void* dest, triton::uint32 src, triton::uint32 size) {
        if (sectionIndex >= this->sectionContent.size())
          throw triton::exceptions::Pe("PeBuilder::readFromSection: section index out of range");

        if (src + size > this->sectionContent[sectionIndex].size())
          throw triton::exceptions::Pe("PeBuilder::readFromSection: trying to read past end of section");

        std::memcpy(dest, &this->sectionContent[sectionIndex][src], size);
      }


      void PeBuilder::writeToSection(triton::uint32 sectionIndex, triton::uint32 dest, void* src, triton::uint32 size) {
        if (sectionIndex >= this->sectionContent.size())
          throw triton::exceptions::Pe("PeBuilder::writeToSection: section index out of range");

        if (dest+size > this->sectionContent[sectionIndex].size())
          throw triton::exceptions::Pe("PeBuilder::writeToSection: trying to write past end of section");

        std::memcpy(&this->sectionContent[sectionIndex][dest], src, size);
      }


      void PeBuilder::readFromRVA(void* dest, triton::uint32 src, triton::uint32 size) {
        triton::uint32 index   = this->getSectionIndexForRVA(src);
        triton::uint32 rawAddr = this->header.getSectionHeaders()[index].getVirtualAddress();

        this->readFromSection(index, dest, src - rawAddr, size);
      }


      void PeBuilder::writeToRVA(triton::uint32 dest, void* src, triton::uint32 size) {
        triton::uint32 index   = this->getSectionIndexForRVA(dest);
        triton::uint32 rawAddr = this->header.getSectionHeaders()[index].getVirtualAddress();

        this->writeToSection(index, dest-rawAddr, src, size);
      }


      void PeBuilder::save(const std::string& path) {
        std::ofstream os;

        os.open(path, std::ios_base::out | std::ios_base::binary);
        if (!os)
          throw triton::exceptions::Pe("Pe::save(): Cannot open the binary file for saving.");

        this->header.save(os);

        for (triton::usize i = 0; i < header.getSectionHeaders().size(); ++i) {
          os.seekp(this->header.getSectionHeaders()[i].getRawAddress());
          os.write(reinterpret_cast<char*>(&this->sectionContent[i][0]), this->header.getSectionHeaders()[i].getRawSize());
        }

        os.flush();
      }

    }; /* pe namespace */
  }; /* format namespace */
}; /* triton namespace */
