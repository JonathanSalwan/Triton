//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstdio>
#include <new>
#include <fstream>

#include <peBuilder.hpp>
#include <exceptions.hpp>


namespace triton {
  namespace format {
    namespace pe {

      PeBuilder::PeBuilder(const std::string& path) : Pe(path) {
        sectionContent.resize(header.getSectionHeaders().size());
        for (triton::usize i=0; i<header.getSectionHeaders().size(); ++i) {
            triton::uint32 sz = header.getSectionHeaders()[i].getRawSize();
            sectionContent[i].resize(sz);
            memcpy(&sectionContent[i][0], raw+header.getSectionHeaders()[i].getRawAddress(), sz);
        }
      }

      PeBuilder::~PeBuilder() {
      }

      void PeBuilder::addSection(const std::string name, triton::uint32 vsize, triton::uint32 rawsize, triton::uint32 characteristics) {
          this->header.addSection(name, vsize, rawsize, characteristics);
          std::vector<triton::uint8> cont;
          cont.resize(rawsize);
          sectionContent.push_back(cont);
      };

      void PeBuilder::save(const std::string &path) {
          std::ofstream os;
          os.open(path, std::ios_base::out | std::ios_base::binary);
          if (!os) {
              throw triton::exceptions::Pe("Pe::save(): Cannot open the binary file for saving.");
          }
          header.save(os);
          for (triton::usize i=0; i<header.getSectionHeaders().size(); ++i) {
              os.seekp(header.getSectionHeaders()[i].getRawAddress());
              os.write((char*)(&sectionContent[i][0]),header.getSectionHeaders()[i].getRawSize());
          }
          os.flush();
      }

    }; /* pe namespace */
  }; /* format namespace */
}; /* triton namespace */
