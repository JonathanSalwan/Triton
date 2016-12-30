//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_PEHEADER_H
#define TRITON_PEHEADER_H

#include "peEnums.hpp"
#include "peFileHeader.hpp"
#include "peOptionalHeader.hpp"
#include "peDataDirectory.hpp"
#include "peSectionHeader.hpp"
#include "tritonTypes.hpp"

#include <vector>

//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Format namespace
  namespace format {
  /*!
   *  \ingroup triton
   *  \addtogroup format
   *  @{
   */

    //! The PE format namespace
    namespace pe {
    /*!
     *  \ingroup format
     *  \addtogroup pe
     *  @{
     */

      /*! \class PeHeader
       *  \brief The PE Header class. */
      class PeHeader {

        protected:
          triton::uint32 peHeaderStart;
          std::vector<triton::uint8> dosStub;
          PeFileHeader fileHeader;
          PeOptionalHeader optionalHeader;
          PeDataDirectory dataDirectory;
          std::vector<PeSectionHeader> sectionHeaders;

          //! Align offset according to fileAlignment
          triton::uint32 fileAlign(triton::uint32 offset) const;

          //! Align RVA according to sectionAlignment
          triton::uint32 sectionAlign(triton::uint32 rva) const;

          //! Gets the total section virtual size (aligned), used when adding new sections
          triton::uint32 getTotalSectionVirtualSize() const;
          //! Gets the total section raw size (aligned), used when adding new sections
          triton::uint32 getTotalSectionRawSize() const;

        public:
          //! Constructor.
          PeHeader();

          //! Constructor by copy.
          PeHeader(const PeHeader& copy);

          //! Destructor.
          virtual ~PeHeader();

          //! Copies a PeHeader.
          PeHeader &operator=(const PeHeader& copy);

          //! Parses the PE Header. Returns the number of bytes read.
          triton::uint32 parse(const triton::uint8* raw, triton::usize totalSize);

          //! Saves the header to file.
          void save(std::ostream &os) const;

          const PeFileHeader &getFileHeader() const;
          const PeOptionalHeader &getOptionalHeader() const;
          const PeDataDirectory &getDataDirectory() const;
          const std::vector<PeSectionHeader> &getSectionHeaders() const;

          //! Adds a new section header.
          void addSection(const std::string name, triton::uint32 vsize, triton::uint32 rawsize, triton::uint32 characteristics);

          triton::uint32 getSize() const;
      };

    /*! @} End of pe namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_PEHEADER_H */
