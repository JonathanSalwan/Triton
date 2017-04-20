//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_PEHEADER_H
#define TRITON_PEHEADER_H

#include <vector>

#include <triton/peDataDirectory.hpp>
#include <triton/peEnums.hpp>
#include <triton/peFileHeader.hpp>
#include <triton/peOptionalHeader.hpp>
#include <triton/peSectionHeader.hpp>
#include <triton/tritonTypes.hpp>



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
          /*!
           * \details Location of the PE File Header.
           */
          triton::uint32 peHeaderStart;

          /*!
           * \details A copy of all the bytes before the PE header, containing the DOS stub and the value of peHeaderStart at offset 0x3C.
           */
          std::vector<triton::uint8> dosStub;

          /*!
           * \details COFF File Header
           */
          PeFileHeader fileHeader;

          /*!
           * \details Optional Header (mandatory for EXEs and DLLs).
           */
          PeOptionalHeader optionalHeader;

          /*!
           * \details Data Directory, formally part of the optional header.
           */
          PeDataDirectory dataDirectory;

          /*!
           * \details The table of section headers.
           */
          std::vector<PeSectionHeader> sectionHeaders;

          //! Align offset according to fileAlignment
          triton::uint32 fileAlign(triton::uint32 offset) const;

          //! Align RVA according to sectionAlignment
          triton::uint32 sectionAlign(triton::uint32 rva) const;

          //! Gets the total section virtual size (aligned), used when adding new sections
          triton::uint32 getTotalSectionVirtualSize(void) const;

          //! Gets the total section raw size (aligned), used when adding new sections
          triton::uint32 getTotalSectionRawSize(void) const;

        public:
          //! Constructor.
          PeHeader();

          //! Constructor by copy.
          PeHeader(const PeHeader& copy);

          //! Destructor.
          virtual ~PeHeader();

          //! Copies a PeHeader.
          PeHeader& operator=(const PeHeader& copy);

          //! Parses the PE Header. Returns the number of bytes read.
          triton::uint32 parse(const triton::uint8* raw, triton::usize totalSize);

          /*!
           * \details Returns the PE File Header.
           */
          const PeFileHeader& getFileHeader(void) const;

          /*!
           * \details Returns the Optional Header.
           */
          const PeOptionalHeader& getOptionalHeader(void) const;

          /*!
           * \details Returns the Data Directory table.
           */
          const PeDataDirectory& getDataDirectory(void) const;

          /*!
           * \details Returns the Section Header table.
           */
          const std::vector<PeSectionHeader>& getSectionHeaders(void) const;

          //! Saves the header to file.
          void save(std::ostream& os) const;

          //! Adds a new section header.
          void addSection(const std::string name, triton::uint32 vsize, triton::uint32 rawsize, triton::uint32 characteristics);

          //! Returns the total size of the header.
          triton::uint32 getSize(void) const;
      };

    /*! @} End of pe namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_PEHEADER_H */
