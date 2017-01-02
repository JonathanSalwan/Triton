//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_PEHEADER_H
#define TRITON_PEHEADER_H

#include <vector>

#include "peDataDirectory.hpp"
#include "peEnums.hpp"
#include "peFileHeader.hpp"
#include "peOptionalHeader.hpp"
#include "peSectionHeader.hpp"
#include "tritonTypes.hpp"



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
          PeFileHeader fileHeader;
          PeOptionalHeader optionalHeader;
          PeDataDirectory dataDirectory;
          std::vector<PeSectionHeader> sectionHeaders;

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

          const PeFileHeader& getFileHeader(void) const;
          const PeOptionalHeader& getOptionalHeader(void) const;
          const PeDataDirectory& getDataDirectory(void) const;
          const std::vector<PeSectionHeader>& getSectionHeaders(void) const;
      };

    /*! @} End of pe namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_PEHEADER_H */
