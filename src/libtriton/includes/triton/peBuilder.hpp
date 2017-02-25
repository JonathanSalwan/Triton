//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_PEBUILDER_H
#define TRITON_PEBUILDER_H

#include <iostream>
#include <vector>

#include <triton/pe.hpp>



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

      /*! \class PeBuilder
       *  \brief A mutable PE container. */
      class PeBuilder : public Pe {
        protected:
          //! Content of each section
          std::vector<std::vector<triton::uint8>> sectionContent;

        public:
          //! Constructor.
          PeBuilder(const std::string& path);

          //! Destructor.
          virtual ~PeBuilder();

          //! Returns which section the specified RVA is located in, using the mutable state.
          triton::uint32 getSectionIndexForRVA(triton::uint64 vaddr) const;

          //! Adds a new section to the binary.
          void addSection(const std::string& name, triton::uint32 vsize, triton::uint32 rawsize, triton::uint32 characteristics);

          //! Returns the entire content of the specified section.
          const std::vector<triton::uint8> getSectionContent(triton::uint32 sectionIndex);

          //! Reads data from the specified section to dest, starting at src (relative to section start). It can't read past the end of the section.
          void readFromSection(triton::uint32 sectionIndex, void* dest, triton::uint32 src, triton::uint32 size);

          //! Writes data to the specified section from src, starting at dest (relative to section start). It can't write past the end of the section.
          void writeToSection(triton::uint32 sectionIndex, triton::uint32 dest, void* src, triton::uint32 size);

          //! Reads data from the specified address (relative to image base)
          void readFromRVA(void* dest, triton::uint32 src, triton::uint32 size);

          //! Writes data to the specified address (relative to image base)
          void writeToRVA(triton::uint32 dest, void* src, triton::uint32 size);

          //! Saves the file conents.
          void save(const std::string& path);
      };

    /*! @} End of pe namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_PEBUILDER_H */
