//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_PESECTIONHEADER_H
#define TRITON_PESECTIONHEADER_H

#include <vector>

#include <triton/peEnums.hpp>
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

      /*! \class PeSectionHeader
       *  \brief PE Section Header */
      class PeSectionHeader {
        protected:
          //! The PE Section structure.
          struct {
            /*!
             * \description Section name. If it's 8 bytes long then it's not null-terminated.
             */
            triton::uint8 name[8];

            /*!
             * \description The total size of the section when loaded into memory. If this value is greater than SizeOfRawData, the section is zero-padded.
             */
            triton::uint32 virtualSize;

            /*!
             * \description The address of the first byte of the section relative to the image base when the section is loaded into memory.
             */
            triton::uint32 virtualAddress;

            /*!
             * \description the Size of the initialized data on disk.
             */
            triton::uint32 rawSize;

            /*!
             * \description The file pointer to the first page of the section within the file.
             */
            triton::uint32 rawAddress;

            /*!
             * \description The file pointer to the beginning of relocation entries for the section.
             */
            triton::uint32 pointerToRelocations;

            /*!
             * \description The file pointer to the beginning of line-number entries for the section. (deprecated)
             */
            triton::uint32 pointerToLinenumbers;

            /*!
             * \description The number of relocation entries for the section.
             */
            triton::uint16 numberOfRelocations;

            /*!
             * \description The number of line-number entries for the section. (deprecated)
             */
            triton::uint16 numberOfLinenumbers;

            /*!
             * \description The flags that describe the characteristics of the section.
             */
            triton::uint32 characteristics;
          } st;

          /*!
           * \description Section name.
           */
          std::string name;

        public:
          //! Constructor.
          PeSectionHeader();

          //! Copy constructor.
          PeSectionHeader(const PeSectionHeader& copy);

          //! Copy assignment operator.
          PeSectionHeader& operator=(const PeSectionHeader& copy);

          //! Destructor.
          ~PeSectionHeader();

          //! Returns the size of the structure.
          triton::uint32 getSize(void) const;

          //! Parses the section header.
          triton::uint32 parse(const triton::uint8* raw);

          //! Saves the header to file.
          void save(std::ostream& os) const;

          //! Sets the name.
          void setName(const std::string &name);

          //! Returns the name.
          std::string getName(void) const;

          //! Sets the virtualSize.
          void setVirtualSize(triton::uint32 virtualSize);

          //! Returns the virtualSize.
          triton::uint32 getVirtualSize(void) const;

          //! Sets the virtualAddress.
          void setVirtualAddress(triton::uint32 virtualAddress);

          //! Returns the virtualAddress.
          triton::uint32 getVirtualAddress(void) const;

          //! Sets the rawSize.
          void setRawSize(triton::uint32 rawSize);

          //! Returns the rawSize.
          triton::uint32 getRawSize(void) const;

          //! Sets the rawAddress.
          void setRawAddress(triton::uint32 rawAddress);

          //! Returns the rawAddress.
          triton::uint32 getRawAddress(void) const;

          //! Returns the pointerToRelocations.
          triton::uint32 getPointerToRelocations(void) const;

          //! Returns the pointerToLinenumbers.
          triton::uint32 getPointerToLinenumbers(void) const;

          //! Returns the numberOfRelocations.
          triton::uint16 getNumberOfRelocations(void) const;

          //! Returns the numberOfLinenumbers.
          triton::uint16 getNumberOfLinenumbers(void) const;

          //! Sets the characteristics.
          void setCharacteristics(triton::uint32 characteristics);

          //! Returns the characteristics.
          triton::uint32 getCharacteristics(void) const;
      };

    /*! @} End of pe namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_PESECTIONHEADER_H */
