//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_PEFILEHEADER_H
#define TRITON_PEFILEHEADER_H

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

      /*! \class PeFileHeader
       *  \brief PE file header (without DOS stub) */
      class PeFileHeader {
        protected:
          //! The PE file header structure.
          struct {
            /*!
             * \description The number that identifies the type of target machine. See IMAGE_FILE_MACHINE_* in peEnums.hpp
             */
            triton::uint16 machine;

            /*!
             * \description The number of sections. This indicates the size of the section table.
             */
            triton::uint16 numberOfSections;

            /*!
             * \description The low 32 bits of the number of seconds since 00:00 January 1, 1970 (a C run-time time_t value), that indicates when the file was created.
             */
            triton::uint32 timeDateStamp;

            /*!
             * \description The file offset of the COFF symbol table, or zero if no COFF symbol table is present. This value should be zero for an image because COFF debugging information is deprecated.
             */
            triton::uint32 pointerToSymbolTable;

            /*!
             * \description The number of entries in the symbol table. This data can be used to locate the string table, which immediately follows the symbol table. This value should be zero for an image because COFF debugging information is deprecated.
             */
            triton::uint32 numberOfSymbolTable;

            /*!
             * \description The size of the optional header, which is required for executable files but not for object files. This value should be zero for an object file.
             */
            triton::uint16 sizeOfOptionalHeader;

            /*!
             * \description The flags that indicate the attributes of the file. See peEnums.hpp
             */
            triton::uint16 characteristics;
          } st;

      public:
          //! Constructor.
          PeFileHeader();

          //! Copy constructor.
          PeFileHeader(const PeFileHeader& copy);

          //! Copy assignment operator.
          PeFileHeader& operator=(const PeFileHeader& copy);

          //! Destructor.
          ~PeFileHeader();

          //! Returns the size of the structure.
          triton::uint32 getSize(void) const;

          //! Parses the header.
          void parse(const triton::uint8* raw);

          //! Saves the header to file.
          void save(std::ostream& os) const;

          //! Sets the numberOfSections.
          void setNumberOfSections(triton::uint16 numberOfSections);

          //! Returns the machine.
          triton::uint16 getMachine(void) const;

          //! Returns the numberOfSections.
          triton::uint16 getNumberOfSections(void) const;

          //! Returns the timeDateStamp.
          triton::uint32 getTimeDateStamp(void) const;

          //! Returns the pointerToSymbolTable.
          triton::uint32 getPointerToSymbolTable(void) const;

          //! Returns the numberOfSymbolTable.
          triton::uint32 getNumberOfSymbolTable(void) const;

          //! Returns the sizeOfOptionalHeader.
          triton::uint16 getSizeOfOptionalHeader(void) const;

          //! Returns the characteristics.
          triton::uint16 getCharacteristics(void) const;
      };

    /*! @} End of pe namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_PEFILEHEADER_H */
