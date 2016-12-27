//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_PEHEADER_H
#define TRITON_PEHEADER_H

#include "peEnums.hpp"
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

      //! The PE header structure.

      // PE Header
      typedef struct PEFileHeader {
        triton::uint32 peSignature;
        triton::uint16 machine;
        triton::uint16 numberOfSections;
        triton::uint32 timeDateStamp;
        triton::uint32 pointerToSymbolTable;
        triton::uint32 numberOfSymbolTable;
        triton::uint16 sizeOfOptionalHeader;
        triton::uint16 characteristics;
      } PE_Ehdr_t;

      //32-bit version
      struct PE32_OptionalHeader {
        triton::uint16 magic;
        triton::uint8 majorLinkerVersion;
        triton::uint8 minorLinkerVersion;
        triton::uint32 sizeOfCode;
        triton::uint32 sizeOfInitializedData;
        triton::uint32 sizeOfUninitializedData;
        triton::uint32 addressOfEntryPoint;
        triton::uint32 baseOfCode;
        triton::uint32 baseOfData;
        triton::uint32 imageBase;
        triton::uint32 sectionAlignment;
        triton::uint32 fileAlignment;
        triton::uint16 majorOperatingSystemVersion;
        triton::uint16 minorOperatingSystemVersion;
        triton::uint16 majorImageVersion;
        triton::uint16 minorImageVersion;
        triton::uint16 majorSubsystemVersion;
        triton::uint16 minorSubsystemVersion;
        triton::uint32 win32VersionValue;
        triton::uint32 sizeOfImage;
        triton::uint32 sizeOfHeaders;
        triton::uint32 checkSum;
        triton::uint16 subsystem;
        triton::uint16 dllCharacteristics;
        triton::uint32 sizeOfStackReserve;
        triton::uint32 sizeOfStackCommit;
        triton::uint32 sizeOfHeapReserve;
        triton::uint32 sizeOfHeapCommit;
        triton::uint32 loaderFlags;
        triton::uint32 numberOfRvaAndSizes;
      };

      //64-bit version
      struct PE32Plus_OptionalHeader {
        triton::uint16 magic;
        triton::uint8 majorLinkerVersion;
        triton::uint8 minorLinkerVersion;
        triton::uint32 sizeOfCode;
        triton::uint32 sizeOfInitializedData;
        triton::uint32 sizeOfUninitializedData;
        triton::uint32 addressOfEntryPoint;
        triton::uint32 baseOfCode;
        triton::uint64 imageBase;
        triton::uint32 sectionAlignment;
        triton::uint32 fileAlignment;
        triton::uint16 majorOperatingSystemVersion;
        triton::uint16 minorOperatingSystemVersion;
        triton::uint16 majorImageVersion;
        triton::uint16 minorImageVersion;
        triton::uint16 majorSubsystemVersion;
        triton::uint16 minorSubsystemVersion;
        triton::uint32 win32VersionValue;
        triton::uint32 sizeOfImage;
        triton::uint32 sizeOfHeaders;
        triton::uint32 checkSum;
        triton::uint16 subsystem;
        triton::uint16 dllCharacteristics;
        triton::uint64 sizeOfStackReserve;
        triton::uint64 sizeOfStackCommit;
        triton::uint64 sizeOfHeapReserve;
        triton::uint64 sizeOfHeapCommit;
        triton::uint32 loaderFlags;
        triton::uint32 numberOfRvaAndSizes;
      };

      // PE Optional Header      
      struct PEOptionalHeader {
        triton::uint16 magic;
        triton::uint8 majorLinkerVersion;
        triton::uint8 minorLinkerVersion;
        triton::uint32 sizeOfCode;
        triton::uint32 sizeOfInitializedData;
        triton::uint32 sizeOfUninitializedData;
        triton::uint32 addressOfEntryPoint;
        triton::uint32 baseOfCode;
        triton::uint32 baseOfData;
        triton::uint64 imageBase;
        triton::uint32 sectionAlignment;
        triton::uint32 fileAlignment;
        triton::uint16 majorOperatingSystemVersion;
        triton::uint16 minorOperatingSystemVersion;
        triton::uint16 majorImageVersion;
        triton::uint16 minorImageVersion;
        triton::uint16 majorSubsystemVersion;
        triton::uint16 minorSubsystemVersion;
        triton::uint32 win32VersionValue;
        triton::uint32 sizeOfImage;
        triton::uint32 sizeOfHeaders;
        triton::uint32 checkSum;
        triton::uint16 subsystem;
        triton::uint16 dllCharacteristics;
        triton::uint64 sizeOfStackReserve;
        triton::uint64 sizeOfStackCommit;
        triton::uint64 sizeOfHeapReserve;
        triton::uint64 sizeOfHeapCommit;
        triton::uint32 loaderFlags;
        triton::uint32 numberOfRvaAndSizes;
        PEOptionalHeader &operator=(const PE32_OptionalHeader &other);
        PEOptionalHeader &operator=(const PE32Plus_OptionalHeader &other);
      };

      // PE data directory      
      typedef struct PEDataDirectory {
        triton::uint32 exportTable_rva;
        triton::uint32 exportTable_size;
        triton::uint32 importTable_rva;
        triton::uint32 importTable_size;
        triton::uint32 resourceTable_rva;
        triton::uint32 resourceTable_size;
        triton::uint32 exceptionTable_rva;
        triton::uint32 exceptionTable_size;
        triton::uint32 certificateTable_rva;
        triton::uint32 certificateTable_size;
        triton::uint32 baseRelocationTable_rva;
        triton::uint32 baseRelocationTable_size;
        triton::uint32 debugTable_rva;
        triton::uint32 debugTable_size;
        triton::uint32 architectureTable_rva;
        triton::uint32 architectureTable_size;
        triton::uint32 globalPtr_rva;
        triton::uint32 globalPtr_size;
        triton::uint32 tlsTable_rva;
        triton::uint32 tlsTable_size;
        triton::uint32 loadConfigTable_rva;
        triton::uint32 loadConfigTable_size;
        triton::uint32 boundImportTable_rva;
        triton::uint32 boundImportTable_size;
        triton::uint32 importAddressTable_rva;
        triton::uint32 importAddressTable_size;
        triton::uint32 delayImportDescriptor_rva;
        triton::uint32 delayImportDescriptor_size;
        triton::uint32 clrRuntimeHeader_rva;
        triton::uint32 clrRuntimeHeader_size;
        triton::uint64 reserved;
      } PE_DataDirectory_t;

      // PE Section Header      
      typedef struct PESectionHeader {
        triton::uint8 name[8];
        triton::uint32 virtualSize;
        triton::uint32 virtualAddress;
        triton::uint32 rawSize;
        triton::uint32 rawAddress;
        triton::uint32 pointerToRelocations;
        triton::uint32 pointerToLinenumbers;
        triton::uint16 numberOfRelocations;
        triton::uint16 numberOfLinenumbers;
        triton::uint32 characteristics;
      } PE_Shdr_t;

      /*! \class PEHeader
       *  \brief The PE Header class. */
      class PEHeader {

        protected:
          PEFileHeader fileHeader;
          PEOptionalHeader optionalHeader;
          PEDataDirectory dataDirectory;
          std::vector<PESectionHeader> sectionHeaders;

        public:
          //! Constructor.
          PEHeader();

          //! Constructor by copy.
          PEHeader(const PEHeader& copy);

          //! Destructor.
          virtual ~PEHeader();

          //! Copies a PEHeader.
          void operator=(const PEHeader& copy);

          //! Parses the PE Header. Returns the number of bytes read.
          triton::uint32 parse(const triton::uint8* raw, triton::usize totalSize);

          const PEFileHeader &getFileHeader() const;
          const PEOptionalHeader &getOptionalHeader() const;
          const PEDataDirectory &getDataDirectory() const;
          const std::vector<PESectionHeader> &getSectionHeaders() const;
      };

    /*! @} End of pe namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_PEHEADER_H */
