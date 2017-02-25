//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_PEOPTIONALHEADER_H
#define TRITON_PEOPTIONALHEADER_H

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

      /*!
       * \description This struct contains the "PE32" (32-bit) version of the optional header.
       * The fields map to the equivalent field in PeOptionalHeader.
       */
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

      /*!
       * \description This struct contains the "PE32+" (64-bit) version of the optional header.
       * The fields map to the equivalent field in PeOptionalHeader.
       */
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

      /*! \class PeOptionalHeader
       *  \brief PE optional header */
      class PeOptionalHeader {
        protected:
          /*!
           * \description The unsigned integer that identifies the state of the image file. The most common number is 0x10B, which identifies it as a normal executable file. 0x107 identifies it as a ROM image, and 0x20B identifies it as a PE32+ executable.
           */
          triton::uint16 magic;

          /*!
           * \description The linker major version number.
           */
          triton::uint8 majorLinkerVersion;

          /*!
           * \description The linker minor version number.
           */
          triton::uint8 minorLinkerVersion;

          /*!
           * \description The size of the code (text) section, or the sum of all code sections if there are multiple sections.
           */
          triton::uint32 sizeOfCode;

          /*!
           * \description The size of the initialized data section, or the sum of all such sections if there are multiple data sections.
           */
          triton::uint32 sizeOfInitializedData;

          /*!
           * \description The size of the uninitialized data section (BSS), or the sum of all such sections if there are multiple BSS sections.
           */
          triton::uint32 sizeOfUninitializedData;

          /*!
           * \description The address of the entry point relative to the image base when the executable file is loaded into memory. For program images, this is the starting address. For device drivers, this is the address of the initialization function. An entry point is optional for DLLs. When no entry point is present, this field must be zero.
           */
          triton::uint32 addressOfEntryPoint;

          /*!
           * \description The address that is relative to the image base of the beginning-of-code section when it is loaded into memory.
           */
          triton::uint32 baseOfCode;

          /*!
           * \description The address that is relative to the image base of the beginning-of-data section when it is loaded into memory.
           */
          triton::uint32 baseOfData;

          /*!
           * \description The preferred address of the first byte of image when loaded into memory; must be a multiple of 64 K. The default for DLLs is 0x10000000. The default for Windows CE EXEs is 0x00010000. The default for Windows NT, Windows 2000, Windows XP, Windows 95, Windows 98, and Windows Me is 0x00400000.
           */
          triton::uint64 imageBase;

          /*!
           * \description The alignment (in bytes) of sections when they are loaded into memory. It must be greater than or equal to FileAlignment. The default is the page size for the architecture.
           */
          triton::uint32 sectionAlignment;

          /*!
           * \description The alignment factor (in bytes) that is used to align the raw data of sections in the image file. The value should be a power of 2 between 512 and 64 K, inclusive. The default is 512. If the SectionAlignment is less than the architecture’s page size, then FileAlignment must match SectionAlignment.
           */
          triton::uint32 fileAlignment;

          /*!
           * \description The major version number of the required operating system.
           */
          triton::uint16 majorOperatingSystemVersion;

          /*!
           * \description The minor version number of the required operating system.
           */
          triton::uint16 minorOperatingSystemVersion;

          /*!
           * \description The major version number of the image.
           */
          triton::uint16 majorImageVersion;

          /*!
           * \description The minor version number of the image.
           */
          triton::uint16 minorImageVersion;

          /*!
           * \description The major version number of the subsystem.
           */
          triton::uint16 majorSubsystemVersion;

          /*!
           * \description The minor version number of the subsystem.
           */
          triton::uint16 minorSubsystemVersion;

          /*!
           * \description Reserved, must be zero.
           */
          triton::uint32 win32VersionValue;

          /*!
           * \description The size (in bytes) of the image, including all headers, as the image is loaded in memory. It must be a multiple of SectionAlignment.
           */
          triton::uint32 sizeOfImage;

          /*!
           * \description The combined size of an MS‑DOS stub, PE header, and section headers rounded up to a multiple of FileAlignment.
           */
          triton::uint32 sizeOfHeaders;

          /*!
           * \description The image file checksum.
           */
          triton::uint32 checkSum;

          /*!
           * \description The subsystem that is required to run this image.
           */
          triton::uint16 subsystem;

          /*!
           * \description DLL Characteristics.
           */
          triton::uint16 dllCharacteristics;

          /*!
           * \description The size of the stack to reserve. Only SizeOfStackCommit is committed; the rest is made available one page at a time until the reserve size is reached.
           */
          triton::uint64 sizeOfStackReserve;

          /*!
           * \description The size of the stack to commit.
           */
          triton::uint64 sizeOfStackCommit;

          /*!
           * \description The size of the local heap space to reserve. Only SizeOfHeapCommit is committed; the rest is made available one page at a time until the reserve size is reached.
           */
          triton::uint64 sizeOfHeapReserve;

          /*!
           * \description The size of the local heap space to commit.
           */
          triton::uint64 sizeOfHeapCommit;

          /*!
           * \description Reserved, must be zero.
           */
          triton::uint32 loaderFlags;

          /*!
           * \description The number of data-directory entries in the remainder of the optional header. Each describes a location and size.
           */
          triton::uint32 numberOfRvaAndSizes;

          //! Copies from a PE32_OptionalHeader object.
          PeOptionalHeader& operator=(const PE32_OptionalHeader& other);

          //! Copies from a PE32Plus_OptionalHeader object.
          PeOptionalHeader& operator=(const PE32Plus_OptionalHeader& other);

          //! Copies to a PE32_OptionalHeader object.
          void assign(PE32_OptionalHeader& target) const;

          //! Copies to a PE32Plus_OptionalHeader object.
          void assign(PE32Plus_OptionalHeader& target) const;

        public:
          //! Constructor.
          PeOptionalHeader();

          //! Copy constructor.
          PeOptionalHeader(const PeOptionalHeader& copy);

          //! Copy assignment operator.
          PeOptionalHeader& operator=(const PeOptionalHeader& copy);

          //! Destructor.
          ~PeOptionalHeader();

          //! Returns the size of the structure.
          triton::uint32 getSize(void) const;

          //! Parses the header.
          triton::usize parse(const triton::uint8* raw);

          //! Saves the header to file.
          void save(std::ostream& os) const;

          //! Returns the magic.
          triton::uint16 getMagic(void) const;

          //! Returns the majorLinkerVersion.
          triton::uint8 getMajorLinkerVersion(void) const;

          //! Returns the minorLinkerVersion.
          triton::uint8 getMinorLinkerVersion(void) const;

          //! Returns the sizeOfCode.
          triton::uint32 getSizeOfCode(void) const;

          //! Returns the sizeOfInitializedData.
          triton::uint32 getSizeOfInitializedData(void) const;

          //! Returns the sizeOfUninitializedData.
          triton::uint32 getSizeOfUninitializedData(void) const;

          //! Returns the addressOfEntryPoint.
          triton::uint32 getAddressOfEntryPoint(void) const;

          //! Returns the baseOfCode.
          triton::uint32 getBaseOfCode(void) const;

          //! Returns the baseOfData.
          triton::uint32 getBaseOfData(void) const;

          //! Returns the imageBase.
          triton::uint64 getImageBase(void) const;

          //! Returns the sectionAlignment.
          triton::uint32 getSectionAlignment(void) const;

          //! Returns the fileAlignment.
          triton::uint32 getFileAlignment(void) const;

          //! Returns the majorOperatingSystemVersion.
          triton::uint16 getMajorOperatingSystemVersion(void) const;

          //! Returns the minorOperatingSystemVersion.
          triton::uint16 getMinorOperatingSystemVersion(void) const;

          //! Returns the majorImageVersion.
          triton::uint16 getMajorImageVersion(void) const;

          //! Returns the minorImageVersion.
          triton::uint16 getMinorImageVersion(void) const;

          //! Returns the majorSubsystemVersion.
          triton::uint16 getMajorSubsystemVersion(void) const;

          //! Returns the minorSubsystemVersion.
          triton::uint16 getMinorSubsystemVersion(void) const;

          //! Returns the win32VersionValue.
          triton::uint32 getWin32VersionValue(void) const;

          //! Returns the sizeOfImage.
          triton::uint32 getSizeOfImage(void) const;

          //! Sets the sizeOfImage.
          void setSizeOfImage(triton::uint32 setSizeOfImage);

          //! Returns the sizeOfHeaders.
          triton::uint32 getSizeOfHeaders(void) const;

          //! Sets the sizeOfHeaders.
          void setSizeOfHeaders(triton::uint32);

          //! Returns the checkSum.
          triton::uint32 getCheckSum(void) const;

          //! Returns the subsystem.
          triton::uint16 getSubsystem(void) const;

          //! Returns the dllCharacteristics.
          triton::uint16 getDllCharacteristics(void) const;

          //! Returns the sizeOfStackReserve.
          triton::uint64 getSizeOfStackReserve(void) const;

          //! Returns the sizeOfStackCommit.
          triton::uint64 getSizeOfStackCommit(void) const;

          //! Returns the sizeOfHeapReserve.
          triton::uint64 getSizeOfHeapReserve(void) const;

          //! Returns the sizeOfHeapCommit.
          triton::uint64 getSizeOfHeapCommit(void) const;

          //! Returns the loaderFlags.
          triton::uint32 getLoaderFlags(void) const;

          //! Returns the numberOfRvaAndSizes.
          triton::uint32 getNumberOfRvaAndSizes(void) const;
      };

    /*! @} End of pe namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_PEOPTIONALHEADER_H */
