//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ELFHEADER_H
#define TRITON_ELFHEADER_H

#include <triton/elfEnums.hpp>
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

    //! The ELF format namespace
    namespace elf {
    /*!
     *  \ingroup format
     *  \addtogroup elf
     *  @{
     */

      //! The ELF (32-bits) header structure.
      typedef struct Elf32_Ehdr {
        triton::uint8  e_ident[triton::format::elf::EI_NIDENT];
        triton::uint16 e_type;
        triton::uint16 e_machine;
        triton::uint32 e_version;
        triton::uint32 e_entry;
        triton::uint32 e_phoff;
        triton::uint32 e_shoff;
        triton::uint32 e_flags;
        triton::uint16 e_ehsize;
        triton::uint16 e_phentsize;
        triton::uint16 e_phnum;
        triton::uint16 e_shentsize;
        triton::uint16 e_shnum;
        triton::uint16 e_shstrndx;
      } Elf32_Ehdr_t;

      //! The ELF (64-bits) header structure.
      typedef struct Elf64_Ehdr {
        triton::uint8  e_ident[triton::format::elf::EI_NIDENT];
        triton::uint16 e_type;
        triton::uint16 e_machine;
        triton::uint32 e_version;
        triton::uint64 e_entry;
        triton::uint64 e_phoff;
        triton::uint64 e_shoff;
        triton::uint32 e_flags;
        triton::uint16 e_ehsize;
        triton::uint16 e_phentsize;
        triton::uint16 e_phnum;
        triton::uint16 e_shentsize;
        triton::uint16 e_shnum;
        triton::uint16 e_shstrndx;
      } Elf64_Ehdr_t;

      /*! \class ElfHeader
       *  \brief The ELF Header class. */
      class ElfHeader {

        protected:
          /*!
           * \description This array of bytes specifies how to interpret the file.
           */
          triton::uint8 ident[triton::format::elf::EI_NIDENT];

          /*!
           * \description This member identifies the object file type.
           */
          triton::uint16 type;

          /*!
           * \description This member specifies the required architecture for an individual file.
           */
          triton::uint16 machine;

          /*!
           * \description This member identifies the file version.
           */
          triton::uint32 version;

          /*!
           *  \description This member gives the virtual address to which the system first transfers control,
           *  thus starting the process. If the file has no associated entry point, this member holds zero.
           */
          triton::uint64 entry;

          /*!
           *  \description This member holds the program header table's file offset in bytes.
           *  If the file has no program header table, this member holds zero.
           */
          triton::uint64 phoff;

          /*!
           *  \description This member holds the section header table's file offset in bytes.
           *  If the file has no section header table, this member holds zero.
           */
          triton::uint64 shoff;

          /*!
           * \description This member holds processor-specific flags associated with the file.
           */
          triton::uint32 flags;

          /*!
           * \description This member holds the ELF header's size in bytes.
           */
          triton::uint16 ehsize;

          /*!
           *  \description This member holds the size in bytes of one entry in the file's
           *  program header table - all entries are the same size.
           */
          triton::uint16 phentsize;

          /*!
           *  \description This member holds the number of entries in the program header table.
           *  Thus the product of e_phentsize and e_phnum gives the table's size in bytes.
           */
          triton::uint16 phnum;

          /*!
           *  \description This member holds a sections header's size in bytes. A section header is one entry
           *  in the section header table - all entries are the same size.
           */
          triton::uint16 shentsize;

          /*!
           *  \description This member holds the number of entries in the section header table. Thus the product
           *  of ElfHeader::shentsize and ElfHeader::shnum gives the section header table's size in bytes.
           */
          triton::uint16 shnum;

          /*!
           *  \description This member holds the section header table index of the entry associated
           *  with the section name string table. If the file has no section name string table, this
           *  member holds the value triton::format::elf::SHN_UNDEF.
           */
          triton::uint16 shstrndx;

        public:
          //! Constructor.
          ElfHeader();

          //! Constructor by copy.
          ElfHeader(const ElfHeader& copy);

          //! Destructor.
          virtual ~ElfHeader();

          //! Copies an ElfHeader.
          void operator=(const ElfHeader& copy);

          //! Parses the ELF Header. Returns the number of bytes read.
          triton::uint32 parse(const triton::uint8* raw);

          //! Returns the architecture size of this binary (ELFCLASS32, ELFCLASS64 or ELFCLASSNONE).
          triton::uint8 getEIClass(void) const;

          //! Returns the endianness of the binary (ELFDATA2LSB, ELFDATA2MSB or ELFDATANONE).
          triton::uint8 getEIData(void) const;

          //! Returns the type.
          triton::uint16 getType(void) const;

          //! Returns the machine.
          triton::uint16 getMachine(void) const;

          //! Returns the version.
          triton::uint32 getVersion(void) const;

          //! Returns the entry point.
          triton::uint64 getEntry(void) const;

          //! Returns the program header offset.
          triton::uint64 getPhoff(void) const;

          //! Returns the section header offset.
          triton::uint64 getShoff(void) const;

          //! Returns the flags.
          triton::uint32 getFlags(void) const;

          //! Returns the ELF header size.
          triton::uint16 getEhsize(void) const;

          //! Returns the program header entry size.
          triton::uint16 getPhentsize(void) const;

          //! Returns the number of program header entry.
          triton::uint16 getPhnum(void) const;

          //! Returns the section header entry size.
          triton::uint16 getShentsize(void) const;

          //! Returns the number of section header entry.
          triton::uint16 getShnum(void) const;

          //! Returns the index of the string table.
          triton::uint16 getShstrndx(void) const;

          //! Returns the max possible size of an ELF Header.
          triton::uint32 getMaxHeaderSize() const;
      };

    /*! @} End of elf namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ELFHEADER_H */
