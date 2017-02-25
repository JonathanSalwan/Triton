//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ELFSECTIONHEADER_H
#define TRITON_ELFSECTIONHEADER_H

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

      //! The ELF (32-bits) section header structure.
      typedef struct Elf32_Shdr {
        triton::uint32 sh_name;
        triton::uint32 sh_type;
        triton::uint32 sh_flags;
        triton::uint32 sh_addr;
        triton::uint32 sh_offset;
        triton::uint32 sh_size;
        triton::uint32 sh_link;
        triton::uint32 sh_info;
        triton::uint32 sh_addralign;
        triton::uint32 sh_entsize;
      } Elf32_Shdr_t;

      //! The ELF (64-bits) section header structure.
      typedef struct Elf64_Shdr {
        triton::uint32 sh_name;
        triton::uint32 sh_type;
        triton::uint64 sh_flags;
        triton::uint64 sh_addr;
        triton::uint64 sh_offset;
        triton::uint64 sh_size;
        triton::uint32 sh_link;
        triton::uint32 sh_info;
        triton::uint64 sh_addralign;
        triton::uint64 sh_entsize;
      } Elf64_Shdr_t;

      /*! \class ElfSectionHeader
       *  \brief The ELF Section Header class. */
      class ElfSectionHeader {

        protected:
        /*!
         * \description This member specifies the name of the section. Its value is an index into the
         * section header string table section, giving the location of a null-terminated string.
         */
        triton::uint32 idxname;

        /*!
         * \description This member specifies the name of the section as string based on the ElfSectionHeader::idxname.
         */
        std::string name;

        /*!
         * \description This member categorizes the section's contents and semantics.
         */
        triton::uint32 type;

        /*!
         * \description Sections support one-bit flags that describe miscellaneous attributes.
         * If a flag bit is set in ElfSectionHeader::flags, the attribute is "on" for the section.
         * Otherwise, the attribute is "off" or does not apply. Undefined attributes are set to zero.
         */
        triton::uint64 flags;

        /*!
         * \description If this section appears in the memory image of a process, this member holds
         * the address at which the section's first byte should reside. Otherwise, the member contains zero.
         */
        triton::uint64 addr;

        /*!
         * \description This member's value holds the byte offset from the beginning of the file to the first
         * byte in the section. One section type, SHT_NOBITS, occupies no space in the  file, and its sh_offset member
         * locates the conceptual placement in the file.
         */
        triton::uint64 offset;

        /*!
         * \description This  member  holds the section's size in bytes. Unless the section type is SHT_NOBITS, the section
         * occupies sh_size bytes in the file. A section of type SHT_NOBITS may have a nonzero size, but it occupies no space
         * in the file.
         */
        triton::uint64 size;

        /*!
         * \description This member holds a section header table index link, whose interpretation depends on the section type.
         */
        triton::uint32 link;

        /*!
         * \description This member holds extra information, whose interpretation depends on the section type.
         */
        triton::uint32 info;

        /*!
         * \description Some sections have address alignment constraints. If a section holds a doubleword, the system must
         * ensure doubleword alignment for the entire section. That is, the value of sh_addr must be congruent to zero,
         * modulo the value of ElfSectionHeader::addralign. Only zero and positive integral powers of two are allowed. Values
         * of zero or one mean the section has no alignment constraints.
         */
        triton::uint64 addralign;

        /*!
         * \description Some sections hold a table of fixed-sized entries, such as a symbol table. For such a section,
         * this member gives the size in bytes for each entry. This member contains zero if the section does not hold
         * a table of fixed-size entries.
         */
        triton::uint64 entsize;

        public:
          //! Constructor.
          ElfSectionHeader();

          //! Constructor by copy.
          ElfSectionHeader(const ElfSectionHeader& copy);

          //! Destructor.
          virtual ~ElfSectionHeader();

          //! Copies an ElfSectionHeader.
          void operator=(const ElfSectionHeader& copy);

          //! Parses the ELF Program Header. Returns the number of bytes read.
          triton::uint32 parse(const triton::uint8* raw, triton::uint8 EIClass);

          //! Returns the section index name.
          triton::uint32 getIdxname(void) const;

          //! Returns the section name.
          const std::string& getName(void) const;

          //! Sets the name as string of the section.
          void setName(const std::string& name);

          //! Sets the name as string of the section.
          void setName(const triton::uint8 *str);

          //! Returns the section type.
          triton::uint32 getType(void) const;

          //! Returns the section flags.
          triton::uint64 getFlags(void) const;

          //! Returns the virtual section address.
          triton::uint64 getAddr(void) const;

          //! Returns the section offset in the binary file.
          triton::uint64 getOffset(void) const;

          //! Returns the section size.
          triton::uint64 getSize(void) const;

          //! Returns the section link.
          triton::uint32 getLink(void) const;

          //! Returns the section info.
          triton::uint32 getInfo(void) const;

          //! Returns the section alignement.
          triton::uint64 getAddralign(void) const;

          //! Returns the size of an section entry.
          triton::uint64 getEntsize(void) const;
      };

    /*! @} End of elf namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ELFSECTIONHEADER_H */
