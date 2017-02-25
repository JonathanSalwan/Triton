//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ELFPROGRAMHEADER_H
#define TRITON_ELFPROGRAMHEADER_H

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

      //! The ELF (32-bits) program header structure.
      typedef struct Elf32_Phdr {
        triton::uint32 p_type;
        triton::uint32 p_offset;
        triton::uint32 p_vaddr;
        triton::uint32 p_paddr;
        triton::uint32 p_filesz;
        triton::uint32 p_memsz;
        triton::uint32 p_flags;
        triton::uint32 p_align;
      } Elf32_Phdr_t;

      //! The ELF (64-bits) program header structure.
      typedef struct Elf64_Phdr {
        triton::uint32 p_type;
        triton::uint32 p_flags;
        triton::uint64 p_offset;
        triton::uint64 p_vaddr;
        triton::uint64 p_paddr;
        triton::uint64 p_filesz;
        triton::uint64 p_memsz;
        triton::uint64 p_align;
      } Elf64_Phdr_t;

      /*! \class ElfProgramHeader
       *  \brief The ELF Program Header class. */
      class ElfProgramHeader {

        protected:
          /*!
           * \description This member indicates what kind of segment this array element describes
           * or how to interpret the array element's information.
           */
          triton::uint32 type;

          /*!
           * \description This member holds a bit mask of flags relevant to the segment (PF_X, PF_W or PF_R).
           */
          triton::uint32 flags;

          /*!
           * \description This member holds the offset from the beginning of the file at which
           * the first byte of the segment resides.
           */
          triton::uint64 offset;

          /*!
           * \description This member holds the virtual address at which the first byte of the
           * segment resides in memory.
           */
          triton::uint64 vaddr;

          /*!
           * \description On systems for which physical addressing is relevant, this member is reserved
           * for the segment's physical address. Under BSD this member is not used and must be zero.
           */
          triton::uint64 paddr;

          /*!
           * \description This member holds the number of bytes in the file image of the segment. It may be zero.
           */
          triton::uint64 filesz;

          /*!
           * \description This member holds the number of bytes in the memory image of the segment. It may be zero.
           */
          triton::uint64 memsz;

          /*!
           * \description This member holds the value to which the segments are aligned in memory and in the file.
           */
          triton::uint64 align;

        public:
          //! Constructor.
          ElfProgramHeader();

          //! Constructor by copy.
          ElfProgramHeader(const ElfProgramHeader& copy);

          //! Destructor.
          virtual ~ElfProgramHeader();

          //! Copies an ElfProgramHeader.
          void operator=(const ElfProgramHeader& copy);

          //! Parses the ELF Program Header. Returns the number of bytes read.
          triton::uint32 parse(const triton::uint8* raw, triton::uint8 EIClass);

          //! Returns the type.
          triton::uint32 getType(void) const;

          //! Returns the type.
          triton::uint32 getFlags(void) const;

          //! Returns the offset.
          triton::uint64 getOffset(void) const;

          //! Returns the virtual address.
          triton::uint64 getVaddr(void) const;

          //! Returns the physical address.
          triton::uint64 getPaddr(void) const;

          //! Returns the file image size.
          triton::uint64 getFilesz(void) const;

          //! Returns the memory image size.
          triton::uint64 getMemsz(void) const;

          //! Returns the segment alignment.
          triton::uint64 getAlign(void) const;
      };

    /*! @} End of elf namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ELFPROGRAMHEADER_H */
