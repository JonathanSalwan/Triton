//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_ELFENUMS_H
#define TRITON_ELFENUMS_H



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The Format namespace
  namespace format {
  /*!
   *  \ingroup triton
   *  \addtogroup format
   *  @{
   */

    //! \module The ELF format namespace
    namespace elf {
    /*!
     *  \ingroup format
     *  \addtogroup elf
     *  @{
     */

      /*!
       *  \brief Some useful ELF enums.
       *  \description This list is not exhaustive, it contains only used enums by the libTriton.
       */
      enum elf_e {
        EI_NIDENT         = 16,
        ELFCLASS32        = 1,
        ELFCLASS64        = 2,
        ELFCLASSNONE      = 0,
        ELFDATA2LSB       = 1,
        ELFDATA2MSB       = 2,
        ELFDATANONE       = 0,
        PF_R              = 4,
        PF_W              = 2,
        PF_X              = 1,
        PT_DYNAMIC        = 2,
        PT_GNU_EH_FRAME   = 0x6474e550,
        PT_GNU_RELRO      = 0x6474e552,
        PT_GNU_STACK      = 0x6474e551,
        PT_HIPROC         = 0x7fffffff,
        PT_INTERP         = 3,
        PT_LOAD           = 1,
        PT_LOPROC         = 0x70000000,
        PT_NOTE           = 4,
        PT_NULL           = 0,
        PT_PHDR           = 6,
        PT_SHLIB          = 5,
        SHF_ALLOC         = 2,
        SHF_EXECINSTR     = 4,
        SHF_MASKPROC      = 0xf0000000,
        SHF_WRITE         = 1,
        SHN_UNDEF         = 0,
        SHN_XINDEX        = 0xffff,
        SHT_DYNAMIC       = 6,
        SHT_DYNSYM        = 11,
        SHT_HASH          = 5,
        SHT_HIPROC        = 0x7fffffff,
        SHT_HIUSER        = 0x8fffffff,
        SHT_LOPROC        = 0x70000000,
        SHT_LOUSER        = 0x80000000,
        SHT_NOBITS        = 8,
        SHT_NOTE          = 7,
        SHT_NULL          = 0,
        SHT_PROGBITS      = 1,
        SHT_REL           = 9,
        SHT_RELA          = 4,
        SHT_SHLIB         = 10,
        SHT_STRTAB        = 3,
        SHT_SYMTAB        = 2,
      };

    /*! @} End of elf namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ELFENUMS_H */
