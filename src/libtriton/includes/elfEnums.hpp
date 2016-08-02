//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ELFENUMS_H
#define TRITON_ELFENUMS_H



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

      /*!
       *  \brief Some useful ELF enums.
       *  \description This list is not exhaustive, it contains only used enums by the libTriton.
       */
      enum elf_e {
        EI_NIDENT         = 16,             //!< Size of the ident array.

        ELFCLASSNONE      = 0,              //!< This class is invalid.
        ELFCLASS32        = 1,              //!< This  defines the 32-bit architecture. It supports machines with files and virtual address spaces up to 4 Gigabytes.
        ELFCLASS64        = 2,              //!< This defines the 64-bit architecture.

        ELFDATANONE       = 0,              //!< Unknown data format.
        ELFDATA2LSB       = 1,              //!< Two's complement, little-endian.
        ELFDATA2MSB       = 2,              //!< Two's complement, big-endian.

        PF_X              = 1,              //!< An executable segment.
        PF_W              = 2,              //!< A writable segment.
        PF_R              = 4,              //!< A readable segment.

        PT_NULL           = 0,              //!< The array element is unused and the other members' values are undefined. This lets the program header have ignored entries.
        PT_LOAD           = 1,              //!< The  array element specifies a loadable segment, described by p_filesz and p_memsz. The bytes from the file are mapped to the beginning of the memory segment. If the segment's memory size p_memsz is larger than the file size p_filesz, the "extra" bytes are defined to hold the value 0 and to follow the segment's initialized area. The file size may not be larger than the memory size. Loadable segment entries in the program header table appear in ascending order, sorted on the p_vaddr member.
        PT_DYNAMIC        = 2,              //!< The array element specifies dynamic linking information.
        PT_INTERP         = 3,              //!< The array element specifies the location and size of a null-terminated pathname to invoke as an interpreter. This segment type is meaningful only for executable files (though it may occur for shared objects). However it may not occur more than once in a file. If it is present, it must precede any loadable segment entry.
        PT_NOTE           = 4,              //!< The array element specifies the location and size for auxiliary information.
        PT_SHLIB          = 5,              //!< This segment type is reserved but has unspecified semantics. Programs that contain a array element of this type do not conform to the ABI.
        PT_PHDR           = 6,              //!< The array element, if present, specifies the location and size of the program header table itself, both in the file and in the memory image of the program. This segment type may not occur more than once in a file. Moreover, it may occur only if the  program header table is part of the memory image of the program. If it is present, it must precede any loadable segment entry.
        PT_GNU_EH_FRAME   = 0x6474e550,     //!< The array element specifies the location and size of the exception handling information as defined by the .eh_frame_hdr section.
        PT_GNU_STACK      = 0x6474e551,     //!< GNU extension which is used by the Linux kernel to control the state of the stack via the flags set in the p_flags member.
        PT_GNU_RELRO      = 0x6474e552,
        PT_LOPROC         = 0x70000000,     //!< Values in the inclusive range [PT_LOPROC, PT_HIPROC] are reserved for processor-specific semantics.
        PT_HIPROC         = 0x7fffffff,     //!< Values in the inclusive range [PT_LOPROC, PT_HIPROC] are reserved for processor-specific semantics.

        SHN_UNDEF         = 0,              //!< Undefined section.
        SHN_XINDEX        = 0xffff,         //!< This value is an escape value. It indicates that the actual section header index is too large to fit in the containing field and is to be found in another location (specific to the structure where it appears).

        SHF_WRITE         = 1,              //!< This section contains data that should be writable during process execution.
        SHF_ALLOC         = 2,              //!< This section occupies memory during process execution. Some control sections do not reside in the memory image of an object file. This attribute is off for those sections.
        SHF_EXECINSTR     = 4,              //!< This section contains executable machine instructions.
        SHF_MASKPROC      = 0xf0000000,     //!< All bits included in this mask are reserved for processor-specific semantics.

        SHT_NULL          = 0,              //!< This value marks the section header as inactive.  It does not have an associated section. Other members of the section header have undefined values.
        SHT_PROGBITS      = 1,              //!< This section  holds information defined by the program, whose format and meaning are determined solely by the program.
        SHT_SYMTAB        = 2,              //!< This section holds a symbol table. Typically, SHT_SYMTAB provides symbols for link editing, though it may also be used for dynamic linking. As a complete symbol table, it may contain many symbols unnecessary for dynamic linking. An object file can also contain a SHT_DYNSYM section.
        SHT_STRTAB        = 3,              //!< This section holds a string table. An object file may have multiple string table sections.
        SHT_RELA          = 4,              //!< This section holds relocation entries with explicit addends, such as type Elf32_Rela for the 32-bit class of object files. An object may have multiple relocation sections.
        SHT_HASH          = 5,              //!< This section holds a symbol hash table. An object participating in dynamic linking must contain a symbol hash table. An object file may have only one hash table.
        SHT_DYNAMIC       = 6,              //!< This section holds information for dynamic linking. An object file may have only one dynamic section.
        SHT_NOTE          = 7,              //!< This section holds information that marks the file in some way.
        SHT_NOBITS        = 8,              //!< A section of this type occupies no space in the file but otherwise resembles SHT_PROGBITS. Although this section contains no bytes, the sh_offset member contains the conceptual file offset.
        SHT_REL           = 9,              //!< This section holds relocation offsets without explicit addends, such as type Elf32_Rel for the 32-bit class of object files. An object file may have multiple relocation sections.
        SHT_SHLIB         = 10,             //!< This section is reserved but has unspecified semantics.
        SHT_DYNSYM        = 11,             //!< This section holds a minimal set of dynamic linking symbols. An object file can also contain a SHT_SYMTAB section.
        SHT_SYMTAB_SHNDX  = 18,             //!< This section is associated with a symbol table section and is required if any of the section header indexes referenced by that symbol table contain the escape value SHN_XINDEX. The section is an array of Elf32_Word values. Each value corresponds one to one with a symbol table entry and appear in the same order as those entries. The values represent the section header indexes against which the symbol table entries are defined. Only if the corresponding symbol table entry's st_shndx field contains the escape value SHN_XINDEX will the matching Elf32_Word hold the actual section header index; otherwise, the entry must be SHN_UNDEF (0).
        SHT_LOPROC        = 0x70000000,     //!< Values in the inclusive range [SHT_LOPROC, SHT_HIPROC] are reserved for processor-specific semantics.
        SHT_HIPROC        = 0x7fffffff,     //!< Values in the inclusive range [SHT_LOPROC, SHT_HIPROC] are reserved for processor-specific semantics.
        SHT_LOUSER        = 0x80000000,     //!< This value specifies the lower bound of the range of indices reserved for application programs.
        SHT_HIUSER        = 0x8fffffff,     //!< This value specifies the upper bound of the range of indices reserved for application programs. Section types between SHT_LOUSER and SHT_HIUSER may be used by the application, without conflicting with current or future system-defined section types.

        DT_NULL           = 0,              //!< Marks end of dynamic section.
        DT_NEEDED         = 1,              //!< String table offset to name of a needed library.
        DT_PLTRELSZ       = 2,              //!< Size in bytes of PLT relocation entries.
        DT_PLTGOT         = 3,              //!< Address of PLT and/or GOT.
        DT_HASH           = 4,              //!< Address of symbol hash table.
        DT_STRTAB         = 5,              //!< Address of string table.
        DT_SYMTAB         = 6,              //!< Address of symbol table.
        DT_RELA           = 7,              //!< Address of Rela relocation table.
        DT_RELASZ         = 8,              //!< Size in bytes of the Rela relocation table.
        DT_RELAENT        = 9,              //!< Size in bytes of a Rela relocation table entry.
        DT_STRSZ          = 10,             //!< Size in bytes of string table.
        DT_SYMENT         = 11,             //!< Size in bytes of a symbol table entry.
        DT_INIT           = 12,             //!< Address of the initialization function.
        DT_FINI           = 13,             //!< Address of the termination function.
        DT_SONAME         = 14,             //!< String table offset to name of shared object.
        DT_RPATH          = 15,             //!< String table offset to library search path (deprecated).
        DT_SYMBOLIC       = 16,             //!< Alert linker to search this shared object before the executable for symbols.
        DT_REL            = 17,             //!< Address of Rel relocation table.
        DT_RELSZ          = 18,             //!< Size in bytes of Rel relocation table.
        DT_RELENT         = 19,             //!< Size in bytes of a Rel table entry.
        DT_PLTREL         = 20,             //!< Type of relocation entry to which the PLT refers (Rela or Rel).
        DT_DEBUG          = 21,             //!< Undefined use for debugging.
        DT_TEXTREL        = 22,             //!< Absence of this entry indicates that no relocation entries should apply to a nonwritable segment.
        DT_JMPREL         = 23,             //!< Address of relocation entries associated solely with the PLT.
        DT_BIND_NOW       = 24,             //!< Instruct dynamic linker to process all relocations transferring control to the executable.
        DT_INIT_ARRAY     = 25,             //!< The address of an array of pointers to initialization functions.
        DT_FINI_ARRAY     = 26,             //!< The address of an array of pointers to termination functions.
        DT_INIT_ARRAYSZ   = 27,             //!< Size in bytes of DT_INIT_ARRAY
        DT_FINI_ARRAYSZ   = 28,             //!< Size in bytes of DT_FINI_ARRAY
        DT_RUNPATH        = 29,             //!< String table offset to library search path.
        DT_GNU_HASH       = 0x6ffffef5,
        DT_VERSYM         = 0x6ffffff0,
        DT_VERDEF         = 0x6ffffffc,
        DT_VERDEFNUM      = 0x6ffffffd,
        DT_VERNEED        = 0x6ffffffe,
        DT_VERNEEDNUM     = 0x6fffffff,

        STV_DEFAULT       = 0,              //!< Default symbol visibility rules. Global and weak symbols are available to other modules; references in the local module can be interposed by definitions in other modules.
        STV_INTERNAL      = 1,              //!< Processor-specific hidden class.
        STV_HIDDEN        = 2,              //!< Symbol is unavailable to other modules; references in the local module always resolve to the local symbol (i.e., the symbol can't be interposed by definitions in other modules).
        STV_PROTECTED     = 3,              //!< Symbol is available to other modules, but references in the local module always resolve to the local symbol.
      };

    /*! @} End of elf namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ELFENUMS_H */
