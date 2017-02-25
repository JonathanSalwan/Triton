//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ELFRELOCATIONTABLE_H
#define TRITON_ELFRELOCATIONTABLE_H

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

      //! The ELF (32-bits) relocation table structure (without addend).
      typedef struct Elf32_Rel {
        triton::uint32 r_offset;
        triton::uint32 r_info;
      } Elf32_Rel_t;

      //! The ELF (64-bits) relocation table structure (without addend).
      typedef struct Elf64_Rel {
        triton::uint64 r_offset;
        triton::uint64 r_info;
      } Elf64_Rel_t;

      //! The ELF (32-bits) relocation table structure (with addend).
      typedef struct Elf32_Rela {
        triton::uint32 r_offset;
        triton::uint32 r_info;
        triton::sint32 r_addend;
      } Elf32_Rela_t;

      //! The ELF (64-bits) relocation table structure (with addend).
      typedef struct Elf64_Rela {
        triton::uint64 r_offset;
        triton::uint64 r_info;
        triton::sint64 r_addend;
      } Elf64_Rela_t;

      /*! \class ElfRelocationTable
       *  \brief The ELF symbol table class. */
      class ElfRelocationTable {

        protected:
          //! Defines if this class is a DT_RELA or a DT_REL.
          bool addendFlag;

          /*!
           * \description This member gives the location at which to apply the relocation action.
           * For a relocatable file, the value is the byte offset from the beginning of the section
           * to the storage unit affected by the relocation. For an executable file or shared object,
           * the value is the virtual address of the storage unit affected by the relocation.
           */
          triton::uint64 offset;

          /*!
           * \description This member gives both the symbol table index with respect to which
           * the relocation must be made and the type of relocation to apply. Relocation types
           * are processor-specific. When the text refers to a relocation entry's relocation type
           * or symbol table index, it means the result of applying ELF[32|64]_R_TYPE or ELF[32|64]_R_SYM,
           * respectively, to the entry's r_info member.
           */
          triton::uint64 info;

          /*!
           * \description This member specifies a constant addend used to compute the value to
           * be stored into the relocatable field.
           */
          triton::sint64 addend;

          /*!
           * \description According to the ElfRelocationTable::info value, this field contains the
           * type of the relocation.
           */
          triton::uint64 type;

          /*!
           * \description According to the ElfRelocationTable::info value, this field contains the
           * index of the corresponding symbol.
           */
          triton::uint64 symidx;

        public:
          //! Constructor.
          ElfRelocationTable();

          //! Constructor by copy.
          ElfRelocationTable(const ElfRelocationTable& copy);

          //! Destructor.
          virtual ~ElfRelocationTable();

          //! Copies an ElfRelocationTable.
          void operator=(const ElfRelocationTable& copy);

          //! Parses the ELF Relocation Table (without addend). Returns the number of bytes read.
          triton::uint32 parseRel(const triton::uint8* raw, triton::uint8 EIClass);

          //! Parses the ELF Relocation Table (with addend). Returns the number of bytes read.
          triton::uint32 parseRela(const triton::uint8* raw, triton::uint8 EIClass);

          //! Returns true if this class is a DT_RELA otherwise false if it's a DT_REL.
          bool isAddend(void) const;

          //! Returns the relocation offset.
          triton::uint64 getOffset(void) const;

          //! Returns the relocation info.
          triton::uint64 getInfo(void) const;

          //! Returns the relocation addend.
          triton::sint64 getAddend(void) const;

          //! Returns the relocation type.
          triton::uint64 getType(void) const;

          //! Returns the relocation symidx
          triton::uint64 getSymidx(void) const;
      };

    /*! @} End of elf namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ELFRELOCATIONTABLE_H */
