//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ELFDYNAMICTABLE_H
#define TRITON_ELFDYNAMICTABLE_H

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

      //! The ELF (32-bits) dynamic table structure.
      typedef struct Elf32_Dyn {
        triton::sint32 d_tag;
        triton::uint32 d_val;
      } Elf32_Dyn_t;

      //! The ELF (64-bits) dynamic table structure.
      typedef struct Elf64_Dyn {
        triton::sint64 d_tag;
        triton::uint64 d_val;
      } Elf64_Dyn_t;

      /*! \class ElfDynamicTable
       *  \brief The ELF dynamic table class. */
      class ElfDynamicTable {

        protected:
        /*!
         * \description This member describes the kind of the entry. E.g: DT_STRTAB, DT_SYMTAB, DT_NEEDED...
         */
        triton::sint64 tag;

        /*!
         * \description This member represents integer values with various interpretations.
         */
        triton::uint64 value;

        public:
          //! Constructor.
          ElfDynamicTable();

          //! Constructor by copy.
          ElfDynamicTable(const ElfDynamicTable& copy);

          //! Destructor.
          virtual ~ElfDynamicTable();

          //! Copies an ElfDynamicTable.
          void operator=(const ElfDynamicTable& copy);

          //! Parses the ELF Dynamic Table. Returns the number of bytes read.
          triton::uint32 parse(const triton::uint8* raw, triton::uint8 EIClass);

          //! Returns the tag of the dynamic entry.
          triton::sint64 getTag(void) const;

          //! Returns the value of the dynamic entry.
          triton::uint64 getValue(void) const;
      };

    /*! @} End of elf namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ELFDYNAMICTABLE_H */
