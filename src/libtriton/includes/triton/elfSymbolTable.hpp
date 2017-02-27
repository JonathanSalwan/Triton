//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ELFSYMBOLTABLE_H
#define TRITON_ELFSYMBOLTABLE_H

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

      //! The ELF (32-bits) symbol table structure.
      typedef struct Elf32_Sym {
        triton::uint32 st_name;
        triton::uint32 st_value;
        triton::uint32 st_size;
        triton::uint8  st_info;
        triton::uint8  st_other;
        triton::uint16 st_shndx;
      } Elf32_Sym_t;

      //! The ELF (64-bits) symbol table structure.
      typedef struct Elf64_Sym {
        triton::uint32 st_name;
        triton::uint8  st_info;
        triton::uint8  st_other;
        triton::uint16 st_shndx;
        triton::uint64 st_value;
        triton::uint64 st_size;
      } Elf64_Sym_t;

      /*! \class ElfSymbolTable
       *  \brief The ELF symbol table class. */
      class ElfSymbolTable {

        protected:
        /*!
         * \description This member holds an index into the object file's symbol string table, which
         * holds the character representations of the symbol names. If the value is non-zero, it represents
         * a string table index that gives the symbol name. Otherwise, the symbol table entry has no name.
         */
        triton::uint32 idxname;

        /*!
         * \description This member specifies the name of the symbol as string based on the ElfSymbolTable::idxname.
         */
        std::string name;

        /*!
         * \description This member specifies the symbol's type and binding attributes. A list of the values
         * and meanings appears below.
         */
        triton::uint8 info;

        /*!
         * \description This member currently specifies a symbol's visibility.
         */
        triton::uint8 other;

        /*!
         * \description Every symbol table entry is defined in relation to some section. This member holds
         * the relevant section header table index. As the sh_link and sh_info interpretation table and the
         * related text describe, some section indexes indicate special meanings. If this member contains
         * SHN_XINDEX, then the actual section header index is too large to fit in this field. The actual
         * value is contained in the associated section of type SHT_SYMTAB_SHNDX.
         */
        triton::uint16 shndx;

        /*!
         * \description This member gives the value of the associated symbol. Depending on the context,
         * this may be an absolute value, an address, and so on.
         */
        triton::uint64 value;

        /*!
         * \description Many symbols have associated sizes. For example, a data object's size is the number
         * of bytes contained in the object. This member holds 0 if the symbol has no size or an unknown size.
         */
        triton::uint64 size;

        public:
          //! Constructor.
          ElfSymbolTable();

          //! Constructor by copy.
          ElfSymbolTable(const ElfSymbolTable& copy);

          //! Destructor.
          virtual ~ElfSymbolTable();

          //! Copies an ElfSymbolTable.
          void operator=(const ElfSymbolTable& copy);

          //! Parses the ELF Symbol Table. Returns the number of bytes read.
          triton::uint32 parse(const triton::uint8* raw, triton::uint8 EIClass);

          //! Returns the symbol index name.
          triton::uint32 getIdxname(void) const;

          //! Returns the symbol name.
          const std::string& getName(void) const;

          //! Sets the name as string of the symbol.
          void setName(const std::string& name);

          //! Sets the name as string of the symbol.
          void setName(const triton::uint8 *str);

          //! Returns the symbol info.
          triton::uint8 getInfo(void) const;

          //! Returns the other field of the symbol table structure.
          triton::uint8 getOther(void) const;

          //! Returns the shndx field of the symbol table structure.
          triton::uint16 getShndx(void) const;

          //! Returns the symbol value.
          triton::uint64 getValue(void) const;

          //! Returns the symbol size.
          triton::uint64 getSize(void) const;
      };

    /*! @} End of elf namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ELFSYMBOLTABLE_H */
