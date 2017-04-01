//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ELF_H
#define TRITON_ELF_H

#include <iostream>
#include <vector>

#include <triton/binaryInterface.hpp>
#include <triton/elfDynamicTable.hpp>
#include <triton/elfEnums.hpp>
#include <triton/elfHeader.hpp>
#include <triton/elfProgramHeader.hpp>
#include <triton/elfRelocationTable.hpp>
#include <triton/elfSectionHeader.hpp>
#include <triton/elfSymbolTable.hpp>
#include <triton/memoryMapping.hpp>
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

      /*! \class Elf
       *  \brief The ELF format class. */
      class Elf : public BinaryInterface {
        protected:
          //! Path file of the binary.
          std::string path;

          //! Total size of the binary file.
          triton::usize totalSize;

          //! The raw binary.
          std::vector<triton::uint8> raw;

          //! The ELF Header
          triton::format::elf::ElfHeader header;

          //! The Program Headers
          std::vector<triton::format::elf::ElfProgramHeader> programHeaders;

          //! The Section Headers
          std::vector<triton::format::elf::ElfSectionHeader> sectionHeaders;

          //! The dynamic table.
          std::vector<triton::format::elf::ElfDynamicTable> dynamicTable;

          //! The symbols table.
          std::vector<triton::format::elf::ElfSymbolTable> symbolsTable;

          //! The relocations table.
          std::vector<triton::format::elf::ElfRelocationTable> relocationsTable;

          //! The shared libraries dependency.
          std::vector<std::string> sharedLibraries;

          /*!
           * \description The list of memory areas which may be mapped into the Triton memory.
           * In the ELF context, this is basically all segments.
           */
          std::list<triton::format::MemoryMapping> memoryMapping;

          //! Open the binary.
          void open(void);

          //! Parse the binary.
          bool parse(void);

          //! Init the memory mapping.
          void initMemoryMapping(void);

          //! Init the dynamic table.
          void initDynamicTable(void);

          //! Init the list of shared libraries dependency.
          void initSharedLibraries(void);

          //! Init the symbols table via the program headers.
          void initSymbolsTableViaProgramHeaders(void);

          //! Init the symbols table via the section headers.
          void initSymbolsTableViaSectionHeaders(void);

          //! Init the relocations table (DT_REL).
          void initRelTable(void);

          //! Init the relocations table (DT_RELA).
          void initRelaTable(void);

          //! Init the relocations table (DT_JMPREL).
          void initJmprelTable(void);

          //! Returns the offset in the file corresponding to the virtual address.
          triton::uint64 getOffsetFromAddress(triton::uint64 vaddr) const;

          //! Returns the offset in the file corresponding to the Dynamic Table (DT) item.
          triton::uint64 getOffsetFromDTValue(triton::format::elf::elf_e dt) const;

          //! Returns the value of a Dynamic Table (DT) item.
          triton::uint64 getDTValue(triton::format::elf::elf_e dt) const;

        public:
          //! Constructor.
          Elf(const std::string& path);

          //! Destructor.
          virtual ~Elf();

          //! Returns the raw binary.
          const triton::uint8* getRaw(void) const;

          //! Returns the binary size.
          triton::usize getSize(void) const;

          //! Returns the path file of the binary.
          const std::string& getPath(void) const;

          //! Returns the ELF Header.
          const triton::format::elf::ElfHeader& getHeader(void) const;

          //! Returns Program Headers.
          const std::vector<triton::format::elf::ElfProgramHeader>& getProgramHeaders(void) const;

          //! Returns Section Headers.
          const std::vector<triton::format::elf::ElfSectionHeader>& getSectionHeaders(void) const;

          //! Returns Dynamic Table.
          const std::vector<triton::format::elf::ElfDynamicTable>& getDynamicTable(void) const;

          //! Returns Symbols Table.
          const std::vector<triton::format::elf::ElfSymbolTable>& getSymbolsTable(void) const;

          //! Returns Relocations Table.
          const std::vector<triton::format::elf::ElfRelocationTable>& getRelocationTable(void) const;

          //! Returns the list of shared libraries dependency.
          const std::vector<std::string>& getSharedLibraries(void) const;

          //! Returns all memory areas which then may be mapped via triton::API::setConcreteMemoryAreaValue.
          const std::list<triton::format::MemoryMapping>& getMemoryMapping(void) const;
      };

    /*! @} End of elf namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ELF_H */
