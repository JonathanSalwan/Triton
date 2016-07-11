//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ELF_H
#define TRITON_ELF_H

#include <iostream>
#include <list>
#include <map>
#include <vector>

#include "binaryInterface.hpp"
#include "elfDynamicTable.hpp"
#include "elfEnums.hpp"
#include "elfHeader.hpp"
#include "elfProgramHeader.hpp"
#include "elfSectionHeader.hpp"
#include "elfSymbolTable.hpp"
#include "memoryMapping.hpp"
#include "tritonTypes.hpp"



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

      /*! \class ELF
       *  \brief The ELF format class. */
      class ELF : public BinaryInterface {
        protected:
          //! Path file of the binary.
          std::string path;

          //! Total size of the binary file.
          triton::usize totalSize;

          //! The raw binary.
          triton::uint8* raw;

          //! The ELF Header
          triton::format::elf::ELFHeader header;

          //! The Program Headers
          std::vector<triton::format::elf::ELFProgramHeader> programHeaders;

          //! The Section Headers
          std::vector<triton::format::elf::ELFSectionHeader> sectionHeaders;

          //! The dynamic table.
          std::list<triton::format::elf::ELFDynamicTable> dynamicTable;

          //! The symbols table as map of `<symbolName:symbolClass>`.
          std::map<std::string, triton::format::elf::ELFSymbolTable> symbolsTable;

          //! The shared libraries dependency.
          std::list<std::string> sharedLibraries;

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

          //! Init the symbols table via the section headers.
          void initSymbolsTableViaSectionHeaders(void);

          //! Init the symbols table via the program headers.
          void initSymbolsTableViaProgramHeaders(void);

          //! Returns the offset in the file corresponding to the virtual address.
          triton::uint64 getOffsetFromAddress(triton::uint64 vaddr);

          //! Returns the offset in the file corresponding to the Dynamic Table (DT) item.
          triton::uint64 getOffsetFromDTValue(triton::format::elf::elf_e dt);

          //! Returns the value of a Dynamic Table (DT) item.
          triton::uint64 getDTValue(triton::format::elf::elf_e dt);

        public:
          //! Constructor.
          ELF(const std::string& path);

          //! Destructor.
          ~ELF();

          //! Returns the path file of the binary.
          const std::string& getPath(void) const;

          //! Returns ELF Headers.
          const triton::format::elf::ELFHeader& getHeader(void) const;

          //! Returns Program Headers.
          const std::vector<triton::format::elf::ELFProgramHeader>& getProgramHeaders(void) const;

          //! Returns Section Headers.
          const std::vector<triton::format::elf::ELFSectionHeader>& getSectionHeaders(void) const;

          //! Returns Dynamic Table.
          const std::list<triton::format::elf::ELFDynamicTable>& getDynamicTable(void) const;

          //! Returns Symbols Table as map of `<symbolName:symbolClass>`.
          const std::map<std::string, triton::format::elf::ELFSymbolTable>& getSymbolsTable(void) const;

          //! Returns the list of shared libraries dependency.
          const std::list<std::string>& getSharedLibraries(void) const;

          //! Returns all memory areas which may be mapped.
          const std::list<triton::format::MemoryMapping>& getMemoryMapping(void) const;
      };

    /*! @} End of elf namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ELF_H */
