//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_PE_H
#define TRITON_PE_H

#include <iostream>
#include <vector>

#include "binaryInterface.hpp"
#include "peHeader.hpp"
#include "memoryMapping.hpp"
#include "tritonTypes.hpp"



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

    //! The PE format namespace
    namespace pe {
    /*!
     *  \ingroup format
     *  \addtogroup pe
     *  @{
     */

      /*! \class PEImportLookup
       *  \brief PE Import Lookup Table entry */
      struct PEImportLookup {
          bool importByName;
          triton::uint16 ordinalNumber; //contains "hint" if importByName
          std::string name; //only if importByName
      };

      /*! \class PEImportDirectory
       *  \brief PE Import Directory Table entry */
      struct PEImportDirectory {
          triton::uint32 importLookupTableRVA;
          triton::uint32 timeDateStamp;
          triton::uint32 forwarderChain;
          triton::uint32 nameRVA;
          triton::uint32 importAddressTableRVA;
          std::string name;
          std::vector<PEImportLookup> entries;
      };

      /*! \class PEExportEntry
       *  \brief PE Export entry */

      struct PEExportEntry {
          bool isForward;
          triton::uint32 exportRVA;     //if not isForward
          triton::uint32 forwarderRVA;  //if isForward
          std::string forwarderName;    //if isForward
          triton::uint32 exportNameRVA;
          std::string exportName;
          triton::uint16 ordinal;
      };

      /*! \class PEExportDirectory
       *  \brief PE Export Directory */
      struct PEExportDirectory {
          triton::uint32 exportFlags;
          triton::uint32 timeDateStamp;
          triton::uint16 majorVersion;
          triton::uint16 minorVersion;
          triton::uint32 nameRVA;
          triton::uint32 ordinalBase;
          triton::uint32 addressTableEntries;
          triton::uint32 numberOfNamePointers;
          triton::uint32 exportAddressTableRVA;
          triton::uint32 namePointerRVA;
          triton::uint32 ordinalTableRVA;

          std::string name;
          std::vector<PEExportEntry> entries;
      };

      /*! \class PE
       *  \brief The PE format class. */
      class PE : public BinaryInterface {
        protected:
          //! Path file of the binary.
          std::string path;

          //! Total size of the binary file.
          triton::usize totalSize;

          //! The raw binary.
          triton::uint8* raw;

          //! The PE Header
          triton::format::pe::PEHeader header;

          /*!
           * \description The list of memory areas which may be mapped into the Triton memory.
           * In the PE context, this is basically all segments.
           */
          std::list<triton::format::MemoryMapping> memoryMapping;

          std::vector<PEImportDirectory> importTable;
          PEExportDirectory exportTable;

          //! Open the binary.
          void open(void);

          //! Parse the binary.
          bool parse(void);

          //! Init the memory mapping.
          void initMemoryMapping(void);

          //! Init the export table.
          void initExportTable(void);

          //! Init the import table.
          void initImportTable(void);

          //! Returns the offset in the file corresponding to the virtual address.
          triton::uint64 getOffsetFromAddress(triton::uint64 vaddr) const;

        public:
          //! Constructor.
          PE(const std::string& path);

          //! Destructor.
          virtual ~PE();

          //! Returns the raw binary.
          const triton::uint8* getRaw(void) const;

          //! Returns the binary size.
          triton::usize getSize(void) const;

          //! Returns the path file of the binary.
          const std::string& getPath(void) const;

          //! Returns the PE Header.
          const triton::format::pe::PEHeader& getHeader(void) const;

          //! Returns the export table.
          const PEExportDirectory& getExportTable(void) const;

          //! Returns the import table.
          const std::vector<PEImportDirectory>& getImportTable(void) const;

          //! Returns all memory areas which then may be mapped via triton::API::setConcreteMemoryAreaValue.
          const std::list<triton::format::MemoryMapping>& getMemoryMapping(void) const;

      };

    /*! @} End of pe namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_PE_H */
