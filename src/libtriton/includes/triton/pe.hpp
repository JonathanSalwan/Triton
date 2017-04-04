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
#include <string>

#include <triton/binaryInterface.hpp>
#include <triton/memoryMapping.hpp>
#include <triton/peExportDirectory.hpp>
#include <triton/peHeader.hpp>
#include <triton/peImportDirectory.hpp>
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

    //! The PE format namespace
    namespace pe {
    /*!
     *  \ingroup format
     *  \addtogroup pe
     *  @{
     */

      /*! \class Pe
       *  \brief The PE format class. */
      class Pe : public BinaryInterface {
        protected:
          //! Path file of the binary.
          std::string path;

          //! Total size of the binary file.
          triton::usize totalSize;

          //! The raw binary.
          std::vector<triton::uint8> raw;

          //! The PE Header.
          triton::format::pe::PeHeader header;

          //! The list of memory areas which may be mapped into the Triton memory. In the PE context, this is basically all segments.
          std::list<triton::format::MemoryMapping> memoryMapping;

          //! The import table.
          std::vector<PeImportDirectory> importTable;

          //! DLL Dependencies.
          std::vector<std::string> dlls;

          //! Export table.
          PeExportDirectory exportTable;

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
          Pe(const std::string& path);

          //! Destructor.
          virtual ~Pe();

          //! Returns the raw binary.
          const triton::uint8* getRaw(void) const;

          //! Returns the binary size.
          triton::usize getSize(void) const;

          //! Returns the path file of the binary.
          const std::string& getPath(void) const;

          //! Returns the PE Header.
          const triton::format::pe::PeHeader& getHeader(void) const;

          //! Returns the export table.
          const PeExportDirectory& getExportTable(void) const;

          //! Returns the import table.
          const std::vector<PeImportDirectory>& getImportTable(void) const;

          //! Returns the names of the imported DLLS.
          const std::vector<std::string>& getSharedLibraries(void) const;

          //! Returns all memory areas which then may be mapped via triton::API::setConcreteMemoryAreaValue.
          const std::list<triton::format::MemoryMapping>& getMemoryMapping(void) const;

          //! Returns the image base (shorthand of getting it via getHeader)
          triton::uint64 getImageBase(void) const;
      };

    /*! @} End of pe namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_PE_H */
