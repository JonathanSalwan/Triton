//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_ELF_H
#define TRITON_ELF_H

#include <iostream>
#include <vector>

#include "binaryInterface.hpp"
#include "elfEnums.hpp"
#include "elfHeader.hpp"
#include "elfProgramHeader.hpp"
#include "elfSectionHeader.hpp"
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
          triton::format::elf::ELFHeader elfHeader;

          //! The Program Headers
          std::vector<triton::format::elf::ELFProgramHeader> elfProgramHeaders;

          //! The Section Headers
          std::vector<triton::format::elf::ELFSectionHeader> elfSectionHeaders;

          /*!
           * \description The list of memory areas which may be mapped into the Triton memory.
           * In the ELF context, this is basically all segments.
           */
          std::list<triton::format::MemoryMapping> memoryMapping;

          //! Open the binary.
          void open(void);

          //! Parse the binary.
          void parse(void);

          //! Init the memory mapping.
          void initMemoryMapping(void);

        public:
          //! Constructor.
          ELF(const std::string& path);

          //! Destructor.
          ~ELF();

          //! Returns the path file of the binary.
          const std::string& getPath(void) const;

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
