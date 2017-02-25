//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ABSTRACTBINARY_H
#define TRITON_ABSTRACTBINARY_H

#include <iostream>

#include <triton/binaryInterface.hpp>
#include <triton/elf.hpp>
#include <triton/pe.hpp>
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

    /*! The different kind of binary format */
    enum binary_e {
      BINARY_INVALID = 0, /*!< invalid binary. */
      BINARY_ELF,         /*!< ELF binary. */
      BINARY_MACHO,       /*!< MACH-O binary. */
      BINARY_PE,          /*!< PE binary. */
      BINARY_LAST_ITEM    /*!< must be the last item.  */
    };

    /*! The magic number of binary format */
    enum magic_e {
      MAGIC_ELF      = 0x464c457f, /*!< magic ELF. */
      MAGIC_MACHO32  = 0xfeedface, /*!< magic MACH-O (32-bits). */
      MAGIC_MACHO64  = 0xfeedfacf, /*!< magic MACH-O (64-bits). */
      MAGIC_PE       = 0x5a4d,     /*!< magic PE. */
    };

    /*! \class AbstractBinary
     *  \brief The abstract binary class. */
    class AbstractBinary {
      protected:
        //! The binary format.
        triton::format::binary_e format;

        //! Instance to the real Binary class.
        triton::format::BinaryInterface* binary;

        //! Parse the binary
        void parseBinary(const std::string& path);

      public:
        //! Constructor.
        AbstractBinary();

        //! Constructor.
        AbstractBinary(const std::string& path);

        //! Destructor.
        virtual ~AbstractBinary();

        //! Returns the binary format.
        triton::format::binary_e getFormat(void) const;

        //! Load a binary.
        void loadBinary(const std::string& path);

        //! Returns the abstract binary.
        triton::format::BinaryInterface* getBinary(void);

        //! Returns the ELF instance only if the AbstractBinary::format is equal to triton::format::BINARY_ELF otherwise raise an excepton.
        triton::format::elf::Elf* getElf(void);

        //! Returns the PE instance only if the AbstractBinary::format is equal to triton::format::BINARY_PE otherwise raise an excepton.
        triton::format::pe::Pe* getPe(void);

        //! Returns the path file of the loaded binary.
        const std::string& getPath(void) const;

        //! Returns all memory areas which may be mapped.
        const std::list<triton::format::MemoryMapping>& getMemoryMapping(void) const;
    };

  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ABSTRACTBINARY_H */
