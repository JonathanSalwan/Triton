//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_MEMORYMAPPING_H
#define TRITON_MEMORYMAPPING_H

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

    /*! \class MemoryMapping
     *  \brief The memory mapping class. */
    class MemoryMapping {
      protected:
        //! The binary file.
        const triton::uint8* binary;

        //! The offset of the area into the binary file.
        triton::uint64 offset;

        //! The virtual address where the area must be mapped into the memory.
        triton::uint64 virtualAddress;

        //! The size of the area.
        triton::uint64 size;

      public:
        //! Constructor.
        MemoryMapping(const triton::uint8* binary);

        //! Constructor by copy.
        MemoryMapping(const MemoryMapping& copy);

        //! Destructor.
        virtual ~MemoryMapping();

        //! Copies a MemoryMapping class.
        void operator=(const MemoryMapping& copy);

        //! Returns the binary.
        const triton::uint8* getBinary(void) const;

        //! Returns the offset.
        triton::uint64 getOffset(void) const;

        //! Returns the virtual address.
        triton::uint64 getVirtualAddress(void) const;

        //! Returns the memory area into the binary file.
        const triton::uint8* getMemoryArea(void) const;

        //! Returns the size.
        triton::uint64 getSize(void) const;

        //! Sets the offset.
        void setOffset(triton::uint64 offset);

        //! Sets the virtual address.
        void setVirtualAddress(triton::uint64 virtualAddress);

        //! Sets the size.
        void setSize(triton::uint64 size);
    };

  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_MEMORYMAPPING_H */
