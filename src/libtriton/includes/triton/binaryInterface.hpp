//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_BINARYINTERFACE_H
#define TRITON_BINARYINTERFACE_H

#include <list>

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

    /*! \class BinaryInterface
     *  \brief The interface of a binary class. */
    class BinaryInterface {
      public:
        //! Destructor.
        virtual ~BinaryInterface(){};

        //! Returns the path file of the loaded binary.
        virtual const std::string& getPath(void) const = 0;

        //! Returns all memory areas which may be mapped.
        virtual const std::list<triton::format::MemoryMapping>& getMemoryMapping(void) const = 0;
    };

  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_BINARYINTERFACE_H */
