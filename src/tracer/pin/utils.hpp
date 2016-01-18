//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_UTILS_H
#define TRITON_UTILS_H

#include <string>
#include <pin.H>
#include <tritonTypes.hpp>



//! \module The Tracer namespace
namespace tracer {
/*!
 *  \addtogroup tracer
 *  @{
 */

  //! \module The pintool namespace
  namespace pintool {
  /*!
   *  \ingroup tracer
   *  \addtogroup pintool
   *  @{
   */

    //! Returns the base address from a given address.
    triton::__uint getBaseAddress(triton::__uint address);

    //! Returns the instruction offset from a given address.
    triton::__uint getInsOffset(triton::__uint address);

    //! Returns the image name from a given address.
    std::string getImageName(triton::__uint address);

    //! Setups the context register from Pin to Triton.
    void setupContextRegister(triton::arch::Instruction* inst, CONTEXT* ctx);


  /*! @} End of pintool namespace */
  };
/*! @} End of tracer namespace */
};

#endif /* TRITON_UTILS_H */
