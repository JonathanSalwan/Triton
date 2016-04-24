//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_EXTERNALLIBS_HPP
#define TRITON_EXTERNALLIBS_HPP



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */
  //! \module The external libraries namespace
  namespace extlibs {
  /*!
   *  \addtogroup triton
   *  @{
   */

    //! \module The Capstone library namespace
    namespace capstone {
    /*!
     *  \addtogroup extlibs
     *  @{
     */
      #if defined(__unix__) || defined(__APPLE__)
        #include <capstone/capstone.h>
        #include <capstone/x86.h>
      #elif _WIN32
        #include <capstone.h>
      #endif
    /*! @} End of capstone namespace */
    };

  /*! @} End of extlibs namespace */
  };
/*! @} End of triton namespace */
};

#endif  /* TRITON_EXTERNALLIBS_HPP */
