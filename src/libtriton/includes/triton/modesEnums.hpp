//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_MODES_HPP
#define TRITON_MODES_HPP



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Modes namespace
  namespace modes {
  /*!
   *  \ingroup triton
   *  \addtogroup modes
   *  @{
   */

    //! Enumerates all kinds of mode.
    enum mode_e {
      ALIGNED_MEMORY,                 //!< [symbolic mode] Keep a map of aligned memory.
      CONCRETIZE_UNDEFINED_REGISTERS, //!< [symbolic mode] Concretize every registers tagged as undefined (see #750).
      ONLY_ON_SYMBOLIZED,             //!< [symbolic mode] Perform symbolic execution only on symbolized expressions.
      ONLY_ON_TAINTED,                //!< [symbolic mode] Perform symbolic execution only on tainted instructions.
      PC_TRACKING_SYMBOLIC,           //!< [symbolic mode] Track path constraints only if they are symbolized.
      SYMBOLIZE_INDEX_ROTATION,       //!< [symbolic mode] Symbolize index rotation for bvrol and bvror (see #751). This mode increases the complexity of solving.
      TAINT_THROUGH_POINTERS,         //!< [taint mode] Spread the taint if an index pointer is already tainted (see #725).
    };

  /*! @} End of modes namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_MODES_HPP */
