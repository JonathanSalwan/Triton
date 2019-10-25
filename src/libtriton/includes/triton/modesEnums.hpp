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
      ALIGNED_MEMORY,                 //!< [symbolic] Keep a map of aligned memory.
      AST_OPTIMIZATIONS,              //!< [AST] Classical arithmetic optimisations to reduce the depth of the trees.
      CONCRETIZE_UNDEFINED_REGISTERS, //!< [symbolic] Concretize every registers tagged as undefined (see #750).
      ITERATIVE_GC,                   //!< [core] Iterative garbage collector. This option may avoid stack overflow during the release of shared_ptr but impact (a little bit) the performance.
      ONLY_ON_SYMBOLIZED,             //!< [symbolic] Perform symbolic execution only on symbolized expressions.
      ONLY_ON_TAINTED,                //!< [symbolic] Perform symbolic execution only on tainted instructions.
      PC_TRACKING_SYMBOLIC,           //!< [symbolic] Track path constraints only if they are symbolized.
      SYMBOLIZE_INDEX_ROTATION,       //!< [symbolic] Symbolize index rotation for bvrol and bvror (see #751). This mode increases the complexity of solving.
      TAINT_THROUGH_POINTERS,         //!< [taint] Spread the taint if an index pointer is already tainted (see #725).
    };

  /*! @} End of modes namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_MODES_HPP */
