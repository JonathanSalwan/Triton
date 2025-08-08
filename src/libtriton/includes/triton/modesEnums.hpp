//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_MODES_HPP
#define TRITON_MODES_HPP

#include <cstdint>


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
      CONSTANT_FOLDING,               //!< [symbolic] Perform a constant folding optimization of sub ASTs which do not contain symbolic variables.
      MEMORY_ARRAY,                   //!< [symbolic] Enable memory symbolic array
      ONLY_ON_SYMBOLIZED,             //!< [symbolic] Perform symbolic execution only on symbolized expressions.
      ONLY_ON_TAINTED,                //!< [symbolic] Perform symbolic execution only on tainted instructions.
      PC_TRACKING_SYMBOLIC,           //!< [symbolic] Track path constraints only if they are symbolized.
      SYMBOLIZE_INDEX_ROTATION,       //!< [symbolic] Symbolize index rotation for bvrol and bvror (see #751). This mode increases the complexity of solving.
      SYMBOLIZE_LOAD,                 //!< [symbolic] Symbolize memory load if memory array is enabled
      SYMBOLIZE_STORE,                //!< [symbolic] Symbolize memory store if memory array is enabled
      TAINT_THROUGH_POINTERS,         //!< [taint] Spread the taint if an index pointer is already tainted (see #725).
    };

  /*! @} End of modes namespace */
  };
/*! @} End of triton namespace */
};

namespace std {
  //! Define the hash function for mode_e to be use in stl containers like unordered_set
  template <> struct hash<triton::modes::mode_e> : public hash<uint64_t> {
  };
};

#endif /* TRITON_MODES_HPP */
