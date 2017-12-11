//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_MODES_H
#define TRITON_MODES_H

#include <set>
#include <triton/dllexport.hpp>



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
      /* AST */
      AST_DICTIONARIES,      //!< [ast mode] Abstract Syntax Tree dictionaries.

      /* Symbolic */
      ALIGNED_MEMORY,        //!< [symbolic mode] Keep a map of aligned memory.
      ONLY_ON_SYMBOLIZED,    //!< [symbolic mode] Perform symbolic execution only on symbolized expressions.
      ONLY_ON_TAINTED,       //!< [symbolic mode] Perform symbolic execution only on tainted instructions.
      PC_TRACKING_SYMBOLIC,  //!< [symbolic mode] Track path constraints only if they are symbolized.
    };


    //! \class Modes
    /*! \brief The modes class */
    class Modes {
      private:
        //! Copies a Modes.
        void copy(const Modes& other);

      protected:
        //! The set of enabled modes
        std::set<enum mode_e> enabledModes;

      public:
        //! Constructor.
        TRITON_EXPORT Modes();

        //! Constructor.
        TRITON_EXPORT Modes(const Modes& other);

        //! Returns true if the mode is enabled.
        TRITON_EXPORT bool isModeEnabled(enum mode_e mode) const;

        //! Enables or disables a specific mode.
        TRITON_EXPORT void enableMode(enum mode_e mode, bool flag);

        //! Copies a Modes.
        TRITON_EXPORT Modes& operator=(const Modes& other);
    };

  /*! @} End of modes namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_MODES_H */
