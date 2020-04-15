//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_MODES_H
#define TRITON_MODES_H

#include <memory>
#include <unordered_set>

#include <triton/dllexport.hpp>
#include <triton/modesEnums.hpp>



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

    //! \class Modes
    /*! \brief The modes class */
    class Modes {
      private:
        //! Copies a Modes.
        void copy(const Modes& other);

      protected:
        //! The set of enabled modes
        std::unordered_set<triton::modes::mode_e> enabledModes;

      public:
        //! Constructor.
        TRITON_EXPORT Modes();

        //! Constructor.
        TRITON_EXPORT Modes(const Modes& other);

        //! Copies a Modes.
        TRITON_EXPORT Modes& operator=(const Modes& other);

        //! Returns true if the mode is enabled.
        TRITON_EXPORT bool isModeEnabled(triton::modes::mode_e mode) const;

        //! Enables or disables a specific mode.
        TRITON_EXPORT void setMode(triton::modes::mode_e mode, bool flag);

        //! Clears recorded modes.
        TRITON_EXPORT void clearModes(void);
    };

    //! Shared Modes.
    using SharedModes = std::shared_ptr<triton::modes::Modes>;

  /*! @} End of modes namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_MODES_H */
