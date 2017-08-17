//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_COVTAG_H
#define TRITON_COVTAG_H

#include <set>

#include <triton/memoryAccess.hpp>
#include <triton/register.hpp>
#include <triton/symbolicEngine.hpp>
#include <triton/tritonTypes.hpp>
#include <triton/taintEngine.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Engines namespace
  namespace engines {
  /*!
   *  \ingroup triton
   *  \addtogroup engines
   *  @{
   */

    //! The Taint namespace
    namespace taint {
    /*!
     *  \ingroup engines
     *  \addtogroup taint
     *  @{
     */

      class CovTag : public triton::engines::taint::TagType {
        private:

          /*! Instruction address wherein the tag was generated */
          triton::uint64 addr;

          /*! The truth value of the condition evaluated at the point where the
           * tag was generated */
          bool truth;

        public:

          CovTag();

          CovTag(CovTag const& tag);

          CovTag(triton::uint64 addr, bool truth);

          ~CovTag();

          std::string toString() const;

          /*! Returns the instruction address wherein this tag was generated */
          triton::uint64 getAddress() const;

          /*! Returns the truth value which was evaluated at the point where
           * this tag was generated */
          bool getTruthValue() const;
      };


    /*! @} End of taint namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* !__TRITON_TAINTENGINE_H__ */

