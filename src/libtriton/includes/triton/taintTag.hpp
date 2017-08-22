//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_TAINTTAG_H
#define TRITON_TAINTTAG_H

#include <set>

#include <triton/memoryAccess.hpp>
#include <triton/register.hpp>
#include <triton/symbolicEngine.hpp>
#include <triton/tritonTypes.hpp>



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

      //! A wrapper class that encapsulates a generic pointer to enable any data to be "tagged" along with the taints.
      class TaintTag {
        private:
          void* data;

        public:
          TaintTag();

          //! Construct a TaintTag object by copying from an existing one.
          TaintTag(TaintTag const& tag);

          //! Initialize a TaintTag with a generic pointer data
          TaintTag(void* data);

          ~TaintTag();

          //! Retrieve the data; it is the user's responsibility to cast it back to its original data type
          void* getData();
      };

    /*! @} End of taint namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* !__TRITON_TAINTENGINE_H__ */

