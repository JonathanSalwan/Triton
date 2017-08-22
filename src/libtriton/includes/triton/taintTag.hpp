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

      class TaintTag {
        private:
          void* data;

        public:
          TaintTag();

          TaintTag(TaintTag const& tag);

          TaintTag(void* data);

          ~TaintTag();

          void* getData();

          //std::string toString() const;

          //long hash() const;

          //friend std::ostream& operator<<(std::ostream& ostrm, TaintTag const& tag);
      };

    /*! @} End of taint namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* !__TRITON_TAINTENGINE_H__ */

