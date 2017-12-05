//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ARMV7SPECIFICATIONS_H
#define TRITON_ARMV7SPECIFICATIONS_H

#include <triton/register.hpp>
#include <triton/registers_e.hpp>
#include <triton/architecture.hpp>

#include <unordered_map>

//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Architecture namespace
  namespace arch {
  /*!
   *  \ingroup triton
   *  \addtogroup arch
   *  @{
   */
    namespace armv7 {
      //! \class armv7mSpecifications
      /*! \brief The armv7mSpecifications class defines specifications about the armv7m CPU */
      class armv7Specifications {

      public:
          //! Constructor
          armv7Specifications(triton::arch::architectures_e);

          //! Converts a capstone register id to a triton register id

      protected:
        //! List of registers specification available for this architecture.
        std::unordered_map<registers_e, const triton::arch::Register> registers_;
      };
    }
  }
}
#endif /* TRITON_ARMV7SPECIFICATIONS_H */
