#ifndef TRITON_REGISTERS_E_H
#define TRITON_REGISTERS_E_H

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
      //! The list of registers.
      enum registers_e {
        ID_REG_INVALID = 0, //!< invalid = 0

#define REG_SPEC(UPPER_NAME, LOWER_NAME, X86_64_UPPER, X86_64_LOWER, X86_64_PARENT, X86_UPPER, X86_LOWER, X86_PARENT, X86_AVAIL)\
        ID_REG_##UPPER_NAME,
#define REG_SPEC_NO_CAPSTONE REG_SPEC
#include "triton/x86.spec"

        /* Must be the last item */
        ID_REG_LAST_ITEM //!< must be the last item
      };
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

namespace std
{
  template <>
  class hash<triton::arch::registers_e>: public hash<uint64_t>
  {};
}

#endif
