//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ARCHENUMS_HPP
#define TRITON_ARCHENUMS_HPP

#include <cstdint>
#include <functional>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Triton namespace
  namespace arch {
  /*!
   *  \ingroup triton
   *  \addtogroup arch
   *  @{
   */

    /*! The architectures */
    enum architectures_e {
      ARCH_INVALID = 0, /*!< Invalid architecture.   */
      ARCH_AARCH64,     /*!< AArch64 architecture.   */
      ARCH_X86,         /*!< X86 architecture.       */
      ARCH_X86_64,      /*!< X86_64 architecture.    */
      ARCH_LAST_ITEM    /*!< Must be the last item.  */
    };

    /*! Endianness */
    enum endianness_e {
      INVALID_ENDIANNESS = 0,   /*!< Invalid endianness */
      LE,                       /*!< Little endian.     */
      BE,                       /*!< Big endian.        */
    };

    /*! Type of operand */
    enum operandType_e {
      OP_INVALID = 0, //!< invalid operand
      OP_IMM,         //!< immediate operand
      OP_MEM,         //!< memory operand
      OP_REG          //!< register operand
    };

    //! The list of registers.
    enum registers_e {
      ID_REG_INVALID = 0, //!< invalid = 0

      #define REG_SPEC(UPPER_NAME, LOWER_NAME, X86_64_UPPER, X86_64_LOWER, X86_64_PARENT, X86_UPPER, X86_LOWER, X86_PARENT, X86_AVAIL) \
      ID_REG_X86_##UPPER_NAME,
      #define REG_SPEC_NO_CAPSTONE REG_SPEC
      #include "triton/x86.spec"

      #define REG_SPEC(UPPER_NAME, LOWER_NAME, AARCH64_UPPER, AARCH64_LOWER, AARCH64_PARENT) \
      ID_REG_AARCH64_##UPPER_NAME,
      #define REG_SPEC_NO_CAPSTONE REG_SPEC
      #include "triton/aarch64.spec"

      /* Must be the last item */
      ID_REG_LAST_ITEM //!< must be the last item
    };

    //! The x86 namespace
    namespace x86 {
    /*!
     *  \ingroup arch
     *  \addtogroup x86
     *  @{
     */

      /*! \brief The list of prefixes.
       *
       *  \details
       *  Note that `REP` and `REPE` have the some opcode. The `REP`
       *  prefix becomes a `REPE` if the instruction modifies `ZF`.
       */
      enum prefixes_e {
        ID_PREFIX_INVALID = 0,  //!< invalid
        ID_PREFIX_LOCK,         //!< LOCK
        ID_PREFIX_REP,          //!< REP
        ID_PREFIX_REPE,         //!< REPE
        ID_PREFIX_REPNE,        //!< REPNE

        /* Must be the last item */
        ID_PREFIX_LAST_ITEM     //!< must be the last item
      };

    /*! @} End of x86 namespace */
    };

    //! The AArch64 namespace
    namespace aarch64 {
    /*!
     *  \ingroup arch
     *  \addtogroup aarch64
     *  @{
     */

      //! The list of shift
      enum shifts_e {
        ID_SHIFT_INVALID = 0, //!< invalid
        ID_SHIFT_ASR,         //!< Arithmetic Shift Right
        ID_SHIFT_LSL,         //!< Logical Shift Left
        ID_SHIFT_LSR,         //!< Logical Shift Right
        ID_SHIFT_ROR,         //!< Rotate Right
        ID_SHIFT_LAST_ITEM,   //!< Must be the last item
      };

      //! The list of condition
      enum conditions_e {
        ID_CONDITION_INVALID = 0, //!< invalid
        ID_CONDITION_AL,          //!< Always. Any flags. This suffix is normally omitted.
        ID_CONDITION_EQ,          //!< Equal. Z set.
        ID_CONDITION_GE,          //!< Signed >=. N and V the same.
        ID_CONDITION_GT,          //!< Signed >. Z clear, N and V the same.
        ID_CONDITION_HI,          //!< Higher (unsigned >). C set and Z clear.
        ID_CONDITION_HS,          //!< Higher or same (unsigned >=). C set.
        ID_CONDITION_LE,          //!< Signed <=. Z set, N and V differ.
        ID_CONDITION_LO,          //!< Lower (unsigned <). C clear.
        ID_CONDITION_LS,          //!< Lower or same (unsigned <=). C clear or Z set.
        ID_CONDITION_LT,          //!< Signed <. N and V differ.
        ID_CONDITION_MI,          //!< Negative. N set.
        ID_CONDITION_NE,          //!< Not equal. Z clear.
        ID_CONDITION_PL,          //!< Positive or zero. N clear.
        ID_CONDITION_VC,          //!< No overflow. V clear.
        ID_CONDITION_VS,          //!< Overflow. V set.
        ID_CONDITION_LAST_ITEM,   //!< must be the last item.
      };

    /*! @} End of aarch64 namespace */
    };
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

namespace std {
  // Define the hash function for registers_e to be use in stl containers like unordered_map
  template <>
  struct hash<triton::arch::registers_e> : public hash<uint64_t> {
  };
};

#endif /* TRITON_ARCHENUMS_HPP */
