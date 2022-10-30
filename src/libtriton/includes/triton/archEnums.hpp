//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
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

    /*! Types of architecture */
    enum architecture_e {
      ARCH_INVALID = 0, /*!< Invalid architecture.   */
      ARCH_AARCH64,     /*!< AArch64 architecture.   */
      ARCH_ARM32,       /*!< ARM32 architecture.     */
      ARCH_X86,         /*!< X86 architecture.       */
      ARCH_X86_64,      /*!< X86_64 architecture.    */
    };

    /*! Types of endianness */
    enum endianness_e {
      LE_ENDIANNESS,    /*!< Little endian.     */
      BE_ENDIANNESS,    /*!< Big endian.        */
    };

    /*! Types of operand */
    enum operand_e {
      OP_INVALID = 0,   /*!< Invalid operand    */
      OP_IMM,           /*!< Immediate operand  */
      OP_MEM,           /*!< Memory operand     */
      OP_REG            /*!< Register operand   */
    };

    /*! Types of exceptions */
    enum exception_e {
      NO_FAULT = 0,     /*!< Succeed, no fault.                       */
      FAULT_DE,         /*!< Fault raised: Divide-by-zero.            */
      FAULT_BP,         /*!< Fault raised: Breakpoint.                */
      FAULT_UD,         /*!< Fault raised: Instruction not supported. */
      FAULT_GP,         /*!< Fault raised: General Protection Fault.  */
    };

    //! Types of register.
    enum register_e {
      ID_REG_INVALID = 0, //!< invalid = 0

      #define REG_SPEC(UPPER_NAME, _1, _2, _3, _4, _5, _6, _7, _8) \
      ID_REG_X86_##UPPER_NAME,
      #define REG_SPEC_NO_CAPSTONE REG_SPEC
      #include "triton/x86.spec"

      #define REG_SPEC(UPPER_NAME, _1, _2, _3, _4, _5) \
      ID_REG_AARCH64_##UPPER_NAME,
      #define REG_SPEC_NO_CAPSTONE REG_SPEC
      #define SYS_REG_SPEC REG_SPEC
      #include "triton/aarch64.spec"

      #define REG_SPEC(UPPER_NAME, _1, _2, _3, _4, _5) \
      ID_REG_ARM32_##UPPER_NAME,
      #define REG_SPEC_NO_CAPSTONE REG_SPEC
      #include "triton/arm32.spec"

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

      /*! \brief Types of prefix.
       *
       *  \details
       *  Note that `REP` and `REPE` have the some opcode. The `REP`
       *  prefix becomes a `REPE` if the instruction modifies `ZF`.
       */
      enum prefix_e {
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

    //! The Arm namespace
    namespace arm {
    /*!
     *  \ingroup arch
     *  \addtogroup arm
     *  @{
     */

      //! Types of shift
      enum shift_e {
        ID_SHIFT_INVALID = 0, //!< invalid
        ID_SHIFT_ASR,         //!< Arithmetic Shift Right (immediate)
        ID_SHIFT_LSL,         //!< Logical Shift Left (immediate)
        ID_SHIFT_LSR,         //!< Logical Shift Right (immediate)
        ID_SHIFT_ROR,         //!< Rotate Right (immediate)
        ID_SHIFT_RRX,         //!< Rotate Right with Extend (immediate)
        ID_SHIFT_ASR_REG,     //!< Arithmetic Shift Right (register)
        ID_SHIFT_LSL_REG,     //!< Logical Shift Left (register)
        ID_SHIFT_LSR_REG,     //!< Logical Shift Right (register)
        ID_SHIFT_ROR_REG,     //!< Rotate Right (register)
        ID_SHIFT_RRX_REG,     //!< Rotate Right with Extend (register)
        ID_SHIFT_LAST_ITEM,   //!< Must be the last item
      };

      //! Types of extend
      enum extend_e {
        ID_EXTEND_INVALID = 0,   //!< invalid
        ID_EXTEND_UXTB,          //!< Extracts a byte (8-bit) value from a register and zero extends it to the size of the register
        ID_EXTEND_UXTH,          //!< Extracts a halfword (16-bit) value from a register and zero extends it to the size of the register
        ID_EXTEND_UXTW,          //!< Extracts a word (32-bit) value from a register and zero extends it to the size of the register
        ID_EXTEND_UXTX,          //!< Use the whole 64-bit register
        ID_EXTEND_SXTB,          //!< Extracts a byte (8-bit) value from a register and zero extends it to the size of the register
        ID_EXTEND_SXTH,          //!< Extracts a halfword (16-bit) value from a register and zero extends it to the size of the register
        ID_EXTEND_SXTW,          //!< Extracts a word (32-bit) value from a register and zero extends it to the size of the register
        ID_EXTEND_SXTX,          //!< Use the whole 64-bit register
        ID_EXTEND_LAST_ITEM,     //!< Must be the last item
      };

      //! Types of condition
      enum condition_e {
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

      //! Vector arrangement specifier
      enum vas_e {
        ID_VAS_INVALID = 0, //!< invalid
        ID_VAS_16B,         //!< 16 lanes, each containing an 8-bit element.
        ID_VAS_8B,          //!< 8 lanes, each containing an 8-bit element.
        ID_VAS_8H,          //!< 8 lanes, each containing a 16-bit element.
        ID_VAS_4H,          //!< 4 lanes, each containing a 16-bit element.
        ID_VAS_4S,          //!< 4 lanes, each containing a 32-bit element.
        ID_VAS_2S,          //!< 2 lanes, each containing a 32-bit element.
        ID_VAS_2D,          //!< 2 lanes, each containing a 64-bit element.
        ID_VAS_1D,          //!< 1 lane containing a 64-bit element.
        ID_VAS_LAST_ITEM,   //!< must be the last item.
      };

    /*! @} End of arm namespace */
    };
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

namespace std {
  //! Define the hash function for register_e to be use in stl containers like unordered_map
  template <> struct hash<triton::arch::register_e> : public hash<uint64_t> {
  };
};

#endif /* TRITON_ARCHENUMS_HPP */
