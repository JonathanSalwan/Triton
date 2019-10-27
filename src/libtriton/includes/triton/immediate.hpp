//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_IMMEDIATE_HPP
#define TRITON_IMMEDIATE_HPP

#include <triton/aarch64OperandProperties.hpp>
#include <triton/archEnums.hpp>
#include <triton/bitsVector.hpp>
#include <triton/triton_export.h>
#include <triton/tritonTypes.hpp>



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

    /*! \class Immediate
     *  \brief This class is used to represent an immediate.
     */
    class Immediate : public BitsVector, public AArch64OperandProperties {
      protected:
        //! The value of the operand.
        triton::uint64 value;

      private:
        //! Copy an Immediate.
        void copy(const Immediate& other);

      public:
        //! Constructor.
        TRITON_EXPORT Immediate();

        //! Constructor.
        TRITON_EXPORT Immediate(triton::uint64 value, triton::uint32 size /* bytes*/);

        //! Constructor by copy.
        TRITON_EXPORT Immediate(const Immediate& other);

        //! Returns the value of the operand.
        TRITON_EXPORT triton::uint64 getValue(void) const;

        //! Returns the size (in bits) of the immediate vector.
        TRITON_EXPORT triton::uint32 getBitSize(void) const;

        //! Returns the size (in bytes) of the immediate vector.
        TRITON_EXPORT triton::uint32 getSize(void) const;

        //! Returns the type of the operand (triton::arch::OPERAND_IMMEDIATE).
        TRITON_EXPORT triton::arch::operand_e getType(void) const;

        //! Sets the value of the operand.
        TRITON_EXPORT void setValue(triton::uint64 v, triton::uint32 size /* bytes*/);

        //! Copy an Immediate.
        TRITON_EXPORT Immediate& operator=(const Immediate& other);
    };

    //! Displays an Immediate.
    TRITON_EXPORT std::ostream& operator<<(std::ostream& stream, const Immediate& imm);

    //! Displays an Immediate.
    TRITON_EXPORT std::ostream& operator<<(std::ostream& stream, const Immediate* imm);

    //! Compares two Immediate.
    TRITON_EXPORT bool operator==(const Immediate& imm1, const Immediate& imm2);

    //! Compares two Immediate.
    TRITON_EXPORT bool operator!=(const Immediate& imm1, const Immediate& imm2);

    //! Compares two Immediate (needed for std::map)
    TRITON_EXPORT bool operator<(const Immediate& imm1, const Immediate& imm2);

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_IMMEDIATE_HPP */
