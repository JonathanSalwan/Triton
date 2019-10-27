//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_REGISTEROPERAND_HPP
#define TRITON_REGISTEROPERAND_HPP

#include <string>
#include <ostream>

#include <triton/aarch64OperandProperties.hpp>
#include <triton/archEnums.hpp>
#include <triton/bitsVector.hpp>
#include <triton/cpuSize.hpp>
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

    //! Used for a Register constructor.
    class CpuInterface;

    /*! \class Register
     *  \brief This class is used when an instruction has a register operand.
     */
    class Register : public BitsVector, public AArch64OperandProperties {
      protected:
        //! The name of the register.
        std::string name;

        //! The id of the register.
        triton::arch::register_e id;

        //! The parent id of the register.
        triton::arch::register_e parent;

        //! True if the register is mutable. For example XZR in AArch64 is immutable.
        bool vmutable;

      private:
        //! Copy a Register.
        void copy(const Register& other);

      public:
        //! Constructor.
        TRITON_EXPORT Register();

        //! Constructor.
        TRITON_EXPORT Register(triton::arch::register_e regId, std::string name, triton::arch::register_e parent, triton::uint32 high, triton::uint32 low, bool vmutable);

        //! Constructor.
        TRITON_EXPORT Register(const triton::arch::CpuInterface&, triton::arch::register_e regId);

        //! Constructor.
        TRITON_EXPORT Register(const Register& other);

        //! Returns the parent id of the register.
        TRITON_EXPORT triton::arch::register_e getParent(void) const;

        //! Returns true if `other` and `self` overlap.
        TRITON_EXPORT bool isOverlapWith(const Register& other) const;

        //! Returns true if this register is mutable. Mainly used in AArch64 to define that some registers like XZR are immutable.
        TRITON_EXPORT bool isMutable(void) const;

        //! Returns the name of the register.
        TRITON_EXPORT std::string getName(void) const;

        //! Returns the id of the register.
        TRITON_EXPORT triton::arch::register_e getId(void) const;

        //! Returns the size (in bits) of the register.
        TRITON_EXPORT triton::uint32 getBitSize(void) const;

        //! Returns the size (in bytes) of the register.
        TRITON_EXPORT triton::uint32 getSize(void) const;

        //! Returns the type of the operand (triton::arch::OPERAND_REGISTER).
        TRITON_EXPORT triton::arch::operand_e getType(void) const;

        //! Compare two registers specifications
        TRITON_EXPORT bool operator==(const Register& other) const;

        //! Compare two registers specifications
        TRITON_EXPORT bool operator!=(const Register& other) const;

        //! Copies a Register.
        TRITON_EXPORT Register& operator=(const Register& other);
    };

    //! Displays a Register.
    TRITON_EXPORT std::ostream& operator<<(std::ostream& stream, const Register& reg);

    //! Displays a Register.
    TRITON_EXPORT std::ostream& operator<<(std::ostream& stream, const Register* reg);

    //! Compares two Register
    TRITON_EXPORT bool operator<(const Register& reg1, const Register& reg2);

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_REGISTEROPERAND_HPP */
