//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_REGISTEROPERAND_H
#define TRITON_REGISTEROPERAND_H

#include <string>
#include <ostream>

#include <triton/bitsVector.hpp>
#include <triton/cpuSize.hpp>
#include <triton/operandInterface.hpp>
#include <triton/tritonTypes.hpp>
#include <triton/registers_e.hpp>



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

    class CpuInterface;

    /*! \class RegisterSpec
     *  \brief This class is used when an instruction has a register operand.
     */
    class RegisterSpec : public BitsVector, public OperandInterface {

      protected:
        //! The name of the register.
        std::string name;

        //! The id of the register.
        triton::arch::registers_e id;

        //! The parent id of the register.
        triton::arch::registers_e parent;

      public:
        //! Constructor.
        RegisterSpec(triton::arch::registers_e regId, std::string name, triton::arch::registers_e parent, triton::uint32 high, triton::uint32 low);

        //! Constructor.
        RegisterSpec(const RegisterSpec& other);

        //! Returns the parent id of the register.
        registers_e getParent(void) const;

        //! Returns true if `other` and `self` overlap.
        bool isOverlapWith(const RegisterSpec& other) const;

        //! Returns the name of the register.
        std::string getName(void) const;

        //! Returns the highest bit of the register vector. \sa BitsVector::getHigh()
        triton::uint32 getAbstractHigh(void) const;

        //! Returns the lower bit of the register vector. \sa BitsVector::getLow()
        triton::uint32 getAbstractLow(void) const;

        //! Returns the size (in bits) of the register.
        triton::uint32 getBitSize(void) const;

        //! Returns the id of the register.
        triton::arch::registers_e getId(void) const;

        //! Returns the size (in bytes) of the register.
        triton::uint32 getSize(void) const;

        //! Returns the type of the operand (triton::arch::OP_REG).
        triton::uint32 getType(void) const;

        //! Compare two registers specifications
        bool operator==(const RegisterSpec& other) const;

        //! Compare two registers specifications
        bool operator!=(const RegisterSpec& other) const;

        //! Copies a RegisterSpec.
        void operator=(const RegisterSpec& other);
    };

    /*! \class Register
     *  \brief This class is used to bind a value on a RegisterSpec
     */
    class Register : public RegisterSpec {

      protected:
        //! The concrete value (content of the register)
        triton::uint512 concreteValue;

        //! True if this register contains a concrete value.
        bool concreteValueDefined;

      public:
        //! Constructor.
        Register();

        //! Constructor.
        Register(const Register& spec);

        //! Constructor.
        Register(const RegisterSpec& spec);

        //! Constructor.
        Register(const RegisterSpec& spec, triton::uint512 concreteValue);

        //! Constructor.
        Register(const triton::arch::CpuInterface&, triton::arch::registers_e regId);

        //! Constructor.
        Register(const triton::arch::CpuInterface&, triton::arch::registers_e regId, triton::uint512 concreteValue);

        //! Returns true if the register contains a concrete value.
        bool hasConcreteValue(void) const;

        //! Returns the concrete value.
        triton::uint512 getConcreteValue(void) const;

        //! Sets the concrete value of the register.
        void setConcreteValue(triton::uint512 concreteValue);

        //! Compare two Register
        bool operator==(const Register& other) const;

        //! Compare two Register
        bool operator!=(const Register& other) const;

        //! Copies a Register.
        void operator=(const Register& other);
    };

    //! Displays a Register.
    std::ostream& operator<<(std::ostream& stream, const RegisterSpec& reg);

    //! Displays a Register.
    std::ostream& operator<<(std::ostream& stream, const RegisterSpec* reg);

    //! Compares two Register (needed for std::map)
    // FIXME This should be remove
    bool operator<(const Register& reg1, const Register& reg2);

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_REGISTEROPERAND_H */
