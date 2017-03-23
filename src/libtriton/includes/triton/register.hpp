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

    /*! \class Register
     *  \brief This class is used when an instruction has a register operand.
     */
    class Register : public BitsVector, public OperandInterface {

      protected:
        //! The name of the register.
        std::string name;

        //! The id of the register.
        triton::uint32 id;

        //! The parent id of the register.
        triton::uint32 parent;

        //! The concrete value (content of the register)
        triton::uint512 concreteValue;

        //! True if this register contains a concrete value.
        bool concreteValueDefined;

        //! True if this register is immutable regarding concrete values.
        bool immutable;

        //! Copies a Register.
        void copy(const Register& other);

        //! Setup everything.
        void setup(triton::uint32 regId);

        //! Resets information.
        void clear(void);

      public:
        //! Constructor.
        Register();

        //! Constructor.
        Register(triton::uint32 regId);

        //! Constructor.
        Register(triton::uint32 regId, triton::uint512 concreteValue);

        //! Constructor.
        Register(triton::uint32 regId, triton::uint512 concreteValue, bool immutable);

        //! Constructor by copy.
        Register(const Register& other);

        //! Copies a Register.
        void operator=(const Register& other);

        //! Destructor.
        virtual ~Register();

        //! Returns the parent id of the register.
        Register getParent(void) const;

        //! Returns true if the register is immutable.
        bool isImmutable(void) const;

        //! Returns true if `other` and `self` overlap.
        bool isOverlapWith(const Register& other) const;

        //! Returns true if the register contains a concrete value.
        bool hasConcreteValue(void) const;

        //! Returns the name of the register.
        std::string getName(void) const;

        //! Returns the highest bit of the register vector. \sa BitsVector::getHigh()
        triton::uint32 getAbstractHigh(void) const;

        //! Returns the lower bit of the register vector. \sa BitsVector::getLow()
        triton::uint32 getAbstractLow(void) const;

        //! Returns the size (in bits) of the register.
        triton::uint32 getBitSize(void) const;

        //! Returns the id of the register.
        triton::uint32 getId(void) const;

        //! Returns the size (in bytes) of the register.
        triton::uint32 getSize(void) const;

        //! Returns the type of the operand (triton::arch::OP_REG).
        triton::uint32 getType(void) const;

        //! Returns the concrete value.
        triton::uint512 getConcreteValue(void) const;

        //! Sets the name of the register.
        void setName(const std::string& name);

        //! Sets the id of the register.
        void setId(triton::uint32 regId);

        //! Sets the parent id of the register.
        void setParent(triton::uint32 regId);

        //! Sets the concrete value of the register.
        void setConcreteValue(triton::uint512 concreteValue);
    };

    //! Displays a Register.
    std::ostream& operator<<(std::ostream& stream, const Register& reg);

    //! Displays a Register.
    std::ostream& operator<<(std::ostream& stream, const Register* reg);

    //! Compares two Register.
    bool operator==(const Register& reg1, const Register& reg2);

    //! Compares two Register.
    bool operator!=(const Register& reg1, const Register& reg2);

    //! Compares two Register (needed for std::map)
    bool operator<(const Register& reg1, const Register& reg2);

    //! Defines the invalid register constant.
    const triton::uint32 INVALID_REGISTER_ID = 0;

    //! Defines the immutable register constant.
    const bool IMMUTABLE_REGISTER = true;

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_REGISTEROPERAND_H */
