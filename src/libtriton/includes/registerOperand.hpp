//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_REGISTEROPERAND_H
#define TRITON_REGISTEROPERAND_H

#include <string>
#include <ostream>

#include "bitsVector.hpp"
#include "cpuSize.hpp"
#include "operandInterface.hpp"
#include "tritonTypes.hpp"



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The Triton namespace
  namespace arch {
  /*!
   *  \ingroup triton
   *  \addtogroup arch
   *  @{
   */

    /*! \class RegisterOperand
     *  \brief This class is used when an instruction has a register operand.
     */
    class RegisterOperand : public BitsVector, public OperandInterface {

      protected:
        //! The name of the register.
        std::string name;

        //! The id of the register.
        triton::uint32 id;

        //! The parent id of the register.
        triton::uint32 parent;

        //! The concrete value (content of the register)
        triton::uint512 concreteValue;

        //! True if this concrete register value is trusted and synchronized with the real CPU value.
        bool trusted;

        //! Copies a RegisterOperand.
        void copy(const RegisterOperand& other);

        //! Setup everything.
        void setup(triton::uint32 reg, triton::uint512 concreteValue);

        //! Resets information.
        void clear(void);

      public:
        //! Constructor.
        RegisterOperand();

        //! Constructor. You cannot set a concreteValue on a flag.
        RegisterOperand(triton::uint32 reg, triton::uint512 concreteValue=0);

        //! Constructor by copy.
        RegisterOperand(const RegisterOperand& other);

        //! Destructor.
        ~RegisterOperand();

        //! Returns the parent id of the register.
        RegisterOperand getParent(void) const;

        //! Returns true if the register is valid.
        bool isValid(void) const;

        //! Returns true if the register is a register.
        bool isRegister(void) const;

        //! Returns true if the register is a flag.
        bool isFlag(void) const;

        //! True if this concrete register value is trusted and synchronized with the real CPU value.
        bool isTrusted(void) const;

        //! Sets the trust flag.
        void setTrust(bool flag);

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

        //! Copies a RegisterOperand.
        void operator=(const RegisterOperand& other);

        //! Sets the id of the register.
        void setId(triton::uint32 reg);

        //! Sets the parent id of the register.
        void setParent(triton::uint32 reg);

        //! Sets the concrete value of the register. This method cannot be called on a flag.
        void setConcreteValue(triton::uint512 concreteValue);
    };

    //! Displays a RegisterOperand.
    std::ostream& operator<<(std::ostream& stream, const RegisterOperand& reg);

    //! Displays a RegisterOperand.
    std::ostream& operator<<(std::ostream& stream, const RegisterOperand* reg);

    //! Compares two RegisterOperand.
    bool operator==(const RegisterOperand& reg1, const RegisterOperand& reg2);

    //! Compares two RegisterOperand.
    bool operator!=(const RegisterOperand& reg1, const RegisterOperand& reg2);

    //! Compares two RegisterOperand (needed for std::map)
    bool operator<(const RegisterOperand& reg1, const RegisterOperand& reg2);

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_REGISTEROPERAND_H */
