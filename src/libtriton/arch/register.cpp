//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <iosfwd>                       // for ostream
#include <string>                       // for string
#include <triton/cpuInterface.hpp>      // for CpuInterface
#include <triton/exceptions.hpp>        // for Register
#include <triton/register.hpp>          // for RegisterSpec, Register
#include "triton/bitsVector.hpp"        // for BitsVector
#include "triton/cpuSize.hpp"           // for BYTE_SIZE_BIT
#include "triton/operandInterface.hpp"  // for operandType_e::OP_REG
#include "triton/registers_e.hpp"       // for registers_e
#include "triton/tritonTypes.hpp"       // for uint32, uint512


namespace triton {
  namespace arch {

    ////////////////////////////////////////////
    // RegisterSpec
    ////////////////////////////////////////////

    RegisterSpec::RegisterSpec(triton::arch::registers_e regId, std::string name, triton::arch::registers_e parent, triton::uint32 high, triton::uint32 low)
      : BitsVector(high, low),
        name(name),
        id(regId),
        parent(parent) {
    }


    triton::arch::registers_e RegisterSpec::getId(void) const {
      return this->id;
    }


    triton::uint32 RegisterSpec::getAbstractLow(void) const {
      return this->getLow();
    }


    triton::uint32 RegisterSpec::getAbstractHigh(void) const {
      return this->getHigh();
    }


    triton::arch::registers_e RegisterSpec::getParent(void) const {
      return this->parent;
    }


    triton::uint32 RegisterSpec::getBitSize(void) const {
      return this->getVectorSize();
    }


    triton::uint32 RegisterSpec::getSize(void) const {
      return this->getVectorSize() / BYTE_SIZE_BIT;
    }


    std::string RegisterSpec::getName(void) const {
      return this->name;
    }


    triton::uint32 RegisterSpec::getType(void) const {
      return triton::arch::OP_REG;
    }


    bool RegisterSpec::isOverlapWith(const RegisterSpec& other) const {
      if (this->parent == other.parent) {
        if (this->getLow() <= other.getLow() && other.getLow() <= this->getHigh()) return true;
        if (other.getLow() <= this->getLow() && this->getLow() <= other.getHigh()) return true;
      }
      return false;
    }


    bool RegisterSpec::operator==(const RegisterSpec& reg1) const {
      return getId() == reg1.getId();
    }


    bool RegisterSpec::operator!=(const RegisterSpec& reg1) const {
      return !(*this == reg1);
    }


    std::ostream& operator<<(std::ostream& stream, const RegisterSpec& reg) {
      stream << reg.getName()
             << ":"
             << std::dec << reg.getBitSize()
             << " bv["
             << reg.getHigh()
             << ".."
             << reg.getLow()
             << "]";
      return stream;
    }


    std::ostream& operator<<(std::ostream& stream, const RegisterSpec* reg) {
      stream << *reg;
      return stream;
    }


    ////////////////////////////////////////////
    // Register
    ////////////////////////////////////////////

    Register::Register()
      : RegisterSpec(triton::arch::ID_REG_INVALID, "unknown", triton::arch::ID_REG_INVALID, 0, 0),
      concreteValue(0),
      concreteValueDefined(false) {
    }


    Register::Register(const RegisterSpec& spec, triton::uint512 concreteValue)
      : RegisterSpec(spec) {
      this->setConcreteValue(concreteValue);
    }


    Register::Register(const RegisterSpec& spec)
      : RegisterSpec(spec),
        concreteValue(0),
        concreteValueDefined(false) {
    }


    Register::Register(const triton::arch::CpuInterface& cpu, triton::arch::registers_e regId)
      : Register(
          (regId == triton::arch::ID_REG_INVALID) ?
          triton::arch::RegisterSpec(triton::arch::ID_REG_INVALID, "unknown", triton::arch::ID_REG_INVALID, 0, 0) : cpu.getRegister(regId)
        ) {
    }


    Register::Register(const triton::arch::CpuInterface& cpu, triton::arch::registers_e regId, triton::uint512 concreteValue)
      : Register(cpu.getRegister(regId), concreteValue) {
    }


    triton::uint512 Register::getConcreteValue(void) const {
      return this->concreteValue;
    }


    void Register::setConcreteValue(triton::uint512 concreteValue) {
      if (concreteValue > this->getMaxValue())
        throw triton::exceptions::Register("Register::setConcreteValue(): You cannot set this concrete value (too big) to this register.");

      this->concreteValue        = concreteValue;
      this->concreteValueDefined = true;
    }


    bool Register::hasConcreteValue(void) const {
      return this->concreteValueDefined;
    }


    bool Register::operator==(const Register& reg1) const {
      return (RegisterSpec::operator==(reg1) && getConcreteValue() == reg1.getConcreteValue());
    }


    bool Register::operator!=(const Register& reg1) const {
      return !(*this == reg1);
    }


    bool operator<(const Register& reg1, const Register& reg2) {
        return (reg1.getId() < reg2.getId());
    }

  }; /* arch namespace */
}; /* triton namespace */
