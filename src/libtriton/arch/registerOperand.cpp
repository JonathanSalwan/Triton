//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <api.hpp>
#include <exceptions.hpp>
#include <registerOperand.hpp>



namespace triton {
  namespace arch {

    Register::Register() {
      this->clear();
    }


    Register::Register(triton::uint32 reg, triton::uint512 concreteValue) {
      if (!triton::api.isArchitectureValid()) {
        this->clear();
        return;
      }
      this->setup(reg, concreteValue);
    }


    void Register::clear(void) {
      this->concreteValue = 0;
      this->id            = triton::api.cpuInvalidRegister();
      this->name          = "unknown";
      this->parent        = triton::api.cpuInvalidRegister();
      this->trusted       = false;
    }


    void Register::setup(triton::uint32 reg, triton::uint512 concreteValue) {
      std::tuple<std::string, triton::uint32, triton::uint32, triton::uint32> regInfo;

      this->id        = reg;
      this->trusted   = true;

      if (!triton::api.isCpuRegisterValid(reg)) {
        this->id      = triton::api.cpuInvalidRegister();
        this->trusted = false;
      }

      regInfo      = triton::api.getCpuRegInformation(this->id);

      this->name   = std::get<0>(regInfo);
      this->parent = std::get<3>(regInfo);

      this->setHigh(std::get<1>(regInfo));
      this->setLow(std::get<2>(regInfo));

      if (concreteValue > this->getMaxValue())
        throw triton::exceptions::Register("Register::setup(): You cannot set this concrete value (too big) to this register.");

      this->concreteValue = concreteValue;
    }


    Register::Register(const Register& other) : BitsVector(other) {
      this->copy(other);
    }


    Register::~Register() {
    }


    triton::uint32 Register::getAbstractLow(void) const {
      return this->getLow();
    }


    triton::uint32 Register::getAbstractHigh(void) const {
      return this->getHigh();
    }


    triton::uint32 Register::getId(void) const {
      return this->id;
    }


    Register Register::getParent(void) const {
      return Register(this->parent);
    }


    triton::uint32 Register::getBitSize(void) const {
      return this->getVectorSize();
    }


    triton::uint32 Register::getSize(void) const {
      return this->getVectorSize() / BYTE_SIZE_BIT;
    }


    std::string Register::getName(void) const {
      return this->name;
    }


    triton::uint32 Register::getType(void) const {
      return triton::arch::OP_REG;
    }


    triton::uint512 Register::getConcreteValue(void) const {
      return this->concreteValue;
    }


    bool Register::isTrusted(void) const {
      return this->trusted;
    }


    void Register::setTrust(bool flag) {
      this->trusted = flag;
    }


    void Register::setId(triton::uint32 reg) {
      this->id = reg;
    }


    void Register::setParent(triton::uint32 reg) {
      this->parent = reg;
    }


    void Register::setConcreteValue(triton::uint512 concreteValue) {
      if (concreteValue > this->getMaxValue())
        throw triton::exceptions::Register("Register::setConcreteValue(): You cannot set this concrete value (too big) to this register.");
      this->concreteValue = concreteValue;
      this->trusted       = true;
    }


    bool Register::isValid(void) const {
      return triton::api.isCpuRegisterValid(this->id);
    }


    bool Register::isRegister(void) const {
      return triton::api.isCpuRegister(this->id);
    }


    bool Register::isFlag(void) const {
      return triton::api.isCpuFlag(this->id);
    }


    void Register::operator=(const Register& other) {
      BitsVector::operator=(other);
      this->copy(other);
    }


    void Register::copy(const Register& other) {
      this->concreteValue = other.concreteValue;
      this->id            = other.id;
      this->name          = other.name;
      this->parent        = other.parent;
      this->trusted       = other.trusted;
    }


    std::ostream& operator<<(std::ostream& stream, const Register& reg) {
      stream << reg.getName() << ":" << reg.getBitSize() << " bv[" << reg.getHigh() << ".." << reg.getLow() << "]";
      return stream;
    }


    std::ostream& operator<<(std::ostream& stream, const Register* reg) {
      stream << *reg;
      return stream;
    }


    bool operator==(const Register& reg1, const Register& reg2) {
      if (reg1.getId() != reg2.getId())
        return false;
      if (reg1.getConcreteValue() != reg2.getConcreteValue())
        return false;
      return true;
    }


    bool operator!=(const Register& reg1, const Register& reg2) {
      if (reg1 == reg2)
        return false;
      return true;
    }


    bool operator<(const Register& reg1, const Register& reg2) {
      return reg1.getId() < reg2.getId();
    }


  }; /* arch namespace */
}; /* triton namespace */
