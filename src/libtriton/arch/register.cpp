//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <api.hpp>
#include <exceptions.hpp>
#include <register.hpp>
#include <registerSpecification.hpp>



namespace triton {
  namespace arch {

    Register::Register() {
      this->clear();
    }


    Register::Register(triton::uint32 regId) {
      if (!triton::api.isArchitectureValid()) {
        this->clear();
        return;
      }

      this->setup(regId);
      this->isImmutable          = false;
      this->concreteValueDefined = false;
    }


    Register::Register(triton::uint32 regId, bool isImmutable) {
      if (!triton::api.isArchitectureValid()) {
        this->clear();
        return;
      }

      this->setup(regId);
      this->isImmutable          = isImmutable;
      this->concreteValueDefined = false;
    }


    Register::Register(triton::uint32 regId, triton::uint512 concreteValue) {
      if (!triton::api.isArchitectureValid()) {
        this->clear();
        return;
      }

      this->setup(regId);
      this->isImmutable = false;
      this->setConcreteValue(concreteValue);
    }


    Register::Register(const Register& other) : BitsVector(other) {
      this->copy(other);
    }


    Register::Register(const Register& other, bool isImmutable) : Register(other) {
      this->isImmutable = isImmutable;
    }


    Register::~Register() {
    }


    void Register::operator=(const Register& other) {
      BitsVector::operator=(other);
      this->copy(other);
    }


    void Register::clear(void) {
      this->concreteValue        = 0;
      this->concreteValueDefined = false;
      this->id                   = triton::arch::INVALID_REGISTER_ID;
      this->isImmutable          = false;
      this->name                 = "unknown";
      this->parent               = triton::arch::INVALID_REGISTER_ID;
    }


    void Register::setup(triton::uint32 regId) {
      triton::arch::RegisterSpecification regInfo;

      this->id = regId;
      if (!triton::api.isCpuRegisterValid(regId))
        this->id = triton::arch::INVALID_REGISTER_ID;

      regInfo      = triton::api.getRegisterSpecification(this->id);
      this->name   = regInfo.getName();
      this->parent = regInfo.getParentId();

      this->setHigh(regInfo.getHigh());
      this->setLow(regInfo.getLow());
    }


    void Register::copy(const Register& other) {
      this->concreteValue        = other.concreteValue;
      this->concreteValueDefined = other.concreteValueDefined;
      this->id                   = other.id;
      this->isImmutable          = false;
      this->name                 = other.name;
      this->parent               = other.parent;
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


    void Register::setId(triton::uint32 regId) {
      this->id = regId;
    }


    void Register::setParent(triton::uint32 regId) {
      this->parent = regId;
    }


    void Register::setConcreteValue(triton::uint512 concreteValue) {
      if (concreteValue > this->getMaxValue())
        throw triton::exceptions::Register("Register::setConcreteValue(): You cannot set this concrete value (too big) to this register.");

      if (this->isImmutable)
        return;

      this->concreteValue        = concreteValue;
      this->concreteValueDefined = true;
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


    bool Register::hasConcreteValue(void) const {
      return this->concreteValueDefined;
    }


    std::ostream& operator<<(std::ostream& stream, const Register& reg) {
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
