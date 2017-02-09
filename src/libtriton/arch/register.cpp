//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <architecture.hpp>
#include <exceptions.hpp>
#include <register.hpp>
#include <registerSpecification.hpp>



namespace triton {
  namespace arch {

    Register::Register(triton::arch::CpuInterface const& cpu):
      name("unknown")
      , id(triton::arch::INVALID_REGISTER_ID)
      , parent(triton::arch::INVALID_REGISTER_ID)
      , concreteValue(0)
      , concreteValueDefined(false)
      , immutable(false)
      , cpu(cpu)
    {
    }

    Register::Register(triton::arch::CpuInterface const& cpu, triton::uint32 regId, triton::arch::RegisterSpecification const& spec): 
      BitsVector(spec.getLow(), spec.getHigh())
      , id(regId)
      , parent(spec.getParentId())
      , concreteValue(0)
      , concreteValueDefined(false)
      , immutable(false)
      , cpu(cpu)
    {}

    Register::Register(triton::arch::CpuInterface const& cpu, triton::uint32 regId): Register(cpu, cpu.isRegisterValid(regId)?regId:triton::arch::INVALID_REGISTER_ID,
                                                                         cpu.getRegisterSpecification(cpu.isRegisterValid(regId)?regId:triton::arch::INVALID_REGISTER_ID)) {
    }


    Register::Register(triton::arch::CpuInterface const& cpu, triton::uint32 regId, triton::uint512 concreteValue)
      : Register(cpu, regId) {
      this->setConcreteValue(concreteValue);
    }


    Register::Register(triton::arch::CpuInterface const& cpu, triton::uint32 regId, triton::uint512 concreteValue, bool immutable):
      Register(cpu, regId, concreteValue)
    {
        this->immutable = immutable;
    }


    Register::Register(const Register& other) : BitsVector(other), cpu(other.cpu) {
      this->copy(other);
    }


    Register::~Register() {
    }


    void Register::operator=(const Register& other) {
      BitsVector::operator=(other);
      this->copy(other);
    }


    void Register::copy(const Register& other) {
      this->concreteValue        = other.concreteValue;
      this->concreteValueDefined = other.concreteValueDefined;
      this->id                   = other.id;
      this->immutable            = false;
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


    Register Register::getParent() const {
      return Register(cpu, this->parent);
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

      if (this->immutable)
        // TODO : Should we throw an exception? Here nothing change and the user don't know
        return;

      this->concreteValue        = concreteValue;
      this->concreteValueDefined = true;
    }


    bool Register::isValid() const {
      return cpu.isRegisterValid(this->id);
    }


    bool Register::isRegister() const {
      return cpu.isRegister(this->id);
    }


    bool Register::isFlag() const {
      return cpu.isFlag(this->id);
    }


    bool Register::isImmutable(void) const {
      return this->immutable;
    }


    bool Register::isOverlapWith(const Register& other) const {
      // FIXME : parent?
      if (this->getParent().getId() == other.getParent().getId()) {
        if (this->getLow() <= other.getLow() && other.getLow() <= this->getHigh()) return true;
        if (other.getLow() <= this->getLow() && this->getLow() <= other.getHigh()) return true;
      }
      return false;
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
      return !(reg1 == reg2);
    }


    bool operator<(const Register& reg1, const Register& reg2) {
      return (reg1.getId() < reg2.getId());
    }

  }; /* arch namespace */
}; /* triton namespace */
