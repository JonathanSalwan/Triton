//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>
#include <api.hpp>
#include <registerOperand.hpp>



namespace triton {
  namespace arch {

    RegisterOperand::RegisterOperand() {
      this->clear();
    }


    RegisterOperand::RegisterOperand(triton::uint32 reg, triton::uint128 concreteValue) {
      if (!triton::api.isArchitectureValid()) {
        this->clear();
        return;
      }
      this->setup(reg, concreteValue);
    }


    void RegisterOperand::clear(void) {
      this->name    = "unknown";
      this->id      = triton::api.cpuInvalidReg();
      this->parent  = triton::api.cpuInvalidReg();
      this->trusted = false;
    }


    void RegisterOperand::setup(triton::uint32 reg, triton::uint128 concreteValue) {
      std::tuple<std::string, triton::uint32, triton::uint32, triton::uint32> regInfo;

      this->id        = reg;
      this->trusted   = true;

      if (!triton::api.isCpuRegValid(reg)) {
        this->id      = triton::api.cpuInvalidReg();
        this->trusted = false;
      }

      regInfo      = triton::api.getCpuRegInformation(this->id);

      this->name   = std::get<0>(regInfo);
      this->parent = std::get<3>(regInfo);

      this->setHigh(std::get<1>(regInfo));
      this->setLow(std::get<2>(regInfo));

      if (concreteValue != 0 && this->isFlag())
        throw std::runtime_error("RegisterOperand::setup(): You cannot set a concrete value on an isolated flag.");

      this->concreteValue = concreteValue;
    }


    RegisterOperand::RegisterOperand(const RegisterOperand& other) {
      this->copy(other);
    }


    RegisterOperand::~RegisterOperand() {
    }


    triton::uint32 RegisterOperand::getAbstractLow(void) const {
      return this->getLow();
    }


    triton::uint32 RegisterOperand::getAbstractHigh(void) const {
      return this->getHigh();
    }


    triton::uint32 RegisterOperand::getId(void) const {
      return this->id;
    }


    RegisterOperand RegisterOperand::getParent(void) const {
      return RegisterOperand(this->parent);
    }


    triton::uint32 RegisterOperand::getBitSize(void) const {
      return this->getVectorSize();
    }


    triton::uint32 RegisterOperand::getSize(void) const {
      return this->getVectorSize() / BYTE_SIZE_BIT;
    }


    std::string RegisterOperand::getName(void) const {
      return this->name;
    }


    triton::uint32 RegisterOperand::getType(void) const {
      return triton::arch::OP_REG;
    }


    triton::uint128 RegisterOperand::getConcreteValue(void) const {
      return this->concreteValue;
    }


    bool RegisterOperand::isTrusted(void) {
      return this->trusted;
    }


    void RegisterOperand::setTrust(bool flag) {
      this->trusted = flag;
    }


    void RegisterOperand::setId(triton::uint32 reg) {
      this->id = reg;
    }


    void RegisterOperand::setParent(triton::uint32 reg) {
      this->parent = reg;
    }


    void RegisterOperand::setConcreteValue(triton::uint128 concreteValue) {
      if (this->isFlag())
        throw std::runtime_error("RegisterOperand::setConcreteValue(): You cannot set a concrete value on an isolated flag.");
      this->concreteValue = concreteValue;
      this->trusted       = true;
    }


    bool RegisterOperand::isValid(void) {
      return triton::api.isCpuRegValid(this->id);
    }


    bool RegisterOperand::isReg(void) {
      return triton::api.isCpuReg(this->id);
    }


    bool RegisterOperand::isFlag(void) {
      return triton::api.isCpuFlag(this->id);
    }


    void RegisterOperand::operator=(const RegisterOperand& other) {
      this->copy(other);
    }


    void RegisterOperand::copy(const RegisterOperand& other) {
      this->concreteValue = other.concreteValue;
      this->high          = other.high;
      this->id            = other.id;
      this->low           = other.low;
      this->name          = other.name;
      this->parent        = other.parent;
      this->trusted       = other.trusted;
    }


    std::ostream &operator<<(std::ostream &stream, RegisterOperand reg) {
      stream << reg.getName() << ":" << reg.getBitSize() << " bv[" << reg.getHigh() << ".." << reg.getLow() << "]";
      return stream;
    }


    bool operator==(RegisterOperand& reg1, RegisterOperand& reg2) {
      return reg1.getId() == reg2.getId();
    }

  }; /* arch namespace */
}; /* triton namespace */
