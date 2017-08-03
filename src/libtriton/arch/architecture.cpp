//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <new>

#include <triton/architecture.hpp>
#include <triton/exceptions.hpp>
#include <triton/x8664Cpu.hpp>
#include <triton/x86Cpu.hpp>



namespace triton {
  namespace arch {

    Architecture::Architecture(triton::callbacks::Callbacks* callbacks) {
      this->arch      = triton::arch::ARCH_INVALID;
      this->callbacks = callbacks;
    }


    triton::uint32 Architecture::getArchitecture(void) const {
      return this->arch;
    }


    triton::arch::CpuInterface* Architecture::getCpu(void) {
      if (!this->cpu)
        throw triton::exceptions::Architecture("Architecture::getCpu(): CPU undefined.");
      return this->cpu.get();
    }


    void Architecture::setArchitecture(triton::uint32 arch) {
      /* Check if the architecture is valid */
      if (!(arch > triton::arch::ARCH_INVALID && arch < triton::arch::ARCH_LAST_ITEM))
        throw triton::exceptions::Architecture("Architecture::setArchitecture(): Invalid architecture.");

      /* Setup global variables */
      this->arch = arch;

      /* Allocate and init the good arch */
      switch (this->arch) {
        case triton::arch::ARCH_X86_64:
          /* init the new instance */
          this->cpu.reset(new(std::nothrow) triton::arch::x86::x8664Cpu(this->callbacks));
          if (this->cpu == nullptr)
            throw triton::exceptions::Architecture("Architecture::setArchitecture(): Not enough memory.");
          break;

        case triton::arch::ARCH_X86:
          /* init the new instance */
          this->cpu.reset(new(std::nothrow) triton::arch::x86::x86Cpu(this->callbacks));
          if (this->cpu == nullptr)
            throw triton::exceptions::Architecture("Architecture::setArchitecture(): Not enough memory.");
          break;
      }
    }


    void Architecture::clearArchitecture(void) {
      if (!this->cpu)
        throw triton::exceptions::Architecture("Architecture::clearArchitecture(): You must define an architecture.");
      this->cpu->clear();
    }


    bool Architecture::isValid(void) const {
      if (this->arch == triton::arch::ARCH_INVALID)
        return false;
      return true;
    }


    bool Architecture::isFlag(triton::arch::registers_e regId) const {
      if (!this->cpu)
        return false;
      return this->cpu->isFlag(regId);
    }


    bool Architecture::isFlag(const triton::arch::Register& reg) const {
      return this->isFlag(reg.getId());
    }


    bool Architecture::isRegister(triton::arch::registers_e regId) const {
      if (!this->cpu)
        return false;
      return this->cpu->isRegister(regId);
    }


    bool Architecture::isRegister(const triton::arch::Register& reg) const {
      return this->isRegister(reg.getId());
    }


    bool Architecture::isRegisterValid(triton::arch::registers_e regId) const {
      if (!this->cpu)
        return false;
      return this->cpu->isRegisterValid(regId);
    }


    bool Architecture::isRegisterValid(const triton::arch::Register& reg) const {
      return this->isRegisterValid(reg.getId());
    }


    triton::uint32 Architecture::numberOfRegisters(void) const {
      if (!this->cpu)
        return 0;
      return this->cpu->numberOfRegisters();
    }


    triton::uint32 Architecture::registerSize(void) const {
      if (!this->cpu)
        return 0;
      return this->cpu->registerSize();
    }


    triton::uint32 Architecture::registerBitSize(void) const {
      if (!this->cpu)
        return 0;
      return this->cpu->registerBitSize();
    }


    const std::unordered_map<registers_e, const triton::arch::Register>& Architecture::getAllRegisters(void) const {
      if (!this->cpu)
        throw triton::exceptions::Architecture("Architecture::getAllRegisters(): You must define an architecture.");
      return this->cpu->getAllRegisters();
    }


    std::set<const triton::arch::Register*> Architecture::getParentRegisters(void) const {
      if (!this->cpu)
        throw triton::exceptions::Architecture("Architecture::getParentRegisters(): You must define an architecture.");
      return this->cpu->getParentRegisters();
    }


    const triton::arch::Register& Architecture::getRegister(triton::arch::registers_e id) const {
      if (!this->cpu)
        throw triton::exceptions::Architecture("Architecture::getRegister(): You must define an architecture.");
      return this->cpu->getRegister(id);
    }


    const triton::arch::Register& Architecture::getParentRegister(const triton::arch::Register& reg) const {
      if (!this->cpu)
        throw triton::exceptions::Architecture("Architecture::getParentRegister(): You must define an architecture.");
      return this->cpu->getParentRegister(reg);
    }


    const triton::arch::Register& Architecture::getParentRegister(triton::arch::registers_e id) const {
      if (!this->cpu)
        throw triton::exceptions::Architecture("Architecture::getParentRegister(): You must define an architecture.");
      return this->cpu->getParentRegister(id);
    }


    void Architecture::disassembly(triton::arch::Instruction& inst) const {
      if (!this->cpu)
        throw triton::exceptions::Architecture("Architecture::disassembly(): You must define an architecture.");
      this->cpu->disassembly(inst);
    }


    triton::uint8 Architecture::getConcreteMemoryValue(triton::uint64 addr) const {
      if (!this->cpu)
        throw triton::exceptions::Architecture("Architecture::getConcreteMemoryValue(): You must define an architecture.");
      return this->cpu->getConcreteMemoryValue(addr);
    }


    triton::uint512 Architecture::getConcreteMemoryValue(const triton::arch::MemoryAccess& mem, bool execCallbacks) const {
      if (!this->cpu)
        throw triton::exceptions::Architecture("Architecture::getConcreteMemoryValue(): You must define an architecture.");
      return this->cpu->getConcreteMemoryValue(mem, execCallbacks);
    }


    std::vector<triton::uint8> Architecture::getConcreteMemoryAreaValue(triton::uint64 baseAddr, triton::usize size, bool execCallbacks) const {
      if (!this->cpu)
        throw triton::exceptions::Architecture("Architecture::getConcreteMemoryAreaValue(): You must define an architecture.");
      return this->cpu->getConcreteMemoryAreaValue(baseAddr, size, execCallbacks);
    }


    triton::uint512 Architecture::getConcreteRegisterValue(const triton::arch::Register& reg, bool execCallbacks) const {
      if (!this->cpu)
        throw triton::exceptions::Architecture("Architecture::getConcreteRegisterValue(): You must define an architecture.");
      return this->cpu->getConcreteRegisterValue(reg, execCallbacks);
    }


    void Architecture::setConcreteMemoryValue(triton::uint64 addr, triton::uint8 value) {
      if (!this->cpu)
        throw triton::exceptions::Architecture("Architecture::setConcreteMemoryValue(): You must define an architecture.");
      this->cpu->setConcreteMemoryValue(addr, value);
    }


    void Architecture::setConcreteMemoryValue(const triton::arch::MemoryAccess& mem, const triton::uint512& value) {
      if (!this->cpu)
        throw triton::exceptions::Architecture("Architecture::setConcreteMemoryValue(): You must define an architecture.");
      this->cpu->setConcreteMemoryValue(mem, value);
    }


    void Architecture::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const std::vector<triton::uint8>& values) {
      if (!this->cpu)
        throw triton::exceptions::Architecture("Architecture::setConcreteMemoryAreaValue(): You must define an architecture.");
      this->cpu->setConcreteMemoryAreaValue(baseAddr, values);
    }


    void Architecture::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const triton::uint8* area, triton::usize size) {
      if (!this->cpu)
        throw triton::exceptions::Architecture("Architecture::setConcreteMemoryAreaValue(): You must define an architecture.");
      this->cpu->setConcreteMemoryAreaValue(baseAddr, area, size);
    }


    void Architecture::setConcreteRegisterValue(const triton::arch::Register& reg, const triton::uint512& value) {
      if (!this->cpu)
        throw triton::exceptions::Architecture("Architecture::setConcreteRegisterValue(): You must define an architecture.");
      this->cpu->setConcreteRegisterValue(reg, value);
    }


    bool Architecture::isMemoryMapped(triton::uint64 baseAddr, triton::usize size) {
      if (!this->cpu)
        throw triton::exceptions::Architecture("Architecture::isMemoryMapped(): You must define an architecture.");
      return this->cpu->isMemoryMapped(baseAddr, size);
    }


    void Architecture::unmapMemory(triton::uint64 baseAddr, triton::usize size) {
      if (!this->cpu)
        throw triton::exceptions::Architecture("Architecture::unmapMemory(): You must define an architecture.");
      this->cpu->unmapMemory(baseAddr, size);
    }

  }; /* arch namespace */
}; /* triton namespace */

