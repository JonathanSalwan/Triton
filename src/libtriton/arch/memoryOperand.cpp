//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <stdexcept>

#include <api.hpp>
#include <cpuSize.hpp>
#include <memoryOperand.hpp>



namespace triton {
  namespace arch {

    MemoryOperand::MemoryOperand() {
      this->address       = 0;
      this->ast           = nullptr;
      this->concreteValue = 0;
      this->trusted       = false;
      this->pcRelative    = 0;
    }


    MemoryOperand::MemoryOperand(triton::uint64 address, triton::uint32 size /* bytes */, triton::uint512 concreteValue) {
      this->address       = address;
      this->ast           = nullptr;
      this->concreteValue = concreteValue;
      this->trusted       = true;
      this->pcRelative    = 0;

      if (size == 0)
        throw std::runtime_error("MemoryOperand::MemoryOperand(): size cannot be zero.");

      if (size != BYTE_SIZE && size != WORD_SIZE && size != DWORD_SIZE && size != QWORD_SIZE && size != DQWORD_SIZE && size != QQWORD_SIZE && size != DQQWORD_SIZE)
        throw std::runtime_error("MemoryOperand::MemoryOperand(): size must be aligned.");

      this->setPair(std::make_pair(((size * BYTE_SIZE_BIT) - 1), 0));

      if (concreteValue > this->getMaxValue())
        throw std::runtime_error("MemoryOperand::MemoryOperand(): You cannot set this concrete value (too big) to this memory access.");
    }


    MemoryOperand::MemoryOperand(const MemoryOperand& other) : BitsVector(other) {
      this->copy(other);
    }


    MemoryOperand::~MemoryOperand() {
    }


    triton::uint32 MemoryOperand::getAbstractLow(void) const {
      return this->getLow();
    }


    triton::uint32 MemoryOperand::getAbstractHigh(void) const {
      return this->getHigh();
    }


    triton::uint64 MemoryOperand::getAddress(void) const {
      return this->address;
    }


    triton::ast::AbstractNode* MemoryOperand::getLeaAst(void) const {
      return this->ast;
    }


    triton::uint64 MemoryOperand::getBaseValue(void) {
      if (this->pcRelative)
        return this->pcRelative;

      else if (this->baseReg.isValid())
        return triton::api.getConcreteRegisterValue(this->baseReg).convert_to<triton::uint64>();

      return 0;
    }


    triton::uint64 MemoryOperand::getIndexValue(void) {
      if (this->indexReg.isValid())
        return triton::api.getConcreteRegisterValue(this->indexReg).convert_to<triton::uint64>();
      return 0;
    }


    triton::uint64 MemoryOperand::getSegmentValue(void) {
      if (this->segmentReg.isValid())
        return triton::api.getConcreteRegisterValue(this->segmentReg).convert_to<triton::uint64>();
      return 0;
    }


    triton::uint64 MemoryOperand::getScaleValue(void) {
      return this->scale.getValue();
    }


    triton::uint64 MemoryOperand::getDisplacementValue(void) {
      return this->displacement.getValue();
    }


    triton::uint64 MemoryOperand::getAccessMask(void) {
      triton::uint64 mask = -1;
      return (mask >> (QWORD_SIZE_BIT - triton::api.cpuRegisterBitSize()));
    }


    triton::uint32 MemoryOperand::getAccessSize(void) {
      if (this->indexReg.isValid())
        return this->indexReg.getBitSize();

      else if (this->baseReg.isValid())
        return this->baseReg.getBitSize();

      else if (this->displacement.getBitSize())
        return this->displacement.getBitSize();

      return triton::api.cpuRegisterBitSize();
    }


    void MemoryOperand::initAddress(void) {
      /* Otherwise, try to compute the address */
      if (triton::api.isArchitectureValid() && this->getBitSize() >= BYTE_SIZE_BIT) {
        RegisterOperand& base         = this->baseReg;
        RegisterOperand& index        = this->indexReg;
        triton::uint64 segmentValue   = this->getSegmentValue();
        triton::uint64 scaleValue     = this->getScaleValue();
        triton::uint64 dispValue      = this->getDisplacementValue();
        triton::uint32 bitSize        = this->getAccessSize();

        /* Initialize the AST of the memory access (LEA) */
        this->ast = triton::ast::bvadd(
                      (this->pcRelative ? triton::ast::bv(this->pcRelative, bitSize) : (base.isValid() ? triton::api.buildSymbolicRegisterOperand(base) : triton::ast::bv(0, bitSize))),
                      triton::ast::bvadd(
                        triton::ast::bvmul(
                          (index.isValid() ? triton::api.buildSymbolicRegisterOperand(index) : triton::ast::bv(0, bitSize)),
                          triton::ast::bv(scaleValue, bitSize)
                        ),
                        triton::ast::bv(dispValue, bitSize)
                      )
                    );

        /* Use segments as base address instead of selector into the GDT. */
        if (segmentValue) {
          this->ast = triton::ast::bvadd(
                        triton::ast::bv(segmentValue, this->segmentReg.getBitSize()),
                        triton::ast::sx((this->segmentReg.getBitSize() - bitSize), this->ast)
                      );
        }

        /* Initialize the address only if it is not already defined */
        if (!this->address)
          this->address = this->ast->evaluate().convert_to<triton::uint64>();
      }
    }


    triton::uint32 MemoryOperand::getBitSize(void) const {
      return this->getVectorSize();
    }


    triton::uint512 MemoryOperand::getConcreteValue(void) const {
      return this->concreteValue;
    }


    triton::uint64 MemoryOperand::getPcRelative(void) const {
      return this->pcRelative;
    }


    triton::uint32 MemoryOperand::getSize(void) const {
      return this->getVectorSize() / BYTE_SIZE_BIT;
    }


    triton::uint32 MemoryOperand::getType(void) const {
      return triton::arch::OP_MEM;
    }


    RegisterOperand& MemoryOperand::getSegmentRegister(void) {
      return this->segmentReg;
    }


    RegisterOperand& MemoryOperand::getBaseRegister(void) {
      return this->baseReg;
    }


    RegisterOperand& MemoryOperand::getIndexRegister(void) {
      return this->indexReg;
    }


    ImmediateOperand& MemoryOperand::getDisplacement(void) {
      return this->displacement;
    }


    ImmediateOperand& MemoryOperand::getScale(void) {
      return this->scale;
    }


    const RegisterOperand& MemoryOperand::getConstSegmentRegister(void) const {
      return this->segmentReg;
    }


    const RegisterOperand& MemoryOperand::getConstBaseRegister(void) const {
      return this->baseReg;
    }


    const RegisterOperand& MemoryOperand::getConstIndexRegister(void) const {
      return this->indexReg;
    }


    const ImmediateOperand& MemoryOperand::getConstDisplacement(void) const {
      return this->displacement;
    }


    const ImmediateOperand& MemoryOperand::getConstScale(void) const {
      return this->scale;
    }


    bool MemoryOperand::isTrusted(void) const {
      return this->trusted;
    }


    bool MemoryOperand::isValid(void) const {
      if (!this->address && !this->concreteValue && !this->trusted && !this->getLow() && !this->getHigh())
        return false;
      return true;
    }


    void MemoryOperand::setTrust(bool flag) {
      this->trusted = flag;
    }


    void MemoryOperand::setAddress(triton::uint64 addr) {
      this->address = addr;
    }


    void MemoryOperand::setConcreteValue(triton::uint512 concreteValue) {
      if (concreteValue > this->getMaxValue())
        throw std::runtime_error("MemoryOperand::MemoryOperand(): You cannot set this concrete value (too big) to this memory access.");
      this->concreteValue = concreteValue;
      this->trusted       = true;
    }


    void MemoryOperand::setPcRelative(triton::uint64 addr) {
      this->pcRelative = addr;
    }


    void MemoryOperand::setSegmentRegister(RegisterOperand& segment) {
      this->segmentReg = segment;
    }


    void MemoryOperand::setBaseRegister(RegisterOperand& base) {
      this->baseReg = base;
    }


    void MemoryOperand::setIndexRegister(RegisterOperand& index) {
      this->indexReg = index;
    }


    void MemoryOperand::setDisplacement(ImmediateOperand& displacement) {
      this->displacement = displacement;
    }


    void MemoryOperand::setScale(ImmediateOperand& scale) {
      this->scale = scale;
    }


    void MemoryOperand::operator=(const MemoryOperand &other) {
      BitsVector::operator=(other);
      this->copy(other);
    }


    void MemoryOperand::copy(const MemoryOperand& other) {
      this->address       = other.address;
      this->ast           = other.ast;
      this->baseReg       = other.baseReg;
      this->concreteValue = other.concreteValue;
      this->displacement  = other.displacement;
      this->indexReg      = other.indexReg;
      this->pcRelative    = other.pcRelative;
      this->scale         = other.scale;
      this->segmentReg    = other.segmentReg;
      this->trusted       = other.trusted;
    }


    std::ostream& operator<<(std::ostream& stream, const MemoryOperand& mem) {
      stream << "[@0x" << std::hex << mem.getAddress() << "]:" << std::dec << mem.getBitSize() << " bv[" << mem.getHigh() << ".." << mem.getLow() << "]";
      return stream;
    }


    std::ostream& operator<<(std::ostream& stream, const MemoryOperand* mem) {
      stream << *mem;
      return stream;
    }


    bool operator==(const MemoryOperand& mem1, const MemoryOperand& mem2) {
      if (mem1.getAddress() != mem2.getAddress())
        return false;
      if (mem1.getSize() != mem2.getSize())
        return false;
      if (mem1.getConcreteValue() != mem2.getConcreteValue())
        return false;
      if (mem1.getConstBaseRegister() != mem2.getConstBaseRegister())
        return false;
      if (mem1.getConstIndexRegister() != mem2.getConstIndexRegister())
        return false;
      if (mem1.getConstScale() != mem2.getConstScale())
        return false;
      if (mem1.getConstDisplacement() != mem2.getConstDisplacement())
        return false;
      if (mem1.getConstSegmentRegister() != mem2.getConstSegmentRegister())
        return false;
      if (mem1.getPcRelative() != mem2.getPcRelative())
        return false;
      return true;
    }


    bool operator!=(const MemoryOperand& mem1, const MemoryOperand& mem2) {
      if (mem1 == mem2)
        return false;
      return true;
    }


    bool operator<(const MemoryOperand& mem1, const MemoryOperand& mem2) {
      return mem1.getAddress() < mem2.getAddress();
    }

  }; /* arch namespace */
}; /* triton namespace */
