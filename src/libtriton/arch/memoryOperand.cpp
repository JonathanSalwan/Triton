//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
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


    MemoryOperand::MemoryOperand(triton::__uint address, triton::uint32 size /* bytes */, triton::uint512 concreteValue) {
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


    MemoryOperand::MemoryOperand(const MemoryOperand& other) {
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


    triton::__uint MemoryOperand::getAddress(void) const {
      return this->address;
    }


    triton::ast::AbstractNode* MemoryOperand::getLeaAst(void) const {
      return this->ast;
    }


    void MemoryOperand::initAddress(void) {
      /* Otherwise, try to compute the address */
      if (triton::api.isArchitectureValid() && this->getBitSize() >= BYTE_SIZE_BIT) {
        RegisterOperand& base         = this->baseReg;
        RegisterOperand& index        = this->indexReg;
        RegisterOperand& segment      = this->segmentReg;
        triton::__uint baseValue      = (this->pcRelative ? this->pcRelative : (base.isValid() ? triton::api.getRegisterValue(base).convert_to<triton::__uint>() : 0));
        triton::__uint indexValue     = (index.isValid() ? triton::api.getRegisterValue(index).convert_to<triton::__uint>() : 0);
        triton::__uint segmentValue   = (segment.isValid() ? triton::api.getRegisterValue(segment).convert_to<triton::__uint>() : 0);
        triton::__uint scaleValue     = this->scale.getValue();
        triton::__uint dispValue      = this->displacement.getValue();
        triton::__uint mask           = -1;
        triton::uint32 bitSize        = (index.isValid() ? index.getBitSize() : base.isValid() ? base.getBitSize() : segment.isValid() ? segment.getBitSize() : triton::api.cpuRegisterBitSize());

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

        /*
         * If the symbolic emulation is enabled, use segments as
         * base address instead of selector into the GDT.
         */
        if (triton::api.isSymbolicEmulationEnabled()) {
          this->ast = triton::ast::bvadd(
                        triton::ast::bv(segmentValue, bitSize),
                        this->ast
                      );
        }

        /* Initialize the address only if it is not already defined */
        if (!this->address) {
          /* LEA computation */
          this->address = (((baseValue + (indexValue * scaleValue)) + dispValue) & mask);
          /*
           * If the symbolic emulation is enabled, use segments as
           * base address instead of selector into the GDT.
           */
          if (triton::api.isSymbolicEmulationEnabled())
            this->address += segmentValue;
        }

      }
    }


    triton::uint32 MemoryOperand::getBitSize(void) const {
      return this->getVectorSize();
    }


    triton::uint512 MemoryOperand::getConcreteValue(void) const {
      return this->concreteValue;
    }


    triton::__uint MemoryOperand::getPcRelative(void) const {
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


    void MemoryOperand::setAddress(triton::__uint addr) {
      this->address = addr;
    }


    void MemoryOperand::setConcreteValue(triton::uint512 concreteValue) {
      if (concreteValue > this->getMaxValue())
        throw std::runtime_error("MemoryOperand::MemoryOperand(): You cannot set this concrete value (too big) to this memory access.");
      this->concreteValue = concreteValue;
      this->trusted       = true;
    }


    void MemoryOperand::setPcRelative(triton::__uint addr) {
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
      this->copy(other);
    }


    void MemoryOperand::copy(const MemoryOperand& other) {
      this->address       = other.address;
      this->ast           = other.ast;
      this->baseReg       = other.baseReg;
      this->concreteValue = other.concreteValue;
      this->displacement  = other.displacement;
      this->high          = other.high;
      this->indexReg      = other.indexReg;
      this->low           = other.low;
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
