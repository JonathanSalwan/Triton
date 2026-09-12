//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <triton/basicBlock.hpp>
#include <triton/exceptions.hpp>

namespace triton {
  namespace arch {

    BasicBlock::BasicBlock() {
    }

    BasicBlock::BasicBlock(const std::vector<triton::arch::Instruction>& instructions) {
      this->instructions = instructions;
    }

    BasicBlock::BasicBlock(const BasicBlock& other) {
      this->instructions = other.instructions;
    }

    BasicBlock& BasicBlock::operator=(const BasicBlock& other) {
      this->instructions = other.instructions;
      return *this;
    }

    BasicBlock::~BasicBlock() {
      this->instructions.clear();
    }

    void BasicBlock::add(const Instruction& instruction) {
      Instruction copy = instruction;
      if (this->instructions.size()) {
        copy.setAddress(this->instructions.back().getNextAddress());
      }
      this->instructions.push_back(copy);
    }

    bool BasicBlock::remove(triton::uint32 position) {
      if (this->instructions.size() <= position)
        return false;
      this->instructions.erase(this->instructions.begin() + position);
      return true;
    }

    std::vector<triton::arch::Instruction>& BasicBlock::getInstructions(void) {
      return this->instructions;
    }

    triton::usize BasicBlock::getSize(void) const {
      return this->instructions.size();
    }

    triton::uint64 BasicBlock::getFirstAddress(void) const {
      if (this->instructions.size() == 0)
        throw triton::exceptions::BasicBlock("BasicBlock::getFirstAddress(): No instruction in the block.");
      return this->instructions.front().getAddress();
    }

    triton::uint64 BasicBlock::getLastAddress(void) const {
      if (this->instructions.size() == 0)
        throw triton::exceptions::BasicBlock("BasicBlock::getLastAddress(): No instruction in the block.");
      return this->instructions.back().getAddress();
    }

    std::ostream& operator<<(std::ostream& stream, BasicBlock& block) {
      triton::usize size = block.getSize();
      for (const auto& inst : block.getInstructions()) {
        stream << inst;
        if (--size) {
          stream << std::endl;
        }
      }
      return stream;
    }

    std::ostream& operator<<(std::ostream& stream, BasicBlock* block) {
      stream << *block;
      return stream;
    }

  }; // namespace arch
};   // namespace triton
