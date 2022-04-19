//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_BASICBLOCK_HPP
#define TRITON_BASICBLOCK_HPP

#include <ostream>
#include <vector>

#include <triton/dllexport.hpp>
#include <triton/instruction.hpp>
#include <triton/tritonTypes.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Triton namespace
  namespace arch {
  /*!
   *  \ingroup triton
   *  \addtogroup arch
   *  @{
   */

    /*! \class BasicBlock
     *  \brief This class is used to represent a basic block
     */
    class BasicBlock {
      private:
        std::vector<triton::arch::Instruction> instructions;

      public:
        //! Constructor.
        TRITON_EXPORT BasicBlock();

        //! Constructor.
        TRITON_EXPORT BasicBlock(const std::vector<triton::arch::Instruction>& instructions);

        //! Constructor by copy.
        TRITON_EXPORT BasicBlock(const BasicBlock& other);

        //! Copies an BasicBlock.
        TRITON_EXPORT BasicBlock& operator=(const BasicBlock& other);

        //! Destructor.
        TRITON_EXPORT ~BasicBlock();

        //! Add an instruction to the block
        TRITON_EXPORT void add(Instruction& instruction);

        //! Remove an instruction from the block at the given position. Returns true if success.
        TRITON_EXPORT bool remove(triton::uint32 position);

        //! Gets all instructions of the block
        TRITON_EXPORT std::vector<triton::arch::Instruction>& getInstructions(void);

        //! Returns the number of instructions in the block
        TRITON_EXPORT triton::usize getSize(void) const;

        //! Returns the first instruction's address
        TRITON_EXPORT triton::uint64 getFirstAddress(void) const;

        //! Returns the last instruction's address
        TRITON_EXPORT triton::uint64 getLastAddress(void) const;
    };

    //! Displays an BasicBlock.
    TRITON_EXPORT std::ostream& operator<<(std::ostream& stream, BasicBlock& block);

    //! Displays an BasicBlock.
    TRITON_EXPORT std::ostream& operator<<(std::ostream& stream, BasicBlock* block);

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_BASICBLOCK_HPP */
