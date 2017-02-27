//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_INSTRUCTION_H
#define TRITON_INSTRUCTION_H

#include <list>
#include <map>
#include <ostream>
#include <sstream>
#include <utility>
#include <vector>

#include <triton/ast.hpp>
#include <triton/memoryAccess.hpp>
#include <triton/operandWrapper.hpp>
#include <triton/register.hpp>
#include <triton/symbolicExpression.hpp>
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

    /*! \class Instruction
     *  \brief This class is used when to represent an instruction
     */
    class Instruction {

      protected:
        //! The thread id of the instruction.
        triton::uint32 tid;

        //! The address of the instruction.
        triton::uint64 address;

        //! The disassembly of the instruction. This field is set at the disassembly level.
        std::stringstream disassembly;

        //! The opcodes of the instruction.
        triton::uint8 opcodes[32];

        //! The size of the instruction.
        triton::uint32 size;

        //! The type of the instruction. This field is set at the disassembly level.
        triton::uint32 type;

        //! The prefix of the instruction. This field is set at the disassembly level.
        triton::uint32 prefix;

        //! Implicit and explicit load access (read). This field is set at the semantics level.
        std::set<std::pair<triton::arch::MemoryAccess, triton::ast::AbstractNode*>> loadAccess;

        //! Implicit and explicit store access (write). This field is set at the semantics level.
        std::set<std::pair<triton::arch::MemoryAccess, triton::ast::AbstractNode*>> storeAccess;

        //! Implicit and explicit register inputs (read). This field is set at the semantics level.
        std::set<std::pair<triton::arch::Register, triton::ast::AbstractNode*>> readRegisters;

        //! Implicit and explicit register outputs (write). This field is set at the semantics level.
        std::set<std::pair<triton::arch::Register, triton::ast::AbstractNode*>> writtenRegisters;

        //! Implicit and explicit immediate inputs (read). This field is set at the semantics level.
        std::set<std::pair<triton::arch::Immediate, triton::ast::AbstractNode*>> readImmediates;

        //! True if this instruction is a branch. This field is set at the disassembly level.
        bool branch;

        //! True if this instruction changes the control flow. This field is set at the disassembly level.
        bool controlFlow;

        //! True if the condition is taken (i.g x86: jcc, cmocc, setcc, ...). This field is set at the semantics level.
        bool conditionTaken;

        //! True if this instruction is tainted. This field is set at the semantics level.
        bool tainted;

        //! Copies an Instruction
        void copy(const Instruction& other);

      public:
        //! The memory access list
        std::list<triton::arch::MemoryAccess> memoryAccess;

        //! A registers state
        /*!
          \brief a map of <regId, regClass>
        */
        std::map<triton::uint32, triton::arch::Register> registerState;

        //! A list of operands
        std::vector<triton::arch::OperandWrapper> operands;

        //! The semantics set of the instruction.
        std::vector<triton::engines::symbolic::SymbolicExpression*> symbolicExpressions;

        //! Constructor.
        Instruction();

        //! Constructor with opcodes.
        Instruction(const triton::uint8* opcodes, triton::uint32 opSize);

        //! Constructor by copy.
        Instruction(const Instruction& other);

        //! Destructor.
        virtual ~Instruction();

        //! Copies an Instruction.
        void operator=(const Instruction& other);

        //! Returns the thread id of the instruction.
        triton::uint32 getThreadId(void) const;

        //! Sets the thread id of the instruction.
        void setThreadId(triton::uint32 tid);

        //! Returns the address of the instruction.
        triton::uint64 getAddress(void) const;

        //! Returns the next address of the instruction.
        triton::uint64 getNextAddress(void) const;

        //! Sets the address of the instruction.
        void setAddress(triton::uint64 addr);

        //! Returns the disassembly of the instruction.
        std::string getDisassembly(void) const;

        //! Returns the opcodes of the instruction.
        const triton::uint8* getOpcodes(void) const;

        //! Returns the type of the instruction.
        triton::uint32 getType(void) const;

        //! Returns the prefix of the instruction.
        triton::uint32 getPrefix(void) const;

        //! Returns the list of all implicit and explicit load access
        const std::set<std::pair<triton::arch::MemoryAccess, triton::ast::AbstractNode*>>& getLoadAccess(void) const;

        //! Returns the list of all implicit and explicit store access
        const std::set<std::pair<triton::arch::MemoryAccess, triton::ast::AbstractNode*>>& getStoreAccess(void) const;

        //! Returns the list of all implicit and explicit register (flags includes) inputs (read)
        const std::set<std::pair<triton::arch::Register, triton::ast::AbstractNode*>>& getReadRegisters(void) const;

        //! Returns the list of all implicit and explicit register (flags includes) outputs (write)
        const std::set<std::pair<triton::arch::Register, triton::ast::AbstractNode*>>& getWrittenRegisters(void) const;

        //! Returns the list of all implicit and explicit immediate inputs (read)
        const std::set<std::pair<triton::arch::Immediate, triton::ast::AbstractNode*>>& getReadImmediates(void) const;

        //! Returns the register state which has been recorded.
        triton::arch::Register getRegisterState(triton::uint32 regId);

        //! Sets the opcodes of the instruction.
        void setOpcodes(const triton::uint8* opcodes, triton::uint32 size);

        //! Returns the size of the instruction.
        triton::uint32 getSize(void) const;

        //! Sets a load access.
        void setLoadAccess(const triton::arch::MemoryAccess& mem, triton::ast::AbstractNode* node);

        //! Removes a load access.
        void removeLoadAccess(const triton::arch::MemoryAccess& mem);

        //! Sets a store access.
        void setStoreAccess(const triton::arch::MemoryAccess& mem, triton::ast::AbstractNode* node);

        //! Removes a store access.
        void removeStoreAccess(const triton::arch::MemoryAccess& mem);

        //! Sets a read register.
        void setReadRegister(const triton::arch::Register& reg, triton::ast::AbstractNode* node);

        //! Removes a read register.
        void removeReadRegister(const triton::arch::Register& reg);

        //! Sets a written register.
        void setWrittenRegister(const triton::arch::Register& reg, triton::ast::AbstractNode* node);

        //! Removes a written register.
        void removeWrittenRegister(const triton::arch::Register& reg);

        //! Sets a read immediate.
        void setReadImmediate(const triton::arch::Immediate& imm, triton::ast::AbstractNode* node);

        //! Removes a read immediate.
        void removeReadImmediate(const triton::arch::Immediate& imm);

        //! Sets the size of the instruction.
        void setSize(triton::uint32 size);

        //! Sets the type of the instruction.
        void setType(triton::uint32 type);

        //! Sets the prefix of the instruction.
        void setPrefix(triton::uint32 prefix);

        //! Sets the disassembly of the instruction.
        void setDisassembly(const std::string& str);

        //! Sets the taint of the instruction.
        void setTaint(bool state);

        //! Sets the taint of the instruction based on its expressions.
        void setTaint(void);

        //! Records an instruction context for a memory access.
        void updateContext(const triton::arch::MemoryAccess& mem);

        //! Records an instruction context for a register state.
        void updateContext(const triton::arch::Register& reg);

        //! Adds a symbolic expression
        void addSymbolicExpression(triton::engines::symbolic::SymbolicExpression* expr);

        //! Returns true if this instruction is a branch
        bool isBranch(void) const;

        //! Returns true if this instruction changes the control flow (e.g x86: JMP, JCC, CALL, RET, ...)
        bool isControlFlow(void) const;

        //! Returns true if the condition is taken (e.g x86: jcc, cmovcc, setcc, ...).
        bool isConditionTaken(void) const;

        //! Returns true if at least one of its expressions is tainted.
        bool isTainted(void) const;

        //! Returns true if at least one of its expressions contains a symbolic variable.
        bool isSymbolized(void) const;

        //! Returns true if the instruction contains an expression which reads the memory.
        bool isMemoryRead(void) const;

        //! Returns true if the instruction contains an expression which writes into the memory.
        bool isMemoryWrite(void) const;

        //! Returns whether the instruction writes the specified operand.
        bool isWriteTo(const triton::arch::OperandWrapper& target) const;

        //! Returns whether the instruction reads the specified operand.
        bool isReadFrom(const triton::arch::OperandWrapper& target) const;

        //! Returns true if the instruction has a prefix.
        bool isPrefixed(void) const;

        //! Sets flag to define this instruction as branch or not.
        void setBranch(bool flag);

        //! Sets flag to define this instruction changes the control flow or not.
        void setControlFlow(bool flag);

        //! Sets flag to define if the condition is taken or not.
        void setConditionTaken(bool flag);

        //! Resets all instruction information.
        void reset(void);

        //! Resets partially instruction information. All except memory and register states.
        void partialReset(void);
    };

    //! Displays an Instruction.
    std::ostream& operator<<(std::ostream& stream, const Instruction& inst);

    //! Displays an Instruction.
    std::ostream& operator<<(std::ostream& stream, const Instruction* inst);

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_INSTRUCTION_H */
