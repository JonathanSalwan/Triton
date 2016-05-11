//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_INSTRUCTION_H
#define TRITON_INSTRUCTION_H

#include <list>
#include <map>
#include <ostream>
#include <sstream>
#include <utility>
#include <vector>

#include "ast.hpp"
#include "memoryOperand.hpp"
#include "operandWrapper.hpp"
#include "registerOperand.hpp"
#include "symbolicExpression.hpp"
#include "tritonTypes.hpp"



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The Triton namespace
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
        triton::__uint address;

        //! The disassembly of the instruction.
        std::stringstream disassembly;

        //! The opcodes of the instruction.
        triton::uint8 opcodes[32];

        //! The size of the instruction.
        triton::uint32 size;

        //! The type of the instruction.
        triton::uint32 type;

        //! The prefix of the instruction.
        triton::uint32 prefix;

        //! Implicit and explicit load access (read).
        std::set<std::pair<triton::arch::MemoryOperand, triton::ast::AbstractNode*>> loadAccess;

        //! Implicit and explicit store access (write).
        std::set<std::pair<triton::arch::MemoryOperand, triton::ast::AbstractNode*>> storeAccess;

        //! Implicit and explicit register inputs (read).
        std::set<std::pair<triton::arch::RegisterOperand, triton::ast::AbstractNode*>> readRegisters;

        //! Implicit and explicit register outputs (write).
        std::set<std::pair<triton::arch::RegisterOperand, triton::ast::AbstractNode*>> writtenRegisters;

        //! Implicit and explicit immediate inputs (read).
        std::set<std::pair<triton::arch::ImmediateOperand, triton::ast::AbstractNode*>> readImmediates;

        //! True if this instruction is a branch.
        bool branch;

        //! True if this instruction changes the control flow.
        bool controlFlow;

        //! True if the condition is taken (i.g x86: jcc, cmocc, setcc, ...).
        bool conditionTaken;

        //! Copies an Instruction
        void copy(const Instruction& other);

      public:
        //! The memory access list
        std::list<triton::arch::MemoryOperand> memoryAccess;

        //! A registers state
        /*!
          \brief a map of <regId, regClass>
        */
        std::map<triton::uint32, triton::arch::RegisterOperand> registerState;

        //! A list of operands
        std::vector<triton::arch::OperandWrapper> operands;

        //! The semantics set of the instruction.
        std::vector<triton::engines::symbolic::SymbolicExpression*> symbolicExpressions;

        //! Constructor.
        Instruction();

        //! Constructor by copy.
        Instruction(const Instruction& other);

        //! Destructor.
        ~Instruction();

        //! Copies an Instruction.
        void operator=(const Instruction& other);

        //! Returns the thread id of the instruction.
        triton::uint32 getThreadId(void) const;

        //! Sets the thread id of the instruction.
        void setThreadId(triton::uint32 tid);

        //! Returns the address of the instruction.
        triton::__uint getAddress(void) const;

        //! Returns the next address of the instruction.
        triton::__uint getNextAddress(void) const;

        //! Sets the address of the instruction.
        void setAddress(triton::__uint addr);

        //! Returns the disassembly of the instruction.
        std::string getDisassembly(void) const;

        //! Returns the opcodes of the instruction.
        const triton::uint8* getOpcodes(void) const;

        //! Returns the type of the instruction.
        triton::uint32 getType(void) const;

        //! Returns the prefix of the instruction.
        triton::uint32 getPrefix(void) const;

        //! Returns the list of all implicit and explicit load access
        const std::set<std::pair<triton::arch::MemoryOperand, triton::ast::AbstractNode*>>& getLoadAccess(void) const;

        //! Returns the list of all implicit and explicit store access
        const std::set<std::pair<triton::arch::MemoryOperand, triton::ast::AbstractNode*>>& getStoreAccess(void) const;

        //! Returns the list of all implicit and explicit register (flags includes) inputs (read)
        const std::set<std::pair<triton::arch::RegisterOperand, triton::ast::AbstractNode*>>& getReadRegisters(void) const;

        //! Returns the list of all implicit and explicit register (flags includes) outputs (write)
        const std::set<std::pair<triton::arch::RegisterOperand, triton::ast::AbstractNode*>>& getWrittenRegisters(void) const;

        //! Returns the list of all implicit and explicit immediate inputs (read)
        const std::set<std::pair<triton::arch::ImmediateOperand, triton::ast::AbstractNode*>>& getReadImmediates(void) const;

        //! If there is a concrete value recorded, build the appropriate MemoryOperand. Otherwise, perfrom the analysis based on args.
        triton::arch::MemoryOperand popMemoryAccess(triton::__uint=0, triton::uint32 size=0, triton::uint512 value=0);

        //! Returns the register state which has been recorded.
        triton::arch::RegisterOperand getRegisterState(triton::uint32 regId);

        //! Sets the opcodes of the instruction.
        void setOpcodes(triton::uint8* opcodes, triton::uint32 size);

        //! Returns the size of the instruction.
        triton::uint32 getSize(void) const;

        //! Sets a load access.
        void setLoadAccess(const triton::arch::MemoryOperand& mem, triton::ast::AbstractNode* node);

        //! Sets a store access.
        void setStoreAccess(const triton::arch::MemoryOperand& mem, triton::ast::AbstractNode* node);

        //! Sets a read register.
        void setReadRegister(const triton::arch::RegisterOperand& reg, triton::ast::AbstractNode* node);

        //! Sets a written register.
        void setWrittenRegister(const triton::arch::RegisterOperand& reg, triton::ast::AbstractNode* node);

        //! Sets a read immediate.
        void setReadImmediate(const triton::arch::ImmediateOperand& imm, triton::ast::AbstractNode* node);

        //! Sets the size of the instruction.
        void setSize(triton::uint32 size);

        //! Sets the type of the instruction.
        void setType(triton::uint32 type);

        //! Sets the prefix of the instruction.
        void setPrefix(triton::uint32 prefix);

        //! Sets the disassembly of the instruction.
        void setDisassembly(std::string str);

        //! Records an instruction context for a memory access.
        void updateContext(MemoryOperand mem);

        //! Records an instruction context for a register state.
        void updateContext(RegisterOperand reg);

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

        //! Returns true if the instruction contains an expression which reads the memory.
        bool isMemoryRead(void) const;

        //! Returns true if the instruction contains an expression which writes into the memory.
        bool isMemoryWrite(void) const;

        //! Returns true if the instruction has a prefix.
        bool isPrefixed(void) const;

        //! Sets flag to define this instruction as branch or not.
        void setBranch(bool flag);

        //! Sets flag to define this instruction changes the control flow or not.
        void setControlFlow(bool flag);

        //! Sets flag to define if the condition is taken or not.
        void setConditionTaken(bool flag);

        //! Everything which must be done before the IR processing.
        void preIRInit(void);

        //! Everything which must be done after the IR processing.
        void postIRInit(void);

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
