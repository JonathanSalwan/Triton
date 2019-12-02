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
#include <set>
#include <sstream>
#include <utility>
#include <vector>

#include <triton/archEnums.hpp>
#include <triton/ast.hpp>
#include <triton/dllexport.hpp>
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

        //! The opcode of the instruction.
        triton::uint8 opcode[32];

        //! The size of the instruction.
        triton::uint32 size;

        //! The type of the instruction. This field is set at the disassembly level.
        triton::uint32 type;

        //! The prefix of the instruction. This field is set at the disassembly level. Mainly used for X86.
        triton::arch::x86::prefix_e prefix;

        //! The code condition of the instruction. This field is set at the disassembly level. Mainly used for AArch64.
        triton::arch::arm::condition_e codeCondition;

        //! Implicit and explicit load access (read). This field is set at the semantics level.
        std::set<std::pair<triton::arch::MemoryAccess, triton::ast::SharedAbstractNode>> loadAccess;

        //! Implicit and explicit store access (write). This field is set at the semantics level.
        std::set<std::pair<triton::arch::MemoryAccess, triton::ast::SharedAbstractNode>> storeAccess;

        //! Implicit and explicit register inputs (read). This field is set at the semantics level.
        std::set<std::pair<triton::arch::Register, triton::ast::SharedAbstractNode>> readRegisters;

        //! Implicit and explicit register outputs (write). This field is set at the semantics level.
        std::set<std::pair<triton::arch::Register, triton::ast::SharedAbstractNode>> writtenRegisters;

        //! Implicit and explicit immediate inputs (read). This field is set at the semantics level.
        std::set<std::pair<triton::arch::Immediate, triton::ast::SharedAbstractNode>> readImmediates;

        //! Implicit and explicit undefined registers. This field is set at the semantics level.
        std::set<triton::arch::Register> undefinedRegisters;

        //! True if this instruction is a branch. This field is set at the disassembly level.
        bool branch;

        //! True if this instruction changes the control flow. This field is set at the disassembly level.
        bool controlFlow;

        //! True if the condition is taken (i.g x86: jcc, cmocc, setcc, ...). This field is set at the semantics level.
        bool conditionTaken;

        //! True if this instruction is tainted. This field is set at the semantics level.
        bool tainted;

        //! True if this instruction performs a write back. Mainly used for AArch64 instruction like LDR.
        bool writeBack;

        //! True if this instruction updartes flags. Mainly used for AArch64 instruction like ADDS.
        bool updateFlag;

        //! True if this is a Thumb instruction.
        bool thumb;

    private:
        //! Copies an Instruction
        void copy(const Instruction& other);

      public:
        //! A list of operands
        std::vector<triton::arch::OperandWrapper> operands;

        //! The semantics set of the instruction.
        std::vector<triton::engines::symbolic::SharedSymbolicExpression> symbolicExpressions;

        //! Constructor.
        TRITON_EXPORT Instruction();

        //! Constructor with opcode.
        TRITON_EXPORT Instruction(const triton::uint8* opcode, triton::uint32 opSize);

        //! Constructor by copy.
        TRITON_EXPORT Instruction(const Instruction& other);

        //! Copies an Instruction.
        TRITON_EXPORT Instruction& operator=(const Instruction& other);

        //! Destructor.
        TRITON_EXPORT ~Instruction();

        //! Returns the thread id of the instruction.
        TRITON_EXPORT triton::uint32 getThreadId(void) const;

        //! Sets the thread id of the instruction.
        TRITON_EXPORT void setThreadId(triton::uint32 tid);

        //! Returns the address of the instruction.
        TRITON_EXPORT triton::uint64 getAddress(void) const;

        //! Returns the next address of the instruction.
        TRITON_EXPORT triton::uint64 getNextAddress(void) const;

        //! Sets the address of the instruction.
        TRITON_EXPORT void setAddress(triton::uint64 addr);

        //! Returns the disassembly of the instruction.
        TRITON_EXPORT std::string getDisassembly(void) const;

        //! Returns the opcode of the instruction.
        TRITON_EXPORT const triton::uint8* getOpcode(void) const;

        //! Returns the type of the instruction.
        TRITON_EXPORT triton::uint32 getType(void) const;

        //! Returns the prefix of the instruction (mainly for X86).
        TRITON_EXPORT triton::arch::x86::prefix_e getPrefix(void) const;

        //! Returns the code codition of the instruction (mainly for AArch64).
        TRITON_EXPORT triton::arch::arm::condition_e getCodeCondition(void) const;

        //! Returns the list of all implicit and explicit load access
        TRITON_EXPORT std::set<std::pair<triton::arch::MemoryAccess, triton::ast::SharedAbstractNode>>& getLoadAccess(void);

        //! Returns the list of all implicit and explicit store access
        TRITON_EXPORT std::set<std::pair<triton::arch::MemoryAccess, triton::ast::SharedAbstractNode>>& getStoreAccess(void);

        //! Returns the list of all implicit and explicit register (flags includes) inputs (read)
        TRITON_EXPORT std::set<std::pair<triton::arch::Register, triton::ast::SharedAbstractNode>>& getReadRegisters(void);

        //! Returns the list of all implicit and explicit register (flags includes) outputs (write)
        TRITON_EXPORT std::set<std::pair<triton::arch::Register, triton::ast::SharedAbstractNode>>& getWrittenRegisters(void);

        //! Returns the list of all implicit and explicit immediate inputs (read)
        TRITON_EXPORT std::set<std::pair<triton::arch::Immediate, triton::ast::SharedAbstractNode>>& getReadImmediates(void);

        //! Returns the list of all implicit and explicit undefined registers.
        TRITON_EXPORT std::set<triton::arch::Register>& getUndefinedRegisters(void);

        //! Sets the opcode of the instruction.
        TRITON_EXPORT void setOpcode(const triton::uint8* opcode, triton::uint32 size);

        //! Returns the size of the instruction.
        TRITON_EXPORT triton::uint32 getSize(void) const;

        //! Sets a load access.
        TRITON_EXPORT void setLoadAccess(const triton::arch::MemoryAccess& mem, const triton::ast::SharedAbstractNode& node);

        //! Removes a load access.
        TRITON_EXPORT void removeLoadAccess(const triton::arch::MemoryAccess& mem);

        //! Sets a store access.
        TRITON_EXPORT void setStoreAccess(const triton::arch::MemoryAccess& mem, const triton::ast::SharedAbstractNode& node);

        //! Removes a store access.
        TRITON_EXPORT void removeStoreAccess(const triton::arch::MemoryAccess& mem);

        //! Sets a read register.
        TRITON_EXPORT void setReadRegister(const triton::arch::Register& reg, const triton::ast::SharedAbstractNode& node);

        //! Removes a read register.
        TRITON_EXPORT void removeReadRegister(const triton::arch::Register& reg);

        //! Sets a written register.
        TRITON_EXPORT void setWrittenRegister(const triton::arch::Register& reg, const triton::ast::SharedAbstractNode& node);

        //! Removes a written register.
        TRITON_EXPORT void removeWrittenRegister(const triton::arch::Register& reg);

        //! Sets a read immediate.
        TRITON_EXPORT void setReadImmediate(const triton::arch::Immediate& imm, const triton::ast::SharedAbstractNode& node);

        //! Removes a read immediate.
        TRITON_EXPORT void removeReadImmediate(const triton::arch::Immediate& imm);

        //! Sets an undefined register.
        TRITON_EXPORT void setUndefinedRegister(const triton::arch::Register& reg);

        //! Removes an undefined register.
        TRITON_EXPORT void removeUndefinedRegister(const triton::arch::Register& reg);

        //! Sets the size of the instruction.
        TRITON_EXPORT void setSize(triton::uint32 size);

        //! Sets the type of the instruction.
        TRITON_EXPORT void setType(triton::uint32 type);

        //! Sets the prefix of the instruction (mainly for X86).
        TRITON_EXPORT void setPrefix(triton::arch::x86::prefix_e prefix);

        //! Sets the code condition of the instruction (mainly for AArch64).
        TRITON_EXPORT void setCodeCondition(triton::arch::arm::condition_e codeCondition);

        //! Sets the disassembly of the instruction.
        TRITON_EXPORT void setDisassembly(const std::string& str);

        //! Sets the taint of the instruction.
        TRITON_EXPORT void setTaint(bool state);

        //! Sets the taint of the instruction based on its expressions.
        TRITON_EXPORT void setTaint(void);

        //! Sets the writeBack flag of the instruction.
        TRITON_EXPORT void setWriteBack(bool state);

        //! Sets the updateFlag of the instruction.
        TRITON_EXPORT void setUpdateFlag(bool state);

        //! Sets the Thumb mode of the instruction.
        TRITON_EXPORT void setThumb(bool state);

        //! Adds a symbolic expression
        TRITON_EXPORT const triton::engines::symbolic::SharedSymbolicExpression& addSymbolicExpression(const triton::engines::symbolic::SharedSymbolicExpression& expr);

        //! Returns true if this instruction is a branch
        TRITON_EXPORT bool isBranch(void) const;

        //! Returns true if this instruction changes the control flow (e.g x86: JMP, JCC, CALL, RET, ...)
        TRITON_EXPORT bool isControlFlow(void) const;

        //! Returns true if the condition is taken (e.g x86: jcc, cmovcc, setcc, ...).
        TRITON_EXPORT bool isConditionTaken(void) const;

        //! Returns true if at least one of its expressions is tainted.
        TRITON_EXPORT bool isTainted(void) const;

        //! Returns true if at least one of its expressions contains a symbolic variable.
        TRITON_EXPORT bool isSymbolized(void) const;

        //! Returns true if the instruction contains an expression which reads the memory.
        TRITON_EXPORT bool isMemoryRead(void) const;

        //! Returns true if the instruction contains an expression which writes into the memory.
        TRITON_EXPORT bool isMemoryWrite(void) const;

        //! Returns whether the instruction writes the specified operand.
        TRITON_EXPORT bool isWriteTo(const triton::arch::OperandWrapper& target) const;

        //! Returns whether the instruction reads the specified operand.
        TRITON_EXPORT bool isReadFrom(const triton::arch::OperandWrapper& target) const;

        //! Returns true if the instruction has a prefix (mainly for X86).
        TRITON_EXPORT bool isPrefixed(void) const;

        //! Returns true if the instruction performs a write back. Mainly used for AArch64 instructions like LDR.
        TRITON_EXPORT bool isWriteBack(void) const;

        //! Returns true if the instruction updates flags. Mainly used for AArch64 instructions like ADDS.
        TRITON_EXPORT bool isUpdateFlag(void) const;

        //! Returns true if it is a Thumb instruction.
        TRITON_EXPORT bool isThumb(void) const;

        //! Sets flag to define this instruction as branch or not.
        TRITON_EXPORT void setBranch(bool flag);

        //! Sets flag to define this instruction changes the control flow or not.
        TRITON_EXPORT void setControlFlow(bool flag);

        //! Sets flag to define if the condition is taken or not.
        TRITON_EXPORT void setConditionTaken(bool flag);

        //! Clears all instruction information.
        TRITON_EXPORT void clear(void);
    };

    //! Displays an Instruction.
    TRITON_EXPORT std::ostream& operator<<(std::ostream& stream, const Instruction& inst);

    //! Displays an Instruction.
    TRITON_EXPORT std::ostream& operator<<(std::ostream& stream, const Instruction* inst);

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_INSTRUCTION_H */
