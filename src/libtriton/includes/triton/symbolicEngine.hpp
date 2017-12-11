//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_SYMBOLICENGINE_H
#define TRITON_SYMBOLICENGINE_H

#include <list>
#include <map>
#include <string>

#include <triton/architecture.hpp>
#include <triton/ast.hpp>
#include <triton/callbacks.hpp>
#include <triton/dllexport.hpp>
#include <triton/memoryAccess.hpp>
#include <triton/modes.hpp>
#include <triton/pathManager.hpp>
#include <triton/register.hpp>
#include <triton/symbolicEnums.hpp>
#include <triton/symbolicExpression.hpp>
#include <triton/symbolicSimplification.hpp>
#include <triton/symbolicVariable.hpp>
#include <triton/tritonTypes.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Engines namespace
  namespace engines {
  /*!
   *  \ingroup triton
   *  \addtogroup engines
   *  @{
   */

    //! The Symbolic Execution namespace
    namespace symbolic {
    /*!
     *  \ingroup engines
     *  \addtogroup symbolic
     *  @{
     */

      //! \class SymbolicEngine
      /*! \brief The symbolic engine class. */
      class SymbolicEngine
        : public triton::engines::symbolic::SymbolicSimplification,
          public triton::engines::symbolic::PathManager {

        protected:
          //! Reference to the context managing ast nodes.
          triton::ast::AstContext& astCtxt;

          //! Defines if the engine is enable or disable.
          bool enableFlag;

          //! Number of registers
          triton::uint32 numberOfRegisters;

          //! Symbolic expressions id.
          triton::usize uniqueSymExprId;

          //! Symbolic variables id.
          triton::usize uniqueSymVarId;

          /*! \brief The map of symbolic variables
           *
           * \details
           * **item1**: variable id<br>
           * **item2**: symbolic variable
           */
          std::map<triton::usize, SymbolicVariable*> symbolicVariables;

          /*! \brief The map of symbolic expressions
           *
           * \details
           * **item1**: symbolic reference id<br>
           * **item2**: symbolic expression
           */
          std::map<triton::usize, SymbolicExpression*> symbolicExpressions;

          /*! \brief map of address -> symbolic expression
           *
           * \details
           * **item1**: memory address<br>
           * **item2**: symbolic reference id
           */
          std::map<triton::uint64, triton::usize> memoryReference;

          /*! \brief map of <address:size> -> symbolic expression.
           *
           * \details
           * **item1**: <addr:size><br>
           * **item2**: AST node
           */
          std::map<std::pair<triton::uint64, triton::uint32>, triton::ast::AbstractNode*> alignedMemoryReference;

        private:
          //! Architecture API
          triton::arch::Architecture* architecture;

          //! Callbacks API
          triton::callbacks::Callbacks* callbacks;

          //! Modes API.
          const triton::modes::Modes& modes;

          //! Defines if this instance is used as a backup.
          bool backupFlag;

          //! Slices all expressions from a given node.
          void sliceExpressions(triton::ast::AbstractNode* node, std::map<triton::usize, SymbolicExpression*>& exprs);

          //! Copies and initializes a SymbolicEngine.
          void copy(const SymbolicEngine& other);

        public:
          //! Symbolic register state.
          triton::usize* symbolicReg;

          //! Constructor. If you use this class as backup or copy you should define the `isBackup` flag as true.
          TRITON_EXPORT SymbolicEngine(triton::arch::Architecture* architecture,
                                       const triton::modes::Modes& modes,
                                       triton::ast::AstContext& astCtxt,
                                       triton::callbacks::Callbacks* callbacks=nullptr,
                                       bool isBackup=false);

          //! Constructor by copy.
          TRITON_EXPORT SymbolicEngine(const SymbolicEngine& other);

          //! Destructor.
          TRITON_EXPORT ~SymbolicEngine();

          //! Copies a SymbolicEngine.
          TRITON_EXPORT SymbolicEngine& operator=(const SymbolicEngine& other);

          //! Creates a new symbolic expression.
          TRITON_EXPORT SymbolicExpression* newSymbolicExpression(triton::ast::AbstractNode* node, symkind_e kind, const std::string& comment="");

          //! Removes the symbolic expression corresponding to the id.
          TRITON_EXPORT void removeSymbolicExpression(triton::usize symExprId);

          //! Adds an aligned entry.
          TRITON_EXPORT void addAlignedMemory(triton::uint64 address, triton::uint32 size, triton::ast::AbstractNode* node);

          //! Gets an aligned entry.
          TRITON_EXPORT triton::ast::AbstractNode* getAlignedMemory(triton::uint64 address, triton::uint32 size);

          //! Checks if the aligned memory is recored.
          TRITON_EXPORT bool isAlignedMemory(triton::uint64 address, triton::uint32 size);

          //! Removes an aligned entry.
          TRITON_EXPORT void removeAlignedMemory(triton::uint64 address, triton::uint32 size);

          //! Adds a symbolic variable.
          TRITON_EXPORT SymbolicVariable* newSymbolicVariable(symkind_e kind, triton::uint64 kindValue, triton::uint32 size, const std::string& comment="");

          //! Converts a symbolic expression to a symbolic variable. `symVarSize` must be in bits.
          TRITON_EXPORT SymbolicVariable* convertExpressionToSymbolicVariable(triton::usize exprId, triton::uint32 symVarSize, const std::string& symVarComment="");

          //! Converts a symbolic memory expression to a symbolic variable.
          TRITON_EXPORT SymbolicVariable* convertMemoryToSymbolicVariable(const triton::arch::MemoryAccess& mem, const std::string& symVarComment="");

          //! Converts a symbolic register expression to a symbolic variable.
          TRITON_EXPORT SymbolicVariable* convertRegisterToSymbolicVariable(const triton::arch::Register& reg, const std::string& symVarComment="");

          //! Returns the symbolic variable corresponding to the symbolic variable id.
          TRITON_EXPORT SymbolicVariable* getSymbolicVariableFromId(triton::usize symVarId) const;

          //! Returns the symbolic variable corresponding to the symbolic variable name.
          TRITON_EXPORT SymbolicVariable* getSymbolicVariableFromName(const std::string& symVarName) const;

          //! Returns the symbolic expression id corresponding to the memory address.
          TRITON_EXPORT triton::usize getSymbolicMemoryId(triton::uint64 addr) const;

          //! Returns the symbolic expression corresponding to an id.
          TRITON_EXPORT SymbolicExpression* getSymbolicExpressionFromId(triton::usize symExprId) const;

          //! Returns the map of symbolic registers defined.
          TRITON_EXPORT std::map<triton::arch::registers_e, SymbolicExpression*> getSymbolicRegisters(void) const;

          //! Returns the map (addr:expr) of all symbolic memory defined.
          TRITON_EXPORT std::map<triton::uint64, SymbolicExpression*> getSymbolicMemory(void) const;

          //! Returns the symbolic expression id corresponding to the register.
          TRITON_EXPORT triton::usize getSymbolicRegisterId(const triton::arch::Register& reg) const;

          //! Returns the symbolic memory value.
          TRITON_EXPORT triton::uint8 getSymbolicMemoryValue(triton::uint64 address);

          //! Returns the symbolic memory value.
          TRITON_EXPORT triton::uint512 getSymbolicMemoryValue(const triton::arch::MemoryAccess& mem);

          //! Returns the symbolic values of a memory area.
          TRITON_EXPORT std::vector<triton::uint8> getSymbolicMemoryAreaValue(triton::uint64 baseAddr, triton::usize size);

          //! Returns the symbolic register value.
          TRITON_EXPORT triton::uint512 getSymbolicRegisterValue(const triton::arch::Register& reg);

          //! Returns a symbolic operand based on the abstract wrapper.
          TRITON_EXPORT triton::ast::AbstractNode* buildSymbolicOperand(const triton::arch::OperandWrapper& op);

          //! Returns a symbolic operand based on the abstract wrapper.
          TRITON_EXPORT triton::ast::AbstractNode* buildSymbolicOperand(triton::arch::Instruction& inst, const triton::arch::OperandWrapper& op);

          //! Returns a symbolic immediate.
          TRITON_EXPORT triton::ast::AbstractNode* buildSymbolicImmediate(const triton::arch::Immediate& imm);

          //! Returns a symbolic immediate and defines the immediate as input of the instruction.
          TRITON_EXPORT triton::ast::AbstractNode* buildSymbolicImmediate(triton::arch::Instruction& inst, const triton::arch::Immediate& imm);

          //! Returns a symbolic memory.
          TRITON_EXPORT triton::ast::AbstractNode* buildSymbolicMemory(const triton::arch::MemoryAccess& mem);

          //! Returns a symbolic memory and defines the memory as input of the instruction.
          TRITON_EXPORT triton::ast::AbstractNode* buildSymbolicMemory(triton::arch::Instruction& inst, const triton::arch::MemoryAccess& mem);

          //! Returns a symbolic register.
          TRITON_EXPORT triton::ast::AbstractNode* buildSymbolicRegister(const triton::arch::Register& reg);

          //! Returns a symbolic register and defines the register as input of the instruction.
          TRITON_EXPORT triton::ast::AbstractNode* buildSymbolicRegister(triton::arch::Instruction& inst, const triton::arch::Register& reg);

          //! Returns the new symbolic abstract expression and links this expression to the instruction.
          TRITON_EXPORT SymbolicExpression* createSymbolicExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, const triton::arch::OperandWrapper& dst, const std::string& comment="");

          //! Returns the new symbolic memory expression expression and links this expression to the instruction.
          TRITON_EXPORT SymbolicExpression* createSymbolicMemoryExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, const triton::arch::MemoryAccess& mem, const std::string& comment="");

          //! Returns the new symbolic register expression expression and links this expression to the instruction.
          TRITON_EXPORT SymbolicExpression* createSymbolicRegisterExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, const triton::arch::Register& reg, const std::string& comment="");

          //! Returns the new symbolic flag expression expression and links this expression to the instruction.
          TRITON_EXPORT SymbolicExpression* createSymbolicFlagExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, const triton::arch::Register& flag, const std::string& comment="");

          //! Returns the new symbolic volatile expression expression and links this expression to the instruction.
          TRITON_EXPORT SymbolicExpression* createSymbolicVolatileExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, const std::string& comment="");

          //! Returns an unique symbolic expression id.
          TRITON_EXPORT triton::usize getUniqueSymExprId(void);

          //! Returns an unique symbolic variable id.
          TRITON_EXPORT triton::usize getUniqueSymVarId(void);

          //! Assigns a symbolic expression to a register.
          TRITON_EXPORT void assignSymbolicExpressionToRegister(SymbolicExpression *se, const triton::arch::Register& reg);

          //! Assigns a symbolic expression to a memory.
          TRITON_EXPORT void assignSymbolicExpressionToMemory(SymbolicExpression *se, const triton::arch::MemoryAccess& mem);

          //! Unrolls the SSA form of a given AST.
          TRITON_EXPORT triton::ast::AbstractNode* unrollAst(triton::ast::AbstractNode* node);

          //! Slices all expressions from a given one.
          TRITON_EXPORT std::map<triton::usize, SymbolicExpression*> sliceExpressions(SymbolicExpression* expr);

          //! Returns the list of the tainted symbolic expressions.
          TRITON_EXPORT std::list<SymbolicExpression*> getTaintedSymbolicExpressions(void) const;

          //! Returns all symbolic expressions.
          TRITON_EXPORT const std::map<triton::usize, SymbolicExpression*>& getSymbolicExpressions(void) const;

          //! Returns all symbolic variables.
          TRITON_EXPORT const std::map<triton::usize, SymbolicVariable*>& getSymbolicVariables(void) const;

          //! Adds a symbolic memory reference.
          TRITON_EXPORT void addMemoryReference(triton::uint64 mem, triton::usize id);

          //! Concretizes all symbolic memory references.
          TRITON_EXPORT void concretizeAllMemory(void);

          //! Concretizes all symbolic register references.
          TRITON_EXPORT void concretizeAllRegister(void);

          //! Concretizes a specific symbolic memory reference.
          TRITON_EXPORT void concretizeMemory(const triton::arch::MemoryAccess& mem);

          //! Concretizes a specific symbolic memory reference.
          TRITON_EXPORT void concretizeMemory(triton::uint64 addr);

          //! Concretizes a specific symbolic register reference.
          TRITON_EXPORT void concretizeRegister(const triton::arch::Register& reg);

          //! Enables or disables the symbolic execution engine.
          TRITON_EXPORT void enable(bool flag);

          //! Returns true if the symbolic execution engine is enabled.
          TRITON_EXPORT bool isEnabled(void) const;

          //! Returns true if the symbolic expression ID exists.
          TRITON_EXPORT bool isSymbolicExpressionIdExists(triton::usize symExprId) const;

          //! Returns true if memory cell expressions contain symbolic variables.
          TRITON_EXPORT bool isMemorySymbolized(const triton::arch::MemoryAccess& mem) const;

          //! Returns true if memory cell expressions contain symbolic variables.
          TRITON_EXPORT bool isMemorySymbolized(triton::uint64 addr, triton::uint32 size=1) const;

          //! Returns true if the register expression contains a symbolic variable.
          TRITON_EXPORT bool isRegisterSymbolized(const triton::arch::Register& reg) const;

          //! Initializes the memory access AST (LOAD and STORE).
          TRITON_EXPORT void initLeaAst(triton::arch::MemoryAccess& mem, bool force=false);

          //! Gets the concrete value of a symbolic variable.
          TRITON_EXPORT const triton::uint512& getConcreteSymbolicVariableValue(const SymbolicVariable& symVar) const;

          //! Sets the concrete value of a symbolic variable.
          TRITON_EXPORT void setConcreteSymbolicVariableValue(const SymbolicVariable& symVar, const triton::uint512& value);
      };

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SYMBOLICENGINE_H */

