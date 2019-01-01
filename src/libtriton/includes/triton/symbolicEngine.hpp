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
#include <memory>
#include <string>
#include <unordered_map>

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
          std::unordered_map<triton::usize, SharedSymbolicVariable> symbolicVariables;

          /*! \brief The map of symbolic expressions
           *
           * \details
           * **item1**: symbolic reference id<br>
           * **item2**: symbolic expression
           */
          mutable std::unordered_map<triton::usize, WeakSymbolicExpression> symbolicExpressions;

          /*! \brief map of address -> symbolic expression
           *
           * \details
           * **item1**: memory address<br>
           * **item2**: shared symbolic expression
           */
          std::map<triton::uint64, SharedSymbolicExpression> memoryReference;

          /*! \brief map of <address:size> -> symbolic expression.
           *
           * \details
           * **item1**: <addr:size><br>
           * **item2**: shared symbolic expression
           */
          std::map<std::pair<triton::uint64, triton::uint32>, SharedSymbolicExpression> alignedMemoryReference;

          //! Symbolic register state.
          std::vector<SharedSymbolicExpression> symbolicReg;

        private:
          //! Reference to the context managing ast nodes.
          triton::ast::AstContext& astCtxt;

          //! Architecture API
          triton::arch::Architecture* architecture;

          //! Callbacks API
          triton::callbacks::Callbacks* callbacks;

          //! Modes API.
          triton::modes::Modes& modes;

          //! Returns an unique symbolic expression id.
          triton::usize getUniqueSymExprId(void);

          //! Returns an unique symbolic variable id.
          triton::usize getUniqueSymVarId(void);

          //! Gets an aligned entry.
          const SharedSymbolicExpression& getAlignedMemory(triton::uint64 address, triton::uint32 size);

          //! Adds an aligned entry.
          void addAlignedMemory(triton::uint64 address, triton::uint32 size, const SharedSymbolicExpression& expr);

          //! Checks if the aligned memory is recored.
          bool isAlignedMemory(triton::uint64 address, triton::uint32 size);

          //! Removes an aligned entry.
          void removeAlignedMemory(triton::uint64 address, triton::uint32 size);

          //! Adds a symbolic memory reference.
          void addMemoryReference(triton::uint64 mem, const SharedSymbolicExpression& expr);

          //! Returns the AST corresponding to the shift operation. Mainly used for AArch64 operands.
          triton::ast::SharedAbstractNode getShiftAst(triton::arch::aarch64::shift_e type, triton::uint32 value, const triton::ast::SharedAbstractNode& node);

          //! Returns the AST corresponding to the extend operation. Mainly used for AArch64 operands.
          triton::ast::SharedAbstractNode getExtendAst(triton::arch::aarch64::extend_e type, triton::uint32 size, const triton::ast::SharedAbstractNode& node);

          //! Slices all expressions from a given node.
          void sliceExpressions(const triton::ast::SharedAbstractNode& node, std::map<triton::usize, SharedSymbolicExpression>& exprs);

        public:
          //! Constructor.
          TRITON_EXPORT SymbolicEngine(triton::arch::Architecture* architecture,
                                       triton::modes::Modes& modes,
                                       triton::ast::AstContext& astCtxt,
                                       triton::callbacks::Callbacks* callbacks=nullptr);

          //! Constructor by copy.
          TRITON_EXPORT SymbolicEngine(const SymbolicEngine& other);

          //! Copies a SymbolicEngine.
          TRITON_EXPORT SymbolicEngine& operator=(const SymbolicEngine& other);

          //! Creates a new shared symbolic expression.
          TRITON_EXPORT SharedSymbolicExpression newSymbolicExpression(const triton::ast::SharedAbstractNode& node, triton::engines::symbolic::expression_e type, const std::string& comment="");

          //! Removes the symbolic expression corresponding to the id.
          TRITON_EXPORT void removeSymbolicExpression(triton::usize symExprId);

          //! Adds a symbolic variable.
          TRITON_EXPORT const SharedSymbolicVariable& newSymbolicVariable(triton::engines::symbolic::variable_e type, triton::uint64 source, triton::uint32 size, const std::string& comment="");

          //! Converts a symbolic expression to a symbolic variable. `symVarSize` must be in bits.
          TRITON_EXPORT const SharedSymbolicVariable& convertExpressionToSymbolicVariable(triton::usize exprId, triton::uint32 symVarSize, const std::string& symVarComment="");

          //! Converts a symbolic memory expression to a symbolic variable.
          TRITON_EXPORT const SharedSymbolicVariable& convertMemoryToSymbolicVariable(const triton::arch::MemoryAccess& mem, const std::string& symVarComment="");

          //! Converts a symbolic register expression to a symbolic variable.
          TRITON_EXPORT const SharedSymbolicVariable& convertRegisterToSymbolicVariable(const triton::arch::Register& reg, const std::string& symVarComment="");

          //! Returns the symbolic variable corresponding to the symbolic variable id.
          TRITON_EXPORT const SharedSymbolicVariable& getSymbolicVariableFromId(triton::usize symVarId) const;

          //! Returns the symbolic variable corresponding to the symbolic variable name.
          TRITON_EXPORT const SharedSymbolicVariable& getSymbolicVariableFromName(const std::string& symVarName) const;

          //! Returns the symbolic expression corresponding to an id.
          TRITON_EXPORT SharedSymbolicExpression getSymbolicExpressionFromId(triton::usize symExprId) const;

          //! Returns the shared symbolic expression corresponding to the memory address.
          TRITON_EXPORT SharedSymbolicExpression getSymbolicMemory(triton::uint64 addr) const;

          //! Returns the map (addr:expr) of all symbolic memory defined.
          TRITON_EXPORT const std::map<triton::uint64, SharedSymbolicExpression>& getSymbolicMemory(void) const;

          //! Returns the shared symbolic expression corresponding to the parent register.
          TRITON_EXPORT const SharedSymbolicExpression& getSymbolicRegister(const triton::arch::Register& reg) const;

          //! Returns the map of symbolic registers defined.
          TRITON_EXPORT std::map<triton::arch::register_e, SharedSymbolicExpression> getSymbolicRegisters(void) const;

          //! Returns the symbolic memory value.
          TRITON_EXPORT triton::uint8 getSymbolicMemoryValue(triton::uint64 address);

          //! Returns the symbolic memory value.
          TRITON_EXPORT triton::uint512 getSymbolicMemoryValue(const triton::arch::MemoryAccess& mem);

          //! Returns the symbolic values of a memory area.
          TRITON_EXPORT std::vector<triton::uint8> getSymbolicMemoryAreaValue(triton::uint64 baseAddr, triton::usize size);

          //! Returns the symbolic register value.
          TRITON_EXPORT triton::uint512 getSymbolicRegisterValue(const triton::arch::Register& reg);

          //! Returns the AST corresponding to the operand.
          TRITON_EXPORT triton::ast::SharedAbstractNode getOperandAst(const triton::arch::OperandWrapper& op);

          //! Returns the AST corresponding to the operand.
          TRITON_EXPORT triton::ast::SharedAbstractNode getOperandAst(triton::arch::Instruction& inst, const triton::arch::OperandWrapper& op);

          //! Returns the AST corresponding to the immediate.
          TRITON_EXPORT triton::ast::SharedAbstractNode getImmediateAst(const triton::arch::Immediate& imm);

          //! Returns the AST corresponding to the immediate and defines the immediate as input of the instruction.
          TRITON_EXPORT triton::ast::SharedAbstractNode getImmediateAst(triton::arch::Instruction& inst, const triton::arch::Immediate& imm);

          //! Returns the AST corresponding to the memory.
          TRITON_EXPORT triton::ast::SharedAbstractNode getMemoryAst(const triton::arch::MemoryAccess& mem);

          //! Returns the AST corresponding to the memory and defines the memory as input of the instruction.
          TRITON_EXPORT triton::ast::SharedAbstractNode getMemoryAst(triton::arch::Instruction& inst, const triton::arch::MemoryAccess& mem);

          //! Returns the AST corresponding to the register.
          TRITON_EXPORT triton::ast::SharedAbstractNode getRegisterAst(const triton::arch::Register& reg);

          //! Returns the AST corresponding to the register and defines the register as input of the instruction.
          TRITON_EXPORT triton::ast::SharedAbstractNode getRegisterAst(triton::arch::Instruction& inst, const triton::arch::Register& reg);

          //! Returns the new shared symbolic abstract expression and links this expression to the instruction.
          TRITON_EXPORT const SharedSymbolicExpression& createSymbolicExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const triton::arch::OperandWrapper& dst, const std::string& comment="");

          //! Returns the new shared symbolic memory expression expression and links this expression to the instruction.
          TRITON_EXPORT const SharedSymbolicExpression& createSymbolicMemoryExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const triton::arch::MemoryAccess& mem, const std::string& comment="");

          //! Returns the new shared symbolic register expression expression and links this expression to the instruction.
          TRITON_EXPORT const SharedSymbolicExpression& createSymbolicRegisterExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const triton::arch::Register& reg, const std::string& comment="");

          //! Returns the new shared symbolic flag expression expression and links this expression to the instruction.
          TRITON_EXPORT const SharedSymbolicExpression& createSymbolicFlagExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const triton::arch::Register& flag, const std::string& comment="");

          //! Returns the new shared symbolic volatile expression expression and links this expression to the instruction.
          TRITON_EXPORT const SharedSymbolicExpression& createSymbolicVolatileExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const std::string& comment="");

          //! Assigns a symbolic expression to a register.
          TRITON_EXPORT void assignSymbolicExpressionToRegister(const SharedSymbolicExpression& se, const triton::arch::Register& reg);

          //! Assigns a symbolic expression to a memory.
          TRITON_EXPORT void assignSymbolicExpressionToMemory(const SharedSymbolicExpression& se, const triton::arch::MemoryAccess& mem);

          //! Unrolls the SSA form of a given AST.
          TRITON_EXPORT triton::ast::SharedAbstractNode unrollAst(const triton::ast::SharedAbstractNode& node);

          //! Slices all expressions from a given one.
          TRITON_EXPORT std::map<triton::usize, SharedSymbolicExpression> sliceExpressions(const SharedSymbolicExpression& expr);

          //! Returns the list of the tainted symbolic expressions.
          TRITON_EXPORT std::list<SharedSymbolicExpression> getTaintedSymbolicExpressions(void) const;

          //! Returns all symbolic expressions.
          TRITON_EXPORT std::unordered_map<triton::usize, SharedSymbolicExpression> getSymbolicExpressions(void) const;

          //! Returns all symbolic variables.
          TRITON_EXPORT const std::unordered_map<triton::usize, SharedSymbolicVariable>& getSymbolicVariables(void) const;

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
          TRITON_EXPORT const triton::uint512& getConcreteVariableValue(const SharedSymbolicVariable& symVar) const;

          //! Sets the concrete value of a symbolic variable.
          TRITON_EXPORT void setConcreteVariableValue(const SharedSymbolicVariable& symVar, const triton::uint512& value);
      };

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SYMBOLICENGINE_H */
