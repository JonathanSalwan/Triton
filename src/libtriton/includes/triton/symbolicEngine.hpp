//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_SYMBOLICENGINE_H
#define TRITON_SYMBOLICENGINE_H

#include <list>
#include <unordered_map>
#include <map>
#include <string>

#include <triton/architecture.hpp>
#include <tritonast/nodes.hpp>
#include <triton/callbacks.hpp>
#include <triton/memoryAccess.hpp>
#include <triton/modes.hpp>
#include <triton/pathManager.hpp>
#include <triton/register.hpp>
#include <triton/symbolicEnums.hpp>
#include <triton/symbolicExpression.hpp>
#include <triton/symbolicSimplification.hpp>
#include <triton/symbolicVariable.hpp>
#include <tritoncore/types.hpp>



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
          triton::AstContext& astCtxt;

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
          std::unordered_map<triton::usize, SymbolicVariable*> symbolicVariables;

          /*! \brief The map of symbolic expressions
           *
           * \details
           * **item1**: symbolic reference id<br>
           * **item2**: symbolic expression
           */
          // It is a cache of existing symExpr
          // FIXME: When should we clean it?
          mutable std::unordered_map<triton::usize, std::weak_ptr<SymbolicExpression>> symbolicExpressions;

          /*! \brief map of address -> symbolic expression
           *
           * \details
           * **item1**: memory address<br>
           * **item2**: symbolic reference id
           */
          std::map<triton::uint64, triton::SharedSymbolicExpression> memoryReference;

          /*! \brief map of <address:size> -> symbolic expression.
           *
           * \details
           * **item1**: <addr:size><br>
           * **item2**: AST node
           */
          std::map<std::pair<triton::uint64, triton::uint32>, triton::SharedSymbolicExpression> alignedMemoryReference;

          //! Symbolic register state.
          std::vector<triton::SharedSymbolicExpression> symbolicReg;

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
          void sliceExpressions(triton::ast::AbstractNode* node, std::map<triton::usize, triton::SharedSymbolicExpression>& exprs);

        public:
          //! Constructor. If you use this class as backup or copy you should define the `isBackup` flag as true.
          SymbolicEngine(triton::arch::Architecture* architecture,
                         const triton::modes::Modes& modes,
                         triton::AstContext& astCtxt,
                         triton::callbacks::Callbacks* callbacks=nullptr,
                         bool isBackup=false);

          //! Constructor by copy.
          SymbolicEngine(const SymbolicEngine& copy);

          //! Destructor.
          ~SymbolicEngine();

          //! Copies and initializes a SymbolicEngine.
          void copy(const SymbolicEngine& other);

          //! Copies a SymbolicEngine.
          void operator=(const SymbolicEngine& other);

          //! Creates a new symbolic expression.
          triton::SharedSymbolicExpression newSymbolicExpression(triton::ast::SharedAbstractNode const& node, symkind_e kind, const std::string& comment="");

          //! Removes the symbolic expression corresponding to the id.
          void removeSymbolicExpression(triton::usize symExprId);

          //! Adds an aligned entry.
          void addAlignedMemory(triton::uint64 address, triton::uint32 size, triton::SharedSymbolicExpression const& expr);

          //! Gets an aligned entry.
          triton::SharedSymbolicExpression const& getAlignedMemory(triton::uint64 address, triton::uint32 size);

          //! Checks if the aligned memory is recored.
          bool isAlignedMemory(triton::uint64 address, triton::uint32 size);

          //! Removes an aligned entry.
          void removeAlignedMemory(triton::uint64 address, triton::uint32 size);

          //! Adds a symbolic variable.
          SymbolicVariable* newSymbolicVariable(symkind_e kind, triton::uint64 kindValue, triton::uint32 size, const std::string& comment="");

          //! Converts a symbolic expression to a symbolic variable. `symVarSize` must be in bits.
          SymbolicVariable* convertExpressionToSymbolicVariable(triton::usize exprId, triton::uint32 symVarSize, const std::string& symVarComment="");

          //! Converts a symbolic memory expression to a symbolic variable.
          SymbolicVariable* convertMemoryToSymbolicVariable(const triton::arch::MemoryAccess& mem, const std::string& symVarComment="");

          //! Converts a symbolic register expression to a symbolic variable.
          SymbolicVariable* convertRegisterToSymbolicVariable(const triton::arch::Register& reg, const std::string& symVarComment="");

          //! Returns the symbolic variable corresponding to the symbolic variable id.
          SymbolicVariable* getSymbolicVariableFromId(triton::usize symVarId) const;

          //! Returns the symbolic variable corresponding to the symbolic variable name.
          SymbolicVariable* getSymbolicVariableFromName(const std::string& symVarName) const;

          //! Returns the symbolic expression id corresponding to the memory address.
          triton::SharedSymbolicExpression getSymbolicMemory(triton::uint64 addr) const;

          //! Returns the map (addr:expr) of all symbolic memory defined.
          std::map<triton::uint64, triton::SharedSymbolicExpression> const& getSymbolicMemory(void) const;

          //! Returns the symbolic expression corresponding to an id.
          triton::SharedSymbolicExpression getSymbolicExpressionFromId(triton::usize symExprId) const;

          //! Returns the map of symbolic registers defined.
          std::map<triton::arch::registers_e, triton::SharedSymbolicExpression> getSymbolicRegisters(void) const;

          //! Returns the symbolic expression id corresponding to the register.
          triton::SharedSymbolicExpression const& getSymbolicRegister(const triton::arch::Register& reg) const;

          //! Returns the symbolic memory value.
          triton::uint8 getSymbolicMemoryValue(triton::uint64 address);

          //! Returns the symbolic memory value.
          triton::uint512 getSymbolicMemoryValue(const triton::arch::MemoryAccess& mem);

          //! Returns the symbolic values of a memory area.
          std::vector<triton::uint8> getSymbolicMemoryAreaValue(triton::uint64 baseAddr, triton::usize size);

          //! Returns the symbolic register value.
          triton::uint512 getSymbolicRegisterValue(const triton::arch::Register& reg);

          //! Returns a symbolic operand based on the abstract wrapper.
          triton::ast::SharedAbstractNode getAstOperand(const triton::arch::OperandWrapper& op);

          //! Returns a symbolic operand based on the abstract wrapper.
          triton::ast::SharedAbstractNode const& getAstOperand(triton::arch::Instruction& inst, const triton::arch::OperandWrapper& op);

          //! Returns a symbolic immediate.
          triton::ast::SharedAbstractNode getAstImmediate(const triton::arch::Immediate& imm);

          //! Returns a symbolic immediate and defines the immediate as input of the instruction.
          triton::ast::SharedAbstractNode const& getAstImmediate(triton::arch::Instruction& inst, const triton::arch::Immediate& imm);

          //! Returns a symbolic memory.
          triton::ast::SharedAbstractNode getAstMemory(const triton::arch::MemoryAccess& mem);

          //! Returns a symbolic memory and defines the memory as input of the instruction.
          triton::ast::SharedAbstractNode const& getAstMemory(triton::arch::Instruction& inst, const triton::arch::MemoryAccess& mem);

          //! Returns a symbolic register.
          triton::ast::SharedAbstractNode getAstRegister(const triton::arch::Register& reg);

          //! Returns a symbolic register and defines the register as input of the instruction.
          triton::ast::SharedAbstractNode const& getAstRegister(triton::arch::Instruction& inst, const triton::arch::Register& reg);

          //! Returns the new symbolic abstract expression and links this expression to the instruction.
          triton::SharedSymbolicExpression const& createSymbolicExpression(triton::arch::Instruction& inst, triton::ast::SharedAbstractNode const& node, const triton::arch::OperandWrapper& dst, const std::string& comment="");

          //! Returns the new symbolic memory expression expression and links this expression to the instruction.
          triton::SharedSymbolicExpression const& createSymbolicMemoryExpression(triton::arch::Instruction& inst, triton::ast::SharedAbstractNode const& node, const triton::arch::MemoryAccess& mem, const std::string& comment="");

          //! Returns the new symbolic register expression expression and links this expression to the instruction.
          triton::SharedSymbolicExpression const& createSymbolicRegisterExpression(triton::arch::Instruction& inst, triton::ast::SharedAbstractNode const& node, const triton::arch::Register& reg, const std::string& comment="");

          //! Returns the new symbolic flag expression expression and links this expression to the instruction.
          triton::SharedSymbolicExpression const& createSymbolicFlagExpression(triton::arch::Instruction& inst, triton::ast::SharedAbstractNode const& node, const triton::arch::Register& flag, const std::string& comment="");

          //! Returns the new symbolic volatile expression expression and links this expression to the instruction.
          triton::SharedSymbolicExpression const& createSymbolicVolatileExpression(triton::arch::Instruction& inst, triton::ast::SharedAbstractNode const& node, const std::string& comment="");

          //! Returns an unique symbolic expression id.
          triton::usize getUniqueSymExprId(void);

          //! Returns an unique symbolic variable id.
          triton::usize getUniqueSymVarId(void);

          //! Assigns a symbolic expression to a register.
          triton::SharedSymbolicExpression const& assignSymbolicExpressionToRegister(triton::SharedSymbolicExpression const& se, const triton::arch::Register& reg);

          //! Assigns a symbolic expression to a memory.
          void assignSymbolicExpressionToMemory(triton::SharedSymbolicExpression const& se, const triton::arch::MemoryAccess& mem);

          //! Unrolls the SSA form of a given AST.
          triton::ast::SharedAbstractNode unrollAst(triton::ast::SharedAbstractNode node);

          //! Slices all expressions from a given one.
          std::map<triton::usize, triton::SharedSymbolicExpression> sliceExpressions(triton::SharedSymbolicExpression const& expr);

          //! Returns the list of the tainted symbolic expressions.
          std::list<triton::SharedSymbolicExpression> getTaintedSymbolicExpressions(void) const;

          //! Returns all symbolic expressions.
          std::unordered_map<triton::usize, triton::SharedSymbolicExpression> getSymbolicExpressions(void) const;

          //! Returns all symbolic variables.
          const std::unordered_map<triton::usize, SymbolicVariable*>& getSymbolicVariables(void) const;

          //! Adds a symbolic memory reference.
          void addMemoryReference(triton::uint64 mem, triton::SharedSymbolicExpression const& expr);

          //! Concretizes all symbolic memory references.
          void concretizeAllMemory(void);

          //! Concretizes all symbolic register references.
          void concretizeAllRegister(void);

          //! Concretizes a specific symbolic memory reference.
          void concretizeMemory(const triton::arch::MemoryAccess& mem);

          //! Concretizes a specific symbolic memory reference.
          void concretizeMemory(triton::uint64 addr);

          //! Concretizes a specific symbolic register reference.
          void concretizeRegister(const triton::arch::Register& reg);

          //! Enables or disables the symbolic execution engine.
          void enable(bool flag);

          //! Returns true if the symbolic execution engine is enabled.
          bool isEnabled(void) const;

          //! Returns true if the symbolic expression ID exists.
          bool isSymbolicExpressionIdExists(triton::usize symExprId) const;

          //! Returns true if memory cell expressions contain symbolic variables.
          bool isMemorySymbolized(const triton::arch::MemoryAccess& mem) const;

          //! Returns true if memory cell expressions contain symbolic variables.
          bool isMemorySymbolized(triton::uint64 addr, triton::uint32 size=1) const;

          //! Returns true if the register expression contains a symbolic variable.
          bool isRegisterSymbolized(const triton::arch::Register& reg) const;

          //! Initializes the memory access AST (LOAD and STORE).
          void initLeaAst(triton::arch::MemoryAccess& mem, bool force=false);

          //! Gets the concrete value of a symbolic variable.
          const triton::uint512& getConcreteSymbolicVariableValue(const SymbolicVariable& symVar) const;

          //! Sets the concrete value of a symbolic variable.
          void setConcreteSymbolicVariableValue(const SymbolicVariable& symVar, const triton::uint512& value);
      };

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SYMBOLICENGINE_H */

