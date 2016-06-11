//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_SYMBOLICENGINE_H
#define TRITON_SYMBOLICENGINE_H

#include <list>
#include <map>
#include <string>

#include "ast.hpp"
#include "astDictionaries.hpp"
#include "memoryOperand.hpp"
#include "pathManager.hpp"
#include "registerOperand.hpp"
#include "symbolicEnums.hpp"
#include "symbolicExpression.hpp"
#include "symbolicOptimization.hpp"
#include "symbolicSimplification.hpp"
#include "symbolicVariable.hpp"
#include "tritonTypes.hpp"



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The Engines namespace
  namespace engines {
  /*!
   *  \ingroup triton
   *  \addtogroup engines
   *  @{
   */

    //! \module The Symbolic Execution namespace
    namespace symbolic {
    /*!
     *  \ingroup engines
     *  \addtogroup symbolic
     *  @{
     */

      //! \class SymbolicEngine
      /*! \brief The symbolic engine class. */
      class SymbolicEngine
        : public triton::ast::AstDictionaries,
          public triton::engines::symbolic::SymbolicOptimization,
          public triton::engines::symbolic::SymbolicSimplification,
          public triton::engines::symbolic::PathManager {

        protected:

          //! Enable / Disable flag.
          bool enableFlag;

          /*! \brief Defines if we use a symbolic emulation.
           *
           * \description
           * **true**: full symbolic execution (emulation).
           * **false**: concolic execution.
           */
          bool emulationFlag;

          //! Number of registers
          triton::uint32 numberOfRegisters;

          //! Symbolic expressions id.
          triton::__uint uniqueSymExprId;

          //! Symbolic variables id.
          triton::__uint uniqueSymVarId;

          /*! \brief The map of symbolic variables
           *
           * \description
           * **item1**: variable id<br>
           * **item2**: symbolic variable
           */
          std::map<triton::__uint, SymbolicVariable*> symbolicVariables;

          /*! \brief The map of symbolic expressions
           *
           * \description
           * **item1**: symbolic reference id<br>
           * **item2**: symbolic expression
           */
          std::map<triton::__uint, SymbolicExpression*> symbolicExpressions;

          /*! \brief map of address -> symbolic expression
           *
           * \description
           * **item1**: memory address<br>
           * **item2**: symbolic reference id
           */
          std::map<triton::__uint, triton::__uint> memoryReference;

          /*! \brief map of <address:size> -> symbolic expression.
           *
           * \description
           * **item1**: <addr:size><br>
           * **item2**: symbolic reference id
           */
          std::map<std::pair<triton::__uint, triton::uint32>, triton::ast::AbstractNode*> alignedMemoryReference;

        public:

          //! Symbolic register state.
          triton::__uint* symbolicReg;

          //! Creates a new symbolic expression.
          SymbolicExpression* newSymbolicExpression(triton::ast::AbstractNode* node, symkind_e kind, const std::string& comment="");

          //! Removes the symbolic expression corresponding to the id.
          void removeSymbolicExpression(triton::__uint symExprId);

          //! Removes aligned entry.
          void removeAlignedMemory(triton::__uint addr);

          //! Adds a symbolic variable.
          SymbolicVariable* newSymbolicVariable(symkind_e kind, triton::__uint kindValue, triton::uint32 size, const std::string& comment="");

          //! Converts a symbolic expression to a symbolic variable. `symVarSize` must be in bits.
          SymbolicVariable* convertExpressionToSymbolicVariable(triton::__uint exprId, triton::uint32 symVarSize, const std::string& symVarComment="");

          //! Converts a symbolic memory expression to a symbolic variable.
          SymbolicVariable* convertMemoryToSymbolicVariable(const triton::arch::MemoryOperand& mem, const std::string& symVarComment="");

          //! Converts a symbolic register expression to a symbolic variable.
          SymbolicVariable* convertRegisterToSymbolicVariable(const triton::arch::RegisterOperand& reg, const std::string& symVarComment="");

          //! Returns the symbolic variable corresponding to the symbolic variable id.
          SymbolicVariable* getSymbolicVariableFromId(triton::__uint symVarId) const;

          //! Returns the symbolic variable corresponding to the symbolic variable name.
          SymbolicVariable* getSymbolicVariableFromName(const std::string& symVarName) const;

          //! Returns the symbolic expression id corresponding to the memory address.
          triton::__uint getSymbolicMemoryId(triton::__uint addr) const;

          //! Returns the symbolic expression corresponding to the id.
          SymbolicExpression* getSymbolicExpressionFromId(triton::__uint symExprId) const;

          //! Returns the map of symbolic registers defined.
          std::map<triton::arch::RegisterOperand, SymbolicExpression*> getSymbolicRegisters(void) const;

          //! Returns the map of symbolic memory defined.
          std::map<triton::__uint, SymbolicExpression*> getSymbolicMemory(void) const;

          //! Returns the symbolic expression id corresponding to the register.
          triton::__uint getSymbolicRegisterId(const triton::arch::RegisterOperand& reg) const;

          //! Returns the symbolic memory value.
          triton::uint8 getSymbolicMemoryValue(triton::__uint address);

          //! Returns the symbolic memory value.
          triton::uint512 getSymbolicMemoryValue(const triton::arch::MemoryOperand& mem);

          //! Returns the symbolic values of a memory area.
          std::vector<triton::uint8> getSymbolicMemoryAreaValue(triton::__uint baseAddr, triton::uint32 size);

          //! Returns the symbolic register value.
          triton::uint512 getSymbolicRegisterValue(const triton::arch::RegisterOperand& reg);

          //! Returns an immediate symbolic operand.
          triton::ast::AbstractNode* buildSymbolicImmediateOperand(const triton::arch::ImmediateOperand& imm);

          //! Returns an immediate symbolic operand and defines the immediate as input of the instruction.
          triton::ast::AbstractNode* buildSymbolicImmediateOperand(triton::arch::Instruction& inst, triton::arch::ImmediateOperand& imm);

          //! Returns a symbolic memory operand.
          triton::ast::AbstractNode* buildSymbolicMemoryOperand(const triton::arch::MemoryOperand& mem);

          //! Returns a symbolic memory operand and defines the memory as input of the instruction.
          triton::ast::AbstractNode* buildSymbolicMemoryOperand(triton::arch::Instruction& inst, triton::arch::MemoryOperand& mem);

          //! Returns a symbolic register operand.
          triton::ast::AbstractNode* buildSymbolicRegisterOperand(const triton::arch::RegisterOperand& reg);

          //! Returns a symbolic register operand and defines the register as input of the instruction.
          triton::ast::AbstractNode* buildSymbolicRegisterOperand(triton::arch::Instruction& inst, triton::arch::RegisterOperand& reg);

          //! Returns the new symbolic memory expression expression and links this expression to the instruction.
          SymbolicExpression* createSymbolicMemoryExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, triton::arch::MemoryOperand& mem, const std::string& comment="");

          //! Returns the new symbolic register expression expression and links this expression to the instruction.
          SymbolicExpression* createSymbolicRegisterExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, triton::arch::RegisterOperand& reg, const std::string& comment="");

          //! Returns the new symbolic flag expression expression and links this expression to the instruction.
          SymbolicExpression* createSymbolicFlagExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, triton::arch::RegisterOperand& flag, const std::string& comment="");

          //! Returns the new symbolic volatile expression expression and links this expression to the instruction.
          SymbolicExpression* createSymbolicVolatileExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, const std::string& comment="");

          //! Returns an unique symbolic expression id.
          triton::__uint getUniqueSymExprId(void);

          //! Returns an unique symbolic variable id.
          triton::__uint getUniqueSymVarId(void);

          //! Assigns a symbolic expression to a register.
          void assignSymbolicExpressionToRegister(SymbolicExpression *se, const triton::arch::RegisterOperand& reg);

          //! Assigns a symbolic expression to a memory.
          void assignSymbolicExpressionToMemory(SymbolicExpression *se, const triton::arch::MemoryOperand& mem);

          //! Returns the full AST of a root node.
          triton::ast::AbstractNode* getFullAst(triton::ast::AbstractNode* node);

          //! Returns the list of the tainted symbolic expressions.
          std::list<SymbolicExpression*> getTaintedSymbolicExpressions(void) const;

          //! Returns all symbolic expressions.
          const std::map<triton::__uint, SymbolicExpression*>& getSymbolicExpressions(void) const;

          //! Returns all symbolic variables.
          const std::map<triton::__uint, SymbolicVariable*>& getSymbolicVariables(void) const;

          //! Returns all variable declarations representation.
          std::string getVariablesDeclaration(void) const;

          //! Adds a symbolic memory reference.
          void addMemoryReference(triton::__uint mem, triton::__uint id);

          //! Concretizes all symbolic memory references.
          void concretizeAllMemory(void);

          //! Concretizes all symbolic register references.
          void concretizeAllRegister(void);

          //! Concretizes a specific symbolic memory reference.
          void concretizeMemory(const triton::arch::MemoryOperand& mem);

          //! Concretizes a specific symbolic memory reference.
          void concretizeMemory(triton::__uint addr);

          //! Concretizes a specific symbolic register reference.
          void concretizeRegister(const triton::arch::RegisterOperand& reg);

          /*! \brief Enables or disables the symbolic emulation.
           *
           * \description
           * **true**: full symbolic execution (emulation).
           * **false**: concolic execution.
           */
          void emulation(bool flag);

          //! Enables or disables the symbolic execution engine.
          void enable(bool flag);

          //! Returns true if the we perform a full symbolic emulation.
          bool isEmulationEnabled(void) const;

          //! Returns true if the symbolic execution engine is enabled.
          bool isEnabled(void) const;

          //! Returns true if the symbolic expression ID exists.
          bool isSymbolicExpressionIdExists(triton::__uint symExprId) const;

          //! Initializes a SymbolicEngine.
          void init(const SymbolicEngine& other);

          //! Copies a SymbolicEngine.
          void operator=(const SymbolicEngine& other);

          //! Constructor.
          SymbolicEngine();

          //! Constructor by copy.
          SymbolicEngine(const SymbolicEngine& copy);

          //! Destructor.
          ~SymbolicEngine();
      };

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SYMBOLICENGINE_H */

