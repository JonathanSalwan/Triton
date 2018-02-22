//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_API_H
#define TRITON_API_H

#include <triton/architecture.hpp>
#include <triton/ast.hpp>
#include <triton/astContext.hpp>
#include <triton/astRepresentation.hpp>
#include <triton/callbacks.hpp>
#include <triton/dllexport.hpp>
#include <triton/immediate.hpp>
#include <triton/instruction.hpp>
#include <triton/irBuilder.hpp>
#include <triton/memoryAccess.hpp>
#include <triton/modes.hpp>
#include <triton/operandWrapper.hpp>
#include <triton/register.hpp>
#include <triton/registers_e.hpp>
#include <triton/solverEngine.hpp>
#include <triton/symbolicEngine.hpp>
#include <triton/taintEngine.hpp>
#include <triton/tritonTypes.hpp>
#include <triton/z3Interface.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

    /*! \class API
     *  \brief This is used as C++ API. */
    class API {
      protected:
        //! The Callbacks interface.
        triton::callbacks::Callbacks callbacks;

        //! The architecture entry.
        triton::arch::Architecture arch;

        //! The modes.
        triton::modes::Modes modes;

        //! The taint engine.
        triton::engines::taint::TaintEngine* taint = nullptr;

        //! The symbolic engine.
        triton::engines::symbolic::SymbolicEngine* symbolic = nullptr;

        //! The solver engine.
        triton::engines::solver::SolverEngine* solver = nullptr;

        //! The AST Context interface.
        triton::ast::AstContext astCtxt;

        //! The IR builder.
        triton::arch::IrBuilder* irBuilder = nullptr;

        //! The Z3 interface between Triton and Z3.
        triton::ast::Z3Interface* z3Interface = nullptr;


      public:
        //! Constructor of the API.
        TRITON_EXPORT API();

        //! Destructor of the API.
        TRITON_EXPORT ~API();


        /* Architecture API ============================================================================== */

        //! [**Architecture api**] - Returns true if the architecture is valid.
        TRITON_EXPORT bool isArchitectureValid(void) const;

        //! [**architecture api**] - Returns the architecture as triton::arch::architectures_e.
        TRITON_EXPORT triton::arch::architectures_e getArchitecture(void) const;

        //! [**architecture api**] - Raises an exception if the architecture is not initialized.
        TRITON_EXPORT void checkArchitecture(void) const;

        //! [**architecture api**] - Returns the CPU instance.
        TRITON_EXPORT triton::arch::CpuInterface* getCpu(void);

        //! [**architecture api**] - Initializes an architecture. \sa triton::arch::architectures_e.
        TRITON_EXPORT void setArchitecture(triton::arch::architectures_e arch);

        //! [**architecture api**] - Clears the architecture states (registers and memory).
        TRITON_EXPORT void clearArchitecture(void);

        //! [**architecture api**] - Returns true if the register id is a flag. \sa triton::arch::x86::registers_e.
        TRITON_EXPORT bool isFlag(triton::arch::registers_e regId) const;

        //! [**architecture api**] - Returns true if the register id is a flag.
        TRITON_EXPORT bool isFlag(const triton::arch::Register& reg) const;

        //! [**architecture api**] - Returns true if the regId is a register. \sa triton::arch::x86::registers_e.
        TRITON_EXPORT bool isRegister(triton::arch::registers_e regId) const;

        //! [**architecture api**] - Returns true if the regId is a register.
        TRITON_EXPORT bool isRegister(const triton::arch::Register& reg) const;

        //! [**architecture api**] - Returns Register from regId.
        TRITON_EXPORT const triton::arch::Register& getRegister(triton::arch::registers_e id) const;

        //! [**architecture api**] - Returns parent Register from a register.
        TRITON_EXPORT const triton::arch::Register& getParentRegister(const triton::arch::Register& reg) const;

        //! [**architecture api**] - Returns parent Register from regId.
        TRITON_EXPORT const triton::arch::Register& getParentRegister(triton::arch::registers_e id) const;

        //! [**architecture api**] - Returns true if the regId is a register or a flag. \sa triton::arch::x86::registers_e.
        TRITON_EXPORT bool isRegisterValid(triton::arch::registers_e regId) const;

        //! [**architecture api**] - Returns true if the regId is a register or a flag.
        TRITON_EXPORT bool isRegisterValid(const triton::arch::Register& reg) const;

        //! [**architecture api**] - Returns the max size (in bit) of the CPU register (GPR).
        TRITON_EXPORT triton::uint32 getRegisterBitSize(void) const;

        //! [**architecture api**] - Returns the max size (in byte) of the CPU register (GPR).
        TRITON_EXPORT triton::uint32 getRegisterSize(void) const;

        //! [**architecture api**] - Returns the number of registers according to the CPU architecture.
        TRITON_EXPORT triton::uint32 getNumberOfRegisters(void) const;

        //! [**architecture api**] - Returns all registers. \sa triton::arch::x86::registers_e.
        TRITON_EXPORT const std::unordered_map<triton::arch::registers_e, const triton::arch::Register>& getAllRegisters(void) const;

        //! [**architecture api**] - Returns all parent registers. \sa triton::arch::x86::registers_e.
        TRITON_EXPORT std::set<const triton::arch::Register*> getParentRegisters(void) const;

        //! [**architecture api**] - Returns the concrete value of a memory cell.
        TRITON_EXPORT triton::uint8 getConcreteMemoryValue(triton::uint64 addr, bool execCallbacks=true) const;

        //! [**architecture api**] - Returns the concrete value of memory cells.
        TRITON_EXPORT triton::uint512 getConcreteMemoryValue(const triton::arch::MemoryAccess& mem, bool execCallbacks=true) const;

        //! [**architecture api**] - Returns the concrete value of a memory area.
        TRITON_EXPORT std::vector<triton::uint8> getConcreteMemoryAreaValue(triton::uint64 baseAddr, triton::usize size, bool execCallbacks=true) const;

        //! [**architecture api**] - Returns the concrete value of a register.
        TRITON_EXPORT triton::uint512 getConcreteRegisterValue(const triton::arch::Register& reg, bool execCallbacks=true) const;

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a memory cell.
         *
         * \details Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        TRITON_EXPORT void setConcreteMemoryValue(triton::uint64 addr, triton::uint8 value);

        /*!
         * \brief [**architecture api**] - Sets the concrete value of memory cells.
         *
         * \details Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        TRITON_EXPORT void setConcreteMemoryValue(const triton::arch::MemoryAccess& mem, const triton::uint512& value);

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a memory area.
         *
         * \details Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        TRITON_EXPORT void setConcreteMemoryAreaValue(triton::uint64 baseAddr, const std::vector<triton::uint8>& values);

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a memory area.
         *
         * \details Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        TRITON_EXPORT void setConcreteMemoryAreaValue(triton::uint64 baseAddr, const triton::uint8* area, triton::usize size);

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a register.
         *
         * \details Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        TRITON_EXPORT void setConcreteRegisterValue(const triton::arch::Register& reg, const triton::uint512& value);

        //! [**architecture api**] - Returns true if the range `[baseAddr:size]` is mapped into the internal memory representation. \sa getConcreteMemoryValue() and getConcreteMemoryAreaValue().
        TRITON_EXPORT bool isMemoryMapped(triton::uint64 baseAddr, triton::usize size=1);

        //! [**architecture api**] - Removes the range `[baseAddr:size]` from the internal memory representation. \sa isMemoryMapped().
        TRITON_EXPORT void unmapMemory(triton::uint64 baseAddr, triton::usize size=1);

        //! [**architecture api**] - Disassembles the instruction and setup operands. You must define an architecture before. \sa processing().
        TRITON_EXPORT void disassembly(triton::arch::Instruction& inst) const;



        /* Processing API ================================================================================ */

        //! [**proccesing api**] - Processes an instruction and updates engines according to the instruction semantics. Returns true if the instruction is supported.
        TRITON_EXPORT bool processing(triton::arch::Instruction& inst);

        //! [**proccesing api**] - Initializes everything.
        TRITON_EXPORT void initEngines(void);

        //! [**proccesing api**] - Removes everything.
        TRITON_EXPORT void removeEngines(void);

        //! [**proccesing api**] - Resets everything.
        TRITON_EXPORT void reset(void);



        /* IR API ======================================================================================== */

        //! [**IR builder api**] - Raises an exception if the IR builder is not initialized.
        TRITON_EXPORT void checkIrBuilder(void) const;

        //! [**IR builder api**] - Builds the instruction semantics. Returns true if the instruction is supported. You must define an architecture before. \sa processing().
        TRITON_EXPORT bool buildSemantics(triton::arch::Instruction& inst);

        //! [**IR builder api**] - Returns the AST context. Used as AST builder.
        TRITON_EXPORT triton::ast::AstContext& getAstContext(void);



        /* AST Garbage Collector API ===================================================================== */

        //! [**AST garbage collector api**] - Go through every allocated nodes and free them.
        TRITON_EXPORT void freeAllAstNodes(void);

        //! [**AST garbage collector api**] - Frees a set of nodes and removes them from the global container.
        TRITON_EXPORT void freeAstNodes(std::set<triton::ast::AbstractNode*>& nodes);

        //! [**AST garbage collector api**] - Extracts all unique nodes from a partial AST into the uniqueNodes set.
        TRITON_EXPORT void extractUniqueAstNodes(std::set<triton::ast::AbstractNode*>& uniqueNodes, triton::ast::AbstractNode* root) const;

        //! [**AST garbage collector api**] - Records the allocated node or returns the same node if it already exists inside the dictionaries.
        TRITON_EXPORT triton::ast::AbstractNode* recordAstNode(triton::ast::AbstractNode* node);

        //! [**AST garbage collector api**] - Records a variable AST node.
        TRITON_EXPORT void recordVariableAstNode(const std::string& name, triton::ast::AbstractNode* node);

        //! [**AST garbage collector api**] - Returns all allocated nodes.
        TRITON_EXPORT const std::set<triton::ast::AbstractNode*>& getAllocatedAstNodes(void) const;

        //! [**AST garbage collector api**] - Returns all stats about AST Dictionaries.
        TRITON_EXPORT std::map<std::string, triton::usize> getAstDictionariesStats(void) const;

        //! [**AST garbage collector api**] - Returns all variable nodes recorded.
        TRITON_EXPORT const std::map<std::string, std::vector<triton::ast::AbstractNode*>>& getAstVariableNodes(void) const;

        //! [**AST garbage collector api**] - Returns the node of a recorded variable.
        TRITON_EXPORT std::vector<triton::ast::AbstractNode*> getAstVariableNode(const std::string& name) const;

        //! [**AST garbage collector api**] - Sets all allocated nodes.
        TRITON_EXPORT void setAllocatedAstNodes(const std::set<triton::ast::AbstractNode*>& nodes);

        //! [**AST garbage collector api**] - Sets all variable nodes recorded.
        TRITON_EXPORT void setAstVariableNodes(const std::map<std::string, std::vector<triton::ast::AbstractNode*>>& nodes);



        /* AST Representation API ======================================================================== */

        //! [**AST representation api**] - Returns the AST representation mode as triton::ast::representations::mode_e.
        TRITON_EXPORT triton::uint32 getAstRepresentationMode(void) const;

        //! [**AST representation api**] - Sets the AST representation mode.
        TRITON_EXPORT void setAstRepresentationMode(triton::uint32 mode);



        /* Callbacks API ================================================================================= */

        //! [**callbacks api**] - Adds a GET_CONCRETE_MEMORY_VALUE callback (LOAD).
        TRITON_EXPORT void addCallback(triton::callbacks::getConcreteMemoryValueCallback cb);

        //! [**callbacks api**] - Adds a GET_CONCRETE_REGISTER_VALUE callback (GET).
        TRITON_EXPORT void addCallback(triton::callbacks::getConcreteRegisterValueCallback cb);

        //! [**callbacks api**] - Adds a SET_CONCRETE_MEMORY_VALUE callback (STORE).
        TRITON_EXPORT void addCallback(triton::callbacks::setConcreteMemoryValueCallback cb);

        //! [**callbacks api**] - Adds a SET_CONCRETE_REGISTER_VALUE callback (PUT).
        TRITON_EXPORT void addCallback(triton::callbacks::setConcreteRegisterValueCallback cb);

        //! [**callbacks api**] - Adds a SYMBOLIC_SIMPLIFICATION callback.
        TRITON_EXPORT void addCallback(triton::callbacks::symbolicSimplificationCallback cb);

        //! [**callbacks api**] - Removes all recorded callbacks.
        TRITON_EXPORT void removeAllCallbacks(void);

        //! [**callbacks api**] - Deletes a GET_CONCRETE_MEMORY_VALUE callback (LOAD).
        TRITON_EXPORT void removeCallback(triton::callbacks::getConcreteMemoryValueCallback cb);

        //! [**callbacks api**] - Deletes a GET_CONCRETE_REGISTER_VALUE callback (GET).
        TRITON_EXPORT void removeCallback(triton::callbacks::getConcreteRegisterValueCallback cb);

        //! [**callbacks api**] - Deletes a SET_CONCRETE_MEMORY_VALUE callback (STORE).
        TRITON_EXPORT void removeCallback(triton::callbacks::setConcreteMemoryValueCallback cb);

        //! [**callbacks api**] - Deletes a SET_CONCRETE_REGISTER_VALUE callback (PUT).
        TRITON_EXPORT void removeCallback(triton::callbacks::setConcreteRegisterValueCallback cb);

        //! [**callbacks api**] - Deletes a SYMBOLIC_SIMPLIFICATION callback.
        TRITON_EXPORT void removeCallback(triton::callbacks::symbolicSimplificationCallback cb);

        //! [**callbacks api**] - Processes callbacks according to the kind and the C++ polymorphism.
        TRITON_EXPORT triton::ast::AbstractNode* processCallbacks(triton::callbacks::callback_e kind, triton::ast::AbstractNode* node) const;

        //! [**callbacks api**] - Processes callbacks according to the kind and the C++ polymorphism.
        TRITON_EXPORT void processCallbacks(triton::callbacks::callback_e kind, const triton::arch::MemoryAccess& mem) const;

        //! [**callbacks api**] - Processes callbacks according to the kind and the C++ polymorphism.
        TRITON_EXPORT void processCallbacks(triton::callbacks::callback_e kind, const triton::arch::Register& reg) const;



        /* Modes API====================================================================================== */

        //! [**modes api**] - Raises an exception if modes interface is not initialized.
        TRITON_EXPORT void checkModes(void) const;

        //! [**modes api**] - Enables or disables a specific mode.
        TRITON_EXPORT void enableMode(enum triton::modes::mode_e mode, bool flag);

        //! [**modes api**] - Returns true if the mode is enabled.
        TRITON_EXPORT bool isModeEnabled(enum triton::modes::mode_e mode) const;



        /* Symbolic engine API =========================================================================== */

        //! [**symbolic api**] - Raises an exception if the symbolic engine is not initialized.
        TRITON_EXPORT void checkSymbolic(void) const;

        //! [**symbolic api**] - Returns the instance of the symbolic engine.
        TRITON_EXPORT triton::engines::symbolic::SymbolicEngine* getSymbolicEngine(void);

        //! [**symbolic api**] - Returns the map of symbolic registers defined.
        TRITON_EXPORT std::map<triton::arch::registers_e, triton::engines::symbolic::SymbolicExpression*> getSymbolicRegisters(void) const;

        //! [**symbolic api**] - Returns the map (<Addr : SymExpr>) of symbolic memory defined.
        TRITON_EXPORT std::map<triton::uint64, triton::engines::symbolic::SymbolicExpression*> getSymbolicMemory(void) const;

        //! [**symbolic api**] - Returns the symbolic expression id corresponding to the memory address.
        TRITON_EXPORT triton::usize getSymbolicMemoryId(triton::uint64 addr) const;

        //! [**symbolic api**] - Returns the symbolic expression id corresponding to the register.
        TRITON_EXPORT triton::usize getSymbolicRegisterId(const triton::arch::Register& reg) const;

        //! [**symbolic api**] - Returns the symbolic memory value.
        TRITON_EXPORT triton::uint8 getSymbolicMemoryValue(triton::uint64 address);

        //! [**symbolic api**] - Returns the symbolic memory value.
        TRITON_EXPORT triton::uint512 getSymbolicMemoryValue(const triton::arch::MemoryAccess& mem);

        //! [**symbolic api**] - Returns the symbolic values of a memory area.
        TRITON_EXPORT std::vector<triton::uint8> getSymbolicMemoryAreaValue(triton::uint64 baseAddr, triton::usize size);

        //! [**symbolic api**] - Returns the symbolic register value.
        TRITON_EXPORT triton::uint512 getSymbolicRegisterValue(const triton::arch::Register& reg);

        //! [**symbolic api**] - Converts a symbolic expression to a symbolic variable. `symVarSize` must be in bits.
        TRITON_EXPORT triton::engines::symbolic::SymbolicVariable* convertExpressionToSymbolicVariable(triton::usize exprId, triton::uint32 symVarSize, const std::string& symVarComment="");

        //! [**symbolic api**] - Converts a symbolic memory expression to a symbolic variable.
        TRITON_EXPORT triton::engines::symbolic::SymbolicVariable* convertMemoryToSymbolicVariable(const triton::arch::MemoryAccess& mem, const std::string& symVarComment="");

        //! [**symbolic api**] - Converts a symbolic register expression to a symbolic variable.
        TRITON_EXPORT triton::engines::symbolic::SymbolicVariable* convertRegisterToSymbolicVariable(const triton::arch::Register& reg, const std::string& symVarComment="");

        //! [**symbolic api**] - Returns a symbolic operand.
        TRITON_EXPORT triton::ast::AbstractNode* buildSymbolicOperand(const triton::arch::OperandWrapper& op);

        //! [**symbolic api**] - Returns a symbolic operand.
        TRITON_EXPORT triton::ast::AbstractNode* buildSymbolicOperand(triton::arch::Instruction& inst, const triton::arch::OperandWrapper& op);

        //! [**symbolic api**] - Returns an immediate symbolic.
        TRITON_EXPORT triton::ast::AbstractNode* buildSymbolicImmediate(const triton::arch::Immediate& imm);

        //! [**symbolic api**] - Returns an immediate symbolic and defines the immediate as input of the instruction..
        TRITON_EXPORT triton::ast::AbstractNode* buildSymbolicImmediate(triton::arch::Instruction& inst, const triton::arch::Immediate& imm);

        //! [**symbolic api**] - Returns a symbolic memory cell.
        TRITON_EXPORT triton::ast::AbstractNode* buildSymbolicMemory(const triton::arch::MemoryAccess& mem);

        //! [**symbolic api**] - Returns a symbolic memory cell and defines the memory cell as input of the instruction.
        TRITON_EXPORT triton::ast::AbstractNode* buildSymbolicMemory(triton::arch::Instruction& inst, const triton::arch::MemoryAccess& mem);

        //! [**symbolic api**] - Returns a symbolic register.
        TRITON_EXPORT triton::ast::AbstractNode* buildSymbolicRegister(const triton::arch::Register& reg);

        //! [**symbolic api**] - Returns a symbolic register and defines the register as input of the instruction.
        TRITON_EXPORT triton::ast::AbstractNode* buildSymbolicRegister(triton::arch::Instruction& inst, const triton::arch::Register& reg);

        //! [**symbolic api**] - Returns a new symbolic expression. Note that if there are simplification passes recorded, simplification will be applied.
        TRITON_EXPORT triton::engines::symbolic::SymbolicExpression* newSymbolicExpression(triton::ast::AbstractNode* node, const std::string& comment="");

        //! [**symbolic api**] - Returns a new symbolic variable.
        TRITON_EXPORT triton::engines::symbolic::SymbolicVariable* newSymbolicVariable(triton::uint32 varSize, const std::string& comment="");

        //! [**symbolic api**] - Removes the symbolic expression corresponding to the id.
        TRITON_EXPORT void removeSymbolicExpression(triton::usize symExprId);

        //! [**symbolic api**] - Returns the new symbolic abstract expression and links this expression to the instruction.
        TRITON_EXPORT triton::engines::symbolic::SymbolicExpression* createSymbolicExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, const triton::arch::OperandWrapper& dst, const std::string& comment="");

        //! [**symbolic api**] - Returns the new symbolic memory expression and links this expression to the instruction.
        TRITON_EXPORT triton::engines::symbolic::SymbolicExpression* createSymbolicMemoryExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, const triton::arch::MemoryAccess& mem, const std::string& comment="");

        //! [**symbolic api**] - Returns the new symbolic register expression and links this expression to the instruction.
        TRITON_EXPORT triton::engines::symbolic::SymbolicExpression* createSymbolicRegisterExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, const triton::arch::Register& reg, const std::string& comment="");

        //! [**symbolic api**] - Returns the new symbolic flag expression and links this expression to the instruction.
        TRITON_EXPORT triton::engines::symbolic::SymbolicExpression* createSymbolicFlagExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, const triton::arch::Register& flag, const std::string& comment="");

        //! [**symbolic api**] - Returns the new symbolic volatile expression and links this expression to the instruction.
        TRITON_EXPORT triton::engines::symbolic::SymbolicExpression* createSymbolicVolatileExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, const std::string& comment="");

        //! [**symbolic api**] - Assigns a symbolic expression to a memory.
        TRITON_EXPORT void assignSymbolicExpressionToMemory(triton::engines::symbolic::SymbolicExpression* se, const triton::arch::MemoryAccess& mem);

        //! [**symbolic api**] - Assigns a symbolic expression to a register.
        TRITON_EXPORT void assignSymbolicExpressionToRegister(triton::engines::symbolic::SymbolicExpression* se, const triton::arch::Register& reg);

        //! [**symbolic api**] - Processes all recorded simplifications. Returns the simplified node.
        TRITON_EXPORT triton::ast::AbstractNode* processSimplification(triton::ast::AbstractNode* node, bool z3=false) const;

        //! [**symbolic api**] - Returns the symbolic expression corresponding to an id.
        TRITON_EXPORT triton::engines::symbolic::SymbolicExpression* getSymbolicExpressionFromId(triton::usize symExprId) const;

        //! [**symbolic api**] - Returns the symbolic variable corresponding to the symbolic variable id.
        TRITON_EXPORT triton::engines::symbolic::SymbolicVariable* getSymbolicVariableFromId(triton::usize symVarId) const;

        //! [**symbolic api**] - Returns the symbolic variable corresponding to the symbolic variable name.
        TRITON_EXPORT triton::engines::symbolic::SymbolicVariable* getSymbolicVariableFromName(const std::string& symVarName) const;

        //! [**symbolic api**] - Returns the logical conjunction vector of path constraints.
        TRITON_EXPORT const std::vector<triton::engines::symbolic::PathConstraint>& getPathConstraints(void) const;

        //! [**symbolic api**] - Returns the logical conjunction AST of path constraints.
        TRITON_EXPORT triton::ast::AbstractNode* getPathConstraintsAst(void);

        //! [**symbolic api**] - Adds a path constraint.
        TRITON_EXPORT void addPathConstraint(const triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* expr);

        //! [**symbolic api**] - Clears the logical conjunction vector of path constraints.
        TRITON_EXPORT void clearPathConstraints(void);

        //! [**symbolic api**] - Enables or disables the symbolic execution engine.
        TRITON_EXPORT void enableSymbolicEngine(bool flag);

        //! [**symbolic api**] - Returns true if the symbolic execution engine is enabled.
        TRITON_EXPORT bool isSymbolicEngineEnabled(void) const;

        //! [**symbolic api**] - Returns true if the symbolic expression ID exists.
        TRITON_EXPORT bool isSymbolicExpressionIdExists(triton::usize symExprId) const;

        //! [**symbolic api**] - Returns true if memory cell expressions contain symbolic variables.
        TRITON_EXPORT bool isMemorySymbolized(const triton::arch::MemoryAccess& mem) const;

        //! [**symbolic api**] - Returns true if memory cell expressions contain symbolic variables.
        TRITON_EXPORT bool isMemorySymbolized(triton::uint64 addr, triton::uint32 size=1) const;

        //! [**symbolic api**] - Returns true if the register expression contains a symbolic variable.
        TRITON_EXPORT bool isRegisterSymbolized(const triton::arch::Register& reg) const;

        //! [**symbolic api**] - Concretizes all symbolic memory references.
        TRITON_EXPORT void concretizeAllMemory(void);

        //! [**symbolic api**] - Concretizes all symbolic register references.
        TRITON_EXPORT void concretizeAllRegister(void);

        //! [**symbolic api**] - Concretizes a specific symbolic memory reference.
        TRITON_EXPORT void concretizeMemory(const triton::arch::MemoryAccess& mem);

        //! [**symbolic api**] - Concretizes a specific symbolic memory reference.
        TRITON_EXPORT void concretizeMemory(triton::uint64 addr);

        //! [**symbolic api**] - Concretizes a specific symbolic register reference.
        TRITON_EXPORT void concretizeRegister(const triton::arch::Register& reg);

        //! [**symbolic api**] - Returns the partial AST from a symbolic expression id.
        TRITON_EXPORT triton::ast::AbstractNode* getAstFromId(triton::usize symExprId);

        //! [**symbolic api**] - Unrolls the SSA form of a given AST.
        TRITON_EXPORT triton::ast::AbstractNode* unrollAst(triton::ast::AbstractNode* node);

        //! [**symbolic api**] - Unrolls the SSA form of a given symbolic expression id.
        TRITON_EXPORT triton::ast::AbstractNode* unrollAstFromId(triton::usize symExprId);

        //! [**symbolic api**] - Slices all expressions from a given one.
        TRITON_EXPORT std::map<triton::usize, triton::engines::symbolic::SymbolicExpression*> sliceExpressions(triton::engines::symbolic::SymbolicExpression* expr);

        //! [**symbolic api**] - Returns the list of the tainted symbolic expressions.
        TRITON_EXPORT std::list<triton::engines::symbolic::SymbolicExpression*> getTaintedSymbolicExpressions(void) const;

        //! [**symbolic api**] - Returns all symbolic expressions as a map of <SymExprId : SymExpr>
        TRITON_EXPORT const std::map<triton::usize, triton::engines::symbolic::SymbolicExpression*>& getSymbolicExpressions(void) const;

        //! [**symbolic api**] - Returns all symbolic variables as a map of <SymVarId : SymVar>
        TRITON_EXPORT const std::map<triton::usize, triton::engines::symbolic::SymbolicVariable*>& getSymbolicVariables(void) const;

        //! [**symbolic api**] - Gets the concrete value of a symbolic variable.
        TRITON_EXPORT const triton::uint512& getConcreteSymbolicVariableValue(const triton::engines::symbolic::SymbolicVariable& symVar) const;

        //! [**symbolic api**] - Sets the concrete value of a symbolic variable.
        TRITON_EXPORT void setConcreteSymbolicVariableValue(const triton::engines::symbolic::SymbolicVariable& symVar, const triton::uint512& value);



        /* Solver engine API ============================================================================= */

        //! [**solver api**] - Raises an exception if the solver engine is not initialized.
        TRITON_EXPORT void checkSolver(void) const;

        /*!
         * \brief [**solver api**] - Computes and returns a model from a symbolic constraint.
         *
         * \details
         * **item1**: symbolic variable id<br>
         * **item2**: model
         */
        TRITON_EXPORT std::map<triton::uint32, triton::engines::solver::SolverModel> getModel(triton::ast::AbstractNode* node) const;

        /*!
         * \brief [**solver api**] - Computes and returns several models from a symbolic constraint. The `limit` is the number of models returned.
         *
         * \details
         * **item1**: symbolic variable id<br>
         * **item2**: model
         */
        TRITON_EXPORT std::list<std::map<triton::uint32, triton::engines::solver::SolverModel>> getModels(triton::ast::AbstractNode* node, triton::uint32 limit) const;



        /* Z3 interface API ============================================================================== */

        //! [**z3 api**] - Raises an exception if the z3 interface is not initialized.
        TRITON_EXPORT void checkZ3Interface(void) const;

        //! [**z3 api**] - Evaluates a Triton's AST via Z3 and returns a concrete value.
        TRITON_EXPORT triton::uint512 evaluateAstViaZ3(triton::ast::AbstractNode* node) const;

        //! [**z3 api**] - Converts a Triton's AST to a Z3's AST, perform a Z3 simplification and returns a Triton's AST.
        TRITON_EXPORT triton::ast::AbstractNode* processZ3Simplification(triton::ast::AbstractNode* node) const;



        /* Taint engine API ============================================================================== */

        //! [**taint api**] - Raises an exception if the taint engine is not initialized.
        TRITON_EXPORT void checkTaint(void) const;

        //! [**taint api**] - Returns the instance of the taint engine.
        TRITON_EXPORT triton::engines::taint::TaintEngine* getTaintEngine(void);

        //! [**taint api**] - Returns the tainted addresses.
        TRITON_EXPORT const std::set<triton::uint64>& getTaintedMemory(void) const;

        //! [**taint api**] - Returns the tainted registers.
        TRITON_EXPORT std::set<const triton::arch::Register*> getTaintedRegisters(void) const;

        //! [**taint api**] - Enables or disables the taint engine.
        TRITON_EXPORT void enableTaintEngine(bool flag);

        //! [**taint api**] - Returns true if the taint engine is enabled.
        TRITON_EXPORT bool isTaintEngineEnabled(void) const;

        //! [**taint api**] - Abstract taint verification. Returns true if the operand is tainted.
        TRITON_EXPORT bool isTainted(const triton::arch::OperandWrapper& op) const;

        //! [**taint api**] - Returns true if the address:size is tainted.
        TRITON_EXPORT bool isMemoryTainted(triton::uint64 addr, triton::uint32 size=1) const;

        //! [**taint api**] - Returns true if the memory is tainted.
        TRITON_EXPORT bool isMemoryTainted(const triton::arch::MemoryAccess& mem) const;

        //! [**taint api**] - Returns true if the register is tainted.
        TRITON_EXPORT bool isRegisterTainted(const triton::arch::Register& reg) const;

        //! [**taint api**] - Sets the flag (taint or untaint) to an abstract operand (Register or Memory).
        TRITON_EXPORT bool setTaint(const triton::arch::OperandWrapper& op, bool flag);

        //! [**taint api**] - Sets the flag (taint or untaint) to a memory.
        TRITON_EXPORT bool setTaintMemory(const triton::arch::MemoryAccess& mem, bool flag);

        //! [**taint api**] - Sets the flag (taint or untaint) to a register.
        TRITON_EXPORT bool setTaintRegister(const triton::arch::Register& reg, bool flag);

        //! [**taint api**] - Taints an address. Returns TAINTED if the address has been tainted correctly. Otherwise it returns the last defined state.
        TRITON_EXPORT bool taintMemory(triton::uint64 addr);

        //! [**taint api**] - Taints a memory. Returns TAINTED if the memory has been tainted correctly. Otherwise it returns the last defined state.
        TRITON_EXPORT bool taintMemory(const triton::arch::MemoryAccess& mem);

        //! [**taint api**] - Taints a register. Returns TAINTED if the register has been tainted correctly. Otherwise it returns the last defined state.
        TRITON_EXPORT bool taintRegister(const triton::arch::Register& reg);

        //! [**taint api**] - Untaints an address. Returns !TAINTED if the address has been untainted correctly. Otherwise it returns the last defined state.
        TRITON_EXPORT bool untaintMemory(triton::uint64 addr);

        //! [**taint api**] - Untaints a memory. Returns !TAINTED if the memory has been untainted correctly. Otherwise it returns the last defined state.
        TRITON_EXPORT bool untaintMemory(const triton::arch::MemoryAccess& mem);

        //! [**taint api**] - Untaints a register. Returns !TAINTED if the register has been untainted correctly. Otherwise it returns the last defined state.
        TRITON_EXPORT bool untaintRegister(const triton::arch::Register& reg);

        //! [**taint api**] - Abstract union tainting.
        TRITON_EXPORT bool taintUnion(const triton::arch::OperandWrapper& op1, const triton::arch::OperandWrapper& op2);

        //! [**taint api**] - Abstract assignment tainting.
        TRITON_EXPORT bool taintAssignment(const triton::arch::OperandWrapper& op1, const triton::arch::OperandWrapper& op2);

        //! [**taint api**] - Taints MemoryImmediate with union. Returns true if the memDst is TAINTED.
        TRITON_EXPORT bool taintUnionMemoryImmediate(const triton::arch::MemoryAccess& memDst);

        //! [**taint api**] - Taints MemoryMemory with union. Returns true if the memDst or memSrc are TAINTED.
        TRITON_EXPORT bool taintUnionMemoryMemory(const triton::arch::MemoryAccess& memDst, const triton::arch::MemoryAccess& memSrc);

        //! [**taint api**] - Taints MemoryRegister with union. Returns true if the memDst or regSrc are TAINTED.
        TRITON_EXPORT bool taintUnionMemoryRegister(const triton::arch::MemoryAccess& memDst, const triton::arch::Register& regSrc);

        //! [**taint api**] - Taints RegisterImmediate with union. Returns true if the regDst is TAINTED.
        TRITON_EXPORT bool taintUnionRegisterImmediate(const triton::arch::Register& regDst);

        //! [**taint api**] - Taints RegisterMemory with union. Returns true if the regDst or memSrc are TAINTED.
        TRITON_EXPORT bool taintUnionRegisterMemory(const triton::arch::Register& regDst, const triton::arch::MemoryAccess& memSrc);

        //! [**taint api**] - Taints RegisterRegister with union. Returns true if the regDst or regSrc are TAINTED.
        TRITON_EXPORT bool taintUnionRegisterRegister(const triton::arch::Register& regDst, const triton::arch::Register& regSrc);

        //! [**taint api**] - Taints MemoryImmediate with assignment. Returns always false.
        TRITON_EXPORT bool taintAssignmentMemoryImmediate(const triton::arch::MemoryAccess& memDst);

        //! [**taint api**] - Taints MemoryMemory with assignment. Returns true if the memDst is tainted.
        TRITON_EXPORT bool taintAssignmentMemoryMemory(const triton::arch::MemoryAccess& memDst, const triton::arch::MemoryAccess& memSrc);

        //! [**taint api**] - Taints MemoryRegister with assignment. Returns true if the memDst is tainted.
        TRITON_EXPORT bool taintAssignmentMemoryRegister(const triton::arch::MemoryAccess& memDst, const triton::arch::Register& regSrc);

        //! [**taint api**] - Taints RegisterImmediate with assignment. Returns always false.
        TRITON_EXPORT bool taintAssignmentRegisterImmediate(const triton::arch::Register& regDst);

        //! [**taint api**] - Taints RegisterMemory with assignment. Returns true if the regDst is tainted.
        TRITON_EXPORT bool taintAssignmentRegisterMemory(const triton::arch::Register& regDst, const triton::arch::MemoryAccess& memSrc);

        //! [**taint api**] - Taints RegisterRegister with assignment. Returns true if the regDst is tainted.
        TRITON_EXPORT bool taintAssignmentRegisterRegister(const triton::arch::Register& regDst, const triton::arch::Register& regSrc);
    };

/*! @} End of triton namespace */
};

#endif /* TRITON_API_H */

