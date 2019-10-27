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
#include <triton/triton_export.h>
#include <triton/immediate.hpp>
#include <triton/instruction.hpp>
#include <triton/irBuilder.hpp>
#include <triton/memoryAccess.hpp>
#include <triton/modes.hpp>
#include <triton/operandWrapper.hpp>
#include <triton/register.hpp>
#include <triton/shortcutRegister.hpp>
#include <triton/solverEngine.hpp>
#include <triton/symbolicEngine.hpp>
#include <triton/taintEngine.hpp>
#include <triton/tritonTypes.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

    /*! \class API
     *  \brief This is used as C++ API. */
    class API {
      private:
        //! Raises an exception if the architecture is not initialized.
        inline void checkArchitecture(void) const;

        //! Raises an exception if the IR builder is not initialized.
        inline void checkIrBuilder(void) const;

        //! Raises an exception if the symbolic engine is not initialized.
        inline void checkSymbolic(void) const;

        //! Raises an exception if the solver engine is not initialized.
        inline void checkSolver(void) const;

        //! Raises an exception if the taint engine is not initialized.
        inline void checkTaint(void) const;


      protected:
        //! The Callbacks interface.
        triton::callbacks::Callbacks callbacks;

        //! The architecture entry.
        triton::arch::Architecture arch;

        //! The modes.
        triton::modes::SharedModes modes;

        //! The taint engine.
        triton::engines::taint::TaintEngine* taint = nullptr;

        //! The symbolic engine.
        triton::engines::symbolic::SymbolicEngine* symbolic = nullptr;

        //! The solver engine.
        triton::engines::solver::SolverEngine* solver = nullptr;

        //! The AST Context interface.
        triton::ast::SharedAstContext astCtxt;

        //! The IR builder.
        triton::arch::IrBuilder* irBuilder = nullptr;


      public:
        //! A shortcut to access to a Register class from a register name.
        triton::arch::ShortcutRegister registers;

        //! Constructor of the API.
        TRITON_EXPORT API();

        //! Constructor of the API.
        TRITON_EXPORT API(triton::arch::architecture_e arch);

        //! Destructor of the API.
        TRITON_EXPORT ~API();



        /* Architecture API ============================================================================== */

        //! [**Architecture api**] - Returns true if the architecture is valid.
        TRITON_EXPORT bool isArchitectureValid(void) const;

        //! [**architecture api**] - Returns the architecture as triton::arch::architecture_e.
        TRITON_EXPORT triton::arch::architecture_e getArchitecture(void) const;

        //! [**architecture api**] - Returns the endianness as triton::arch::endianness_e.
        TRITON_EXPORT triton::arch::endianness_e getEndianness(void) const;

        //! [**architecture api**] - Returns the instance of the current CPU used.
        TRITON_EXPORT triton::arch::CpuInterface* getCpuInstance(void);

        //! [**architecture api**] - Initializes an architecture. \sa triton::arch::architecture_e.
        TRITON_EXPORT void setArchitecture(triton::arch::architecture_e arch);

        //! [**architecture api**] - Clears the architecture states (registers and memory).
        TRITON_EXPORT void clearArchitecture(void);

        //! [**architecture api**] - Returns true if the register id is a flag. \sa triton::arch::x86::register_e.
        TRITON_EXPORT bool isFlag(triton::arch::register_e regId) const;

        //! [**architecture api**] - Returns true if the register id is a flag.
        TRITON_EXPORT bool isFlag(const triton::arch::Register& reg) const;

        //! [**architecture api**] - Returns true if the regId is a register. \sa triton::arch::x86::register_e.
        TRITON_EXPORT bool isRegister(triton::arch::register_e regId) const;

        //! [**architecture api**] - Returns true if the regId is a register.
        TRITON_EXPORT bool isRegister(const triton::arch::Register& reg) const;

        //! [**architecture api**] - Returns Register from regId.
        TRITON_EXPORT const triton::arch::Register& getRegister(triton::arch::register_e id) const;

        //! [**architecture api**] - Returns parent Register from a register.
        TRITON_EXPORT const triton::arch::Register& getParentRegister(const triton::arch::Register& reg) const;

        //! [**architecture api**] - Returns parent Register from regId.
        TRITON_EXPORT const triton::arch::Register& getParentRegister(triton::arch::register_e id) const;

        //! [**architecture api**] - Returns true if the regId is a register or a flag. \sa triton::arch::x86::register_e.
        TRITON_EXPORT bool isRegisterValid(triton::arch::register_e regId) const;

        //! [**architecture api**] - Returns true if the regId is a register or a flag.
        TRITON_EXPORT bool isRegisterValid(const triton::arch::Register& reg) const;

        //! [**architecture api**] - Returns the bit in byte of the General Purpose Registers.
        TRITON_EXPORT triton::uint32 getGprBitSize(void) const;

        //! [**architecture api**] - Returns the size in byte of the General Purpose Registers.
        TRITON_EXPORT triton::uint32 getGprSize(void) const;

        //! [**architecture api**] - Returns the number of registers according to the CPU architecture.
        TRITON_EXPORT triton::uint32 getNumberOfRegisters(void) const;

        //! [**architecture api**] - Returns all registers. \sa triton::arch::x86::register_e.
        TRITON_EXPORT const std::unordered_map<triton::arch::register_e, const triton::arch::Register>& getAllRegisters(void) const;

        //! [**architecture api**] - Returns all parent registers. \sa triton::arch::x86::register_e.
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

        //! [**IR builder api**] - Builds the instruction semantics. Returns true if the instruction is supported. You must define an architecture before. \sa processing().
        TRITON_EXPORT bool buildSemantics(triton::arch::Instruction& inst);

        //! [**IR builder api**] - Returns the AST context. Used as AST builder.
        TRITON_EXPORT triton::ast::SharedAstContext getAstContext(void);



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
        TRITON_EXPORT triton::ast::SharedAbstractNode processCallbacks(triton::callbacks::callback_e kind, triton::ast::SharedAbstractNode node);

        //! [**callbacks api**] - Processes callbacks according to the kind and the C++ polymorphism.
        TRITON_EXPORT void processCallbacks(triton::callbacks::callback_e kind, const triton::arch::MemoryAccess& mem);

        //! [**callbacks api**] - Processes callbacks according to the kind and the C++ polymorphism.
        TRITON_EXPORT void processCallbacks(triton::callbacks::callback_e kind, const triton::arch::Register& reg);



        /* Modes API====================================================================================== */

        //! [**modes api**] - Enables or disables a specific mode.
        TRITON_EXPORT void setMode(triton::modes::mode_e mode, bool flag);

        //! [**modes api**] - Returns true if the mode is enabled.
        TRITON_EXPORT bool isModeEnabled(triton::modes::mode_e mode) const;



        /* Symbolic engine API =========================================================================== */

        //! [**symbolic api**] - Returns the instance of the symbolic engine.
        TRITON_EXPORT triton::engines::symbolic::SymbolicEngine* getSymbolicEngine(void);

        //! [**symbolic api**] - Returns the map of symbolic registers defined.
        TRITON_EXPORT std::map<triton::arch::register_e, triton::engines::symbolic::SharedSymbolicExpression> getSymbolicRegisters(void) const;

        //! [**symbolic api**] - Returns the map (<Addr : SymExpr>) of symbolic memory defined.
        TRITON_EXPORT std::map<triton::uint64, triton::engines::symbolic::SharedSymbolicExpression> getSymbolicMemory(void) const;

        //! [**symbolic api**] - Returns the shared symbolic expression corresponding to the memory address.
        TRITON_EXPORT triton::engines::symbolic::SharedSymbolicExpression getSymbolicMemory(triton::uint64 addr) const;

        //! [**symbolic api**] - Returns the shared symbolic expression corresponding to the parent register.
        TRITON_EXPORT const triton::engines::symbolic::SharedSymbolicExpression& getSymbolicRegister(const triton::arch::Register& reg) const;

        //! [**symbolic api**] - Returns the symbolic memory value.
        TRITON_EXPORT triton::uint8 getSymbolicMemoryValue(triton::uint64 address);

        //! [**symbolic api**] - Returns the symbolic memory value.
        TRITON_EXPORT triton::uint512 getSymbolicMemoryValue(const triton::arch::MemoryAccess& mem);

        //! [**symbolic api**] - Returns the symbolic values of a memory area.
        TRITON_EXPORT std::vector<triton::uint8> getSymbolicMemoryAreaValue(triton::uint64 baseAddr, triton::usize size);

        //! [**symbolic api**] - Returns the symbolic register value.
        TRITON_EXPORT triton::uint512 getSymbolicRegisterValue(const triton::arch::Register& reg);

        //! [**symbolic api**] - Returns the AST corresponding to the operand.
        TRITON_EXPORT triton::ast::SharedAbstractNode getOperandAst(const triton::arch::OperandWrapper& op);

        //! [**symbolic api**] - Returns the AST corresponding to the operand.
        TRITON_EXPORT triton::ast::SharedAbstractNode getOperandAst(triton::arch::Instruction& inst, const triton::arch::OperandWrapper& op);

        //! [**symbolic api**] - Returns the AST corresponding to the immediate.
        TRITON_EXPORT triton::ast::SharedAbstractNode getImmediateAst(const triton::arch::Immediate& imm);

        //! [**symbolic api**] - Returns the AST corresponding to the immediate and defines the immediate as input of the instruction..
        TRITON_EXPORT triton::ast::SharedAbstractNode getImmediateAst(triton::arch::Instruction& inst, const triton::arch::Immediate& imm);

        //! [**symbolic api**] - Returns the AST corresponding to the memory.
        TRITON_EXPORT triton::ast::SharedAbstractNode getMemoryAst(const triton::arch::MemoryAccess& mem);

        //! [**symbolic api**] - Returns the AST corresponding to the memory and defines the memory cell as input of the instruction.
        TRITON_EXPORT triton::ast::SharedAbstractNode getMemoryAst(triton::arch::Instruction& inst, const triton::arch::MemoryAccess& mem);

        //! [**symbolic api**] - Returns the AST corresponding to the register.
        TRITON_EXPORT triton::ast::SharedAbstractNode getRegisterAst(const triton::arch::Register& reg);

        //! [**symbolic api**] - Returns the AST corresponding to the register and defines the register as input of the instruction.
        TRITON_EXPORT triton::ast::SharedAbstractNode getRegisterAst(triton::arch::Instruction& inst, const triton::arch::Register& reg);

        //! [**symbolic api**] - Returns a new shared symbolic expression. Note that if there are simplification passes recorded, simplification will be applied.
        TRITON_EXPORT triton::engines::symbolic::SharedSymbolicExpression newSymbolicExpression(const triton::ast::SharedAbstractNode& node, const std::string& comment="");

        //! [**symbolic api**] - Returns a new symbolic variable.
        TRITON_EXPORT triton::engines::symbolic::SharedSymbolicVariable newSymbolicVariable(triton::uint32 varSize, const std::string& comment="");

        //! [**symbolic api**] - Removes the symbolic expression corresponding to the id.
        TRITON_EXPORT void removeSymbolicExpression(triton::usize symExprId);

        //! [**symbolic api**] - Returns the new shared symbolic abstract expression and links this expression to the instruction.
        TRITON_EXPORT const triton::engines::symbolic::SharedSymbolicExpression& createSymbolicExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const triton::arch::OperandWrapper& dst, const std::string& comment="");

        //! [**symbolic api**] - Returns the new shared symbolic memory expression and links this expression to the instruction.
        TRITON_EXPORT const triton::engines::symbolic::SharedSymbolicExpression& createSymbolicMemoryExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const triton::arch::MemoryAccess& mem, const std::string& comment="");

        //! [**symbolic api**] - Returns the new shared symbolic register expression and links this expression to the instruction.
        TRITON_EXPORT const triton::engines::symbolic::SharedSymbolicExpression& createSymbolicRegisterExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const triton::arch::Register& reg, const std::string& comment="");

        //! [**symbolic api**] - Returns the new shared symbolic volatile expression and links this expression to the instruction.
        TRITON_EXPORT const triton::engines::symbolic::SharedSymbolicExpression& createSymbolicVolatileExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const std::string& comment="");

        //! [**symbolic api**] - Assigns a symbolic expression to a memory.
        TRITON_EXPORT void assignSymbolicExpressionToMemory(const triton::engines::symbolic::SharedSymbolicExpression& se, const triton::arch::MemoryAccess& mem);

        //! [**symbolic api**] - Assigns a symbolic expression to a register.
        TRITON_EXPORT void assignSymbolicExpressionToRegister(const triton::engines::symbolic::SharedSymbolicExpression& se, const triton::arch::Register& reg);

        //! [**symbolic api**] - Processes all recorded simplifications. Returns the simplified node.
        TRITON_EXPORT triton::ast::SharedAbstractNode processSimplification(const triton::ast::SharedAbstractNode& node, bool z3=false) const;

        //! [**symbolic api**] - Returns the shared symbolic expression corresponding to an id.
        TRITON_EXPORT triton::engines::symbolic::SharedSymbolicExpression getSymbolicExpression(triton::usize symExprId) const;

        //! [**symbolic api**] - Returns the symbolic variable corresponding to the symbolic variable id.
        TRITON_EXPORT triton::engines::symbolic::SharedSymbolicVariable getSymbolicVariable(triton::usize symVarId) const;

        //! [**symbolic api**] - Returns the symbolic variable corresponding to the symbolic variable name.
        TRITON_EXPORT triton::engines::symbolic::SharedSymbolicVariable getSymbolicVariable(const std::string& symVarName) const;

        //! [**symbolic api**] - Returns the logical conjunction vector of path constraints.
        TRITON_EXPORT const std::vector<triton::engines::symbolic::PathConstraint>& getPathConstraints(void) const;

        //! [**symbolic api**] - Returns the current path predicate as an AST of logical conjunction of each taken branch.
        TRITON_EXPORT triton::ast::SharedAbstractNode getPathPredicate(void);

        //! [**symbolic api**] - Returns path predicates which may reach the targeted address.
        TRITON_EXPORT std::vector<triton::ast::SharedAbstractNode> getPredicatesToReachAddress(triton::uint64 addr);

        //! [**symbolic api**] - Pushs constraints to the current path predicate.
        TRITON_EXPORT void pushPathConstraint(const triton::ast::SharedAbstractNode& node);

        //! [**symbolic api**] - Pops the last constraints added to the path predicate.
        TRITON_EXPORT void popPathConstraint(void);

        //! [**symbolic api**] - Clears the current path predicate.
        TRITON_EXPORT void clearPathConstraints(void);

        //! [**symbolic api**] - Enables or disables the symbolic execution engine.
        TRITON_EXPORT void enableSymbolicEngine(bool flag);

        //! [**symbolic api**] - Returns true if the symbolic execution engine is enabled.
        TRITON_EXPORT bool isSymbolicEngineEnabled(void) const;

        //! [**symbolic api**] - Returns true if the symbolic expression ID exists.
        TRITON_EXPORT bool isSymbolicExpressionExists(triton::usize symExprId) const;

        //! [**symbolic api**] - Returns true if memory cell expressions contain symbolic variables.
        TRITON_EXPORT bool isMemorySymbolized(const triton::arch::MemoryAccess& mem) const;

        //! [**symbolic api**] - Returns true if memory cell expressions contain symbolic variables.
        TRITON_EXPORT bool isMemorySymbolized(triton::uint64 addr, triton::uint32 size=1) const;

        //! [**symbolic api**] - Returns true if the register expression contains a symbolic variable.
        TRITON_EXPORT bool isRegisterSymbolized(const triton::arch::Register& reg) const;

        //! [**symbolic api**] - Converts a symbolic expression to a symbolic variable. `symVarSize` must be in bits.
        TRITON_EXPORT triton::engines::symbolic::SharedSymbolicVariable symbolizeExpression(triton::usize exprId, triton::uint32 symVarSize, const std::string& symVarComment="");

        //! [**symbolic api**] - Converts a symbolic memory expression to a symbolic variable.
        TRITON_EXPORT triton::engines::symbolic::SharedSymbolicVariable symbolizeMemory(const triton::arch::MemoryAccess& mem, const std::string& symVarComment="");

        //! [**symbolic api**] - Converts a symbolic register expression to a symbolic variable.
        TRITON_EXPORT triton::engines::symbolic::SharedSymbolicVariable symbolizeRegister(const triton::arch::Register& reg, const std::string& symVarComment="");

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

        //! [**symbolic api**] - Slices all expressions from a given one.
        TRITON_EXPORT std::map<triton::usize, triton::engines::symbolic::SharedSymbolicExpression> sliceExpressions(const triton::engines::symbolic::SharedSymbolicExpression& expr);

        //! [**symbolic api**] - Returns the list of the tainted symbolic expressions.
        TRITON_EXPORT std::vector<triton::engines::symbolic::SharedSymbolicExpression> getTaintedSymbolicExpressions(void) const;

        //! [**symbolic api**] - Returns all symbolic expressions as a map of <SymExprId : SymExpr>
        TRITON_EXPORT std::unordered_map<triton::usize, triton::engines::symbolic::SharedSymbolicExpression> getSymbolicExpressions(void) const;

        //! [**symbolic api**] - Returns all symbolic variables as a map of <SymVarId : SymVar>
        TRITON_EXPORT std::unordered_map<triton::usize, triton::engines::symbolic::SharedSymbolicVariable> getSymbolicVariables(void) const;

        //! [**symbolic api**] - Gets the concrete value of a symbolic variable.
        TRITON_EXPORT triton::uint512 getConcreteVariableValue(const triton::engines::symbolic::SharedSymbolicVariable& symVar) const;

        //! [**symbolic api**] - Sets the concrete value of a symbolic variable.
        TRITON_EXPORT void setConcreteVariableValue(const triton::engines::symbolic::SharedSymbolicVariable& symVar, const triton::uint512& value);



        /* Solver engine API ============================================================================= */

        /*!
         * \brief [**solver api**] - Computes and returns a model from a symbolic constraint.
         *
         * \details
         * **item1**: symbolic variable id<br>
         * **item2**: model
         */
        TRITON_EXPORT std::map<triton::uint32, triton::engines::solver::SolverModel> getModel(const triton::ast::SharedAbstractNode& node) const;

        /*!
         * \brief [**solver api**] - Computes and returns several models from a symbolic constraint. The `limit` is the number of models returned.
         *
         * \details
         * **item1**: symbolic variable id<br>
         * **item2**: model
         */
        TRITON_EXPORT std::vector<std::map<triton::uint32, triton::engines::solver::SolverModel>> getModels(const triton::ast::SharedAbstractNode& node, triton::uint32 limit) const;

        //! Returns true if an expression is satisfiable.
        TRITON_EXPORT bool isSat(const triton::ast::SharedAbstractNode& node) const;

        //! Returns the kind of solver as triton::engines::solver::solver_e.
        TRITON_EXPORT triton::engines::solver::solver_e getSolver(void) const;

        //! Returns the instance of the initialized solver
        TRITON_EXPORT const triton::engines::solver::SolverInterface* getSolverInstance(void) const;

        //! Initializes a predefined solver.
        TRITON_EXPORT void setSolver(triton::engines::solver::solver_e kind);

        //! Initializes a custom solver.
        TRITON_EXPORT void setCustomSolver(triton::engines::solver::SolverInterface* customSolver);

        //! Returns true if the solver is valid.
        TRITON_EXPORT bool isSolverValid(void) const;

        //! [**solver api**] - Evaluates a Triton's AST via Z3 and returns a concrete value.
        TRITON_EXPORT triton::uint512 evaluateAstViaZ3(const triton::ast::SharedAbstractNode& node) const;

        //! [**solver api**] - Converts a Triton's AST to a Z3's AST, perform a Z3 simplification and returns a Triton's AST.
        TRITON_EXPORT triton::ast::SharedAbstractNode processZ3Simplification(const triton::ast::SharedAbstractNode& node) const;



        /* Taint engine API ============================================================================== */

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

        //! [**taint api**] - Taints MemoryImmediate with union. Returns true if the memDst is TAINTED.
        TRITON_EXPORT bool taintUnion(const triton::arch::MemoryAccess& memDst, const triton::arch::Immediate& imm);

        //! [**taint api**] - Taints MemoryMemory with union. Returns true if the memDst or memSrc are TAINTED.
        TRITON_EXPORT bool taintUnion(const triton::arch::MemoryAccess& memDst, const triton::arch::MemoryAccess& memSrc);

        //! [**taint api**] - Taints MemoryRegister with union. Returns true if the memDst or regSrc are TAINTED.
        TRITON_EXPORT bool taintUnion(const triton::arch::MemoryAccess& memDst, const triton::arch::Register& regSrc);

        //! [**taint api**] - Taints RegisterImmediate with union. Returns true if the regDst is TAINTED.
        TRITON_EXPORT bool taintUnion(const triton::arch::Register& regDst, const triton::arch::Immediate& imm);

        //! [**taint api**] - Taints RegisterMemory with union. Returns true if the regDst or memSrc are TAINTED.
        TRITON_EXPORT bool taintUnion(const triton::arch::Register& regDst, const triton::arch::MemoryAccess& memSrc);

        //! [**taint api**] - Taints RegisterRegister with union. Returns true if the regDst or regSrc are TAINTED.
        TRITON_EXPORT bool taintUnion(const triton::arch::Register& regDst, const triton::arch::Register& regSrc);

        //! [**taint api**] - Abstract assignment tainting.
        TRITON_EXPORT bool taintAssignment(const triton::arch::OperandWrapper& op1, const triton::arch::OperandWrapper& op2);

        //! [**taint api**] - Taints MemoryImmediate with assignment. Returns always false.
        TRITON_EXPORT bool taintAssignment(const triton::arch::MemoryAccess& memDst, const triton::arch::Immediate& imm);

        //! [**taint api**] - Taints MemoryMemory with assignment. Returns true if the memDst is tainted.
        TRITON_EXPORT bool taintAssignment(const triton::arch::MemoryAccess& memDst, const triton::arch::MemoryAccess& memSrc);

        //! [**taint api**] - Taints MemoryRegister with assignment. Returns true if the memDst is tainted.
        TRITON_EXPORT bool taintAssignment(const triton::arch::MemoryAccess& memDst, const triton::arch::Register& regSrc);

        //! [**taint api**] - Taints RegisterImmediate with assignment. Returns always false.
        TRITON_EXPORT bool taintAssignment(const triton::arch::Register& regDst, const triton::arch::Immediate& imm);

        //! [**taint api**] - Taints RegisterMemory with assignment. Returns true if the regDst is tainted.
        TRITON_EXPORT bool taintAssignment(const triton::arch::Register& regDst, const triton::arch::MemoryAccess& memSrc);

        //! [**taint api**] - Taints RegisterRegister with assignment. Returns true if the regDst is tainted.
        TRITON_EXPORT bool taintAssignment(const triton::arch::Register& regDst, const triton::arch::Register& regSrc);
    };

/*! @} End of triton namespace */
};

#endif /* TRITON_API_H */
