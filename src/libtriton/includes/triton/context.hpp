//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_CONTEXT_H
#define TRITON_CONTEXT_H

#include <triton/architecture.hpp>
#include <triton/ast.hpp>
#include <triton/astContext.hpp>
#include <triton/astRepresentation.hpp>
#include <triton/basicBlock.hpp>
#include <triton/callbacks.hpp>
#include <triton/dllexport.hpp>
#include <triton/immediate.hpp>
#include <triton/instruction.hpp>
#include <triton/irBuilder.hpp>
#include <triton/liftingEngine.hpp>
#include <triton/memoryAccess.hpp>
#include <triton/modes.hpp>
#include <triton/operandWrapper.hpp>
#include <triton/register.hpp>
#include <triton/shortcutRegister.hpp>
#include <triton/solverEngine.hpp>
#include <triton/solverEnums.hpp>
#include <triton/symbolicEngine.hpp>
#include <triton/synthesizer.hpp>
#include <triton/taintEngine.hpp>
#include <triton/tritonTypes.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

    /*! \class Context
     *  \brief This is the main Triton Context class. */
    class Context {
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

        //! Raises an exception if the lifting engine is not initialized.
        inline void checkLifting(void) const;


      protected:
        //! The Callbacks interface.
        triton::callbacks::Callbacks callbacks;

        //! The architecture entry.
        triton::arch::Architecture arch;

        //! The modes.
        triton::modes::SharedModes modes;

        //! The lifting engine.
        triton::engines::lifters::LiftingEngine* lifting = nullptr;

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

        //! Constructor of the Context.
        TRITON_EXPORT Context();

        //! Constructor of the Context.
        TRITON_EXPORT Context(triton::arch::architecture_e arch);

        //! Destructor of the Context.
        TRITON_EXPORT ~Context();



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

        //! [**architecture api**] - Returns Register from its name.
        TRITON_EXPORT const triton::arch::Register& getRegister(const std::string& name) const;

        //! [**architecture api**] - Returns parent Register from a register.
        TRITON_EXPORT const triton::arch::Register& getParentRegister(const triton::arch::Register& reg) const;

        //! [**architecture api**] - Returns parent Register from regId.
        TRITON_EXPORT const triton::arch::Register& getParentRegister(triton::arch::register_e id) const;

        //! [**architecture api**] - Returns true if the regId is a register or a flag. \sa triton::arch::x86::register_e.
        TRITON_EXPORT bool isRegisterValid(triton::arch::register_e regId) const;

        //! [**architecture api**] - Returns true if the regId is a register or a flag.
        TRITON_EXPORT bool isRegisterValid(const triton::arch::Register& reg) const;

        //! [**architecture api**] - Returns true if the execution mode is Thumb. Only useful for Arm32.
        TRITON_EXPORT bool isThumb(void) const;

        //! [**architecture api**] - Sets CPU state to Thumb mode.
        TRITON_EXPORT void setThumb(bool state);

        //! [**architecture api**] - Returns the bit in byte of the General Purpose Registers.
        TRITON_EXPORT triton::uint32 getGprBitSize(void) const;

        //! [**architecture api**] - Returns the size in byte of the General Purpose Registers.
        TRITON_EXPORT triton::uint32 getGprSize(void) const;

        //! [**architecture api**] - Returns the number of registers according to the CPU architecture.
        TRITON_EXPORT triton::uint32 getNumberOfRegisters(void) const;

        //! Returns a NOP instruction according to the architecture.
        TRITON_EXPORT const triton::arch::Instruction getNopInstruction(void) const;

        //! [**architecture api**] - Returns all registers. \sa triton::arch::x86::register_e.
        TRITON_EXPORT const std::unordered_map<triton::arch::register_e, const triton::arch::Register>& getAllRegisters(void) const;

        //! [**architecture api**] - Returns all memory.
        TRITON_EXPORT const std::unordered_map<triton::uint64, triton::uint8, IdentityHash<triton::uint64>>& getConcreteMemory(void) const;

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
        TRITON_EXPORT void setConcreteMemoryValue(triton::uint64 addr, triton::uint8 value, bool execCallbacks=true);

        /*!
         * \brief [**architecture api**] - Sets the concrete value of memory cells.
         *
         * \details Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        TRITON_EXPORT void setConcreteMemoryValue(const triton::arch::MemoryAccess& mem, const triton::uint512& value, bool execCallbacks=true);

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a memory area.
         *
         * \details Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        TRITON_EXPORT void setConcreteMemoryAreaValue(triton::uint64 baseAddr, const std::vector<triton::uint8>& values, bool execCallbacks=true);

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a memory area.
         *
         * \details Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        TRITON_EXPORT void setConcreteMemoryAreaValue(triton::uint64 baseAddr, const void* area, triton::usize size, bool execCallbacks=true);

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a register.
         *
         * \details Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        TRITON_EXPORT void setConcreteRegisterValue(const triton::arch::Register& reg, const triton::uint512& value, bool execCallbacks=true);

        //! [**architecture api**] - Defines a concrete state.
        TRITON_EXPORT void setConcreteState(triton::arch::Architecture& other);

        //! Returns true if memory cells have a defined concrete value
        TRITON_EXPORT bool isConcreteMemoryValueDefined(const triton::arch::MemoryAccess& mem) const;

        //! Returns true if memory cells have a defined concrete value
        TRITON_EXPORT bool isConcreteMemoryValueDefined(triton::uint64 baseAddr, triton::usize size=1) const;

        //! Clears concrete values assigned to the memory cells
        TRITON_EXPORT void clearConcreteMemoryValue(const triton::arch::MemoryAccess& mem);

        //! Clears concrete values assigned to the memory cells
        TRITON_EXPORT void clearConcreteMemoryValue(triton::uint64 baseAddr, triton::usize size=1);

        //! [**architecture api**] - Disassembles the instruction and setup operands.
        TRITON_EXPORT void disassembly(triton::arch::Instruction& inst) const;

        //! [**architecture api**] - Disassembles a block of instructions. You must define an architecture before.
        TRITON_EXPORT void disassembly(triton::arch::BasicBlock& block, triton::uint64 addr=0) const;

        //! [**architecture api**] - Disassembles a concrete memory area and returns a list of at most `count` disassembled instructions.
        TRITON_EXPORT std::vector<triton::arch::Instruction> disassembly(triton::uint64 addr, triton::usize count) const;

        //! [**architecture api**] - Disassembles a concrete memory area from `addr` until 'filterCallback' returns false. The function returns a 'BasicBlock'
        TRITON_EXPORT triton::arch::BasicBlock disassembly(triton::uint64 addr, bool(*filterCallback)(std::vector<triton::arch::Instruction>&)) const;

        //! [**architecture api**] - Disassembles a concrete memory area from `addr` to control flow instruction and returns a `BasicBlock`.
        TRITON_EXPORT triton::arch::BasicBlock disassembly(triton::uint64 addr) const;



        /* Processing API ================================================================================ */

        //! [**proccesing api**] - Processes an instruction and updates engines according to the instruction semantics. Returns `triton::arch::NO_FAULT` if succeed.
        TRITON_EXPORT triton::arch::exception_e processing(triton::arch::Instruction& inst);

        //! [**proccesing api**] - Processes a block of instructions and updates engines according to instructions semantics. Returns `triton::arch::NO_FAULT` if succeed.
        TRITON_EXPORT triton::arch::exception_e processing(triton::arch::BasicBlock& block, triton::uint64 addr=0);

        //! [**proccesing api**] - Initializes everything.
        TRITON_EXPORT void initEngines(void);

        //! [**proccesing api**] - Removes everything.
        TRITON_EXPORT void removeEngines(void);

        //! [**proccesing api**] - Resets everything.
        TRITON_EXPORT void reset(void);



        /* IR API ======================================================================================== */

        //! [**IR builder api**] - Builds the instruction semantics. Returns `triton::arch::NO_FAULT` if succeed.
        TRITON_EXPORT triton::arch::exception_e buildSemantics(triton::arch::Instruction& inst);

        //! [**IR builder api**] - Builds the instructions semantics of a block. Returns `triton::arch::NO_FAULT` if succeed.
        TRITON_EXPORT triton::arch::exception_e buildSemantics(triton::arch::BasicBlock& block);

        //! [**IR builder api**] - Returns the AST context. Used as AST builder.
        TRITON_EXPORT triton::ast::SharedAstContext getAstContext(void);



        /* AST Representation API ======================================================================== */

        //! [**AST representation api**] - Returns the AST representation as triton::ast::representation_e.
        TRITON_EXPORT triton::ast::representations::mode_e getAstRepresentationMode(void) const;

        //! [**AST representation api**] - Sets the AST representation.
        TRITON_EXPORT void setAstRepresentationMode(triton::ast::representations::mode_e mode);



        /* Callbacks API ================================================================================= */

        //! [**callbacks api**] - Adds a callback.
        template <typename T> void addCallback(triton::callbacks::callback_e kind, T cb) {
          this->callbacks.addCallback(kind, cb);
        }

        //! [**callbacks api**] - Removes a callback.
        template <typename T> void removeCallback(triton::callbacks::callback_e kind, T cb) {
          this->callbacks.removeCallback(kind, cb);
        }

        //! [**callbacks api**] - Clears recorded callbacks.
        TRITON_EXPORT void clearCallbacks(void);

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

        //! [**modes api**] - Clears recorded modes.
        TRITON_EXPORT void clearModes(void);



        /* Symbolic engine API =========================================================================== */

        //! [**symbolic api**] - Returns the instance of the symbolic engine.
        TRITON_EXPORT triton::engines::symbolic::SymbolicEngine* getSymbolicEngine(void);

        //! [**symbolic api**] - Returns the map of symbolic registers defined.
        TRITON_EXPORT std::unordered_map<triton::arch::register_e, triton::engines::symbolic::SharedSymbolicExpression> getSymbolicRegisters(void) const;

        //! [**symbolic api**] - Returns the map (<Addr : SymExpr>) of symbolic memory defined.
        TRITON_EXPORT std::unordered_map<triton::uint64, triton::engines::symbolic::SharedSymbolicExpression> getSymbolicMemory(void) const;

        //! [**symbolic api**] - Returns the symbolic expression assigned to the memory address.
        TRITON_EXPORT triton::engines::symbolic::SharedSymbolicExpression getSymbolicMemory(triton::uint64 addr) const;

        //! [**symbolic api**] - Returns the symbolic expression assigned to the parent register.
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
        TRITON_EXPORT triton::ast::SharedAbstractNode getRegisterAst(const triton::arch::Register& reg) const;

        //! [**symbolic api**] - Returns the AST corresponding to the register and defines the register as input of the instruction.
        TRITON_EXPORT triton::ast::SharedAbstractNode getRegisterAst(triton::arch::Instruction& inst, const triton::arch::Register& reg) const;

        //! [**symbolic api**] - Returns a new symbolic expression. Note that if there are simplification passes recorded, simplification will be applied.
        TRITON_EXPORT triton::engines::symbolic::SharedSymbolicExpression newSymbolicExpression(const triton::ast::SharedAbstractNode& node, const std::string& comment="");

        //! [**symbolic api**] - Returns a new symbolic variable.
        TRITON_EXPORT triton::engines::symbolic::SharedSymbolicVariable newSymbolicVariable(triton::uint32 varSize, const std::string& alias="");

        //! [**symbolic api**] - Removes the symbolic expression corresponding to the id.
        TRITON_EXPORT void removeSymbolicExpression(const triton::engines::symbolic::SharedSymbolicExpression& expr);

        //! [**symbolic api**] - Returns the new symbolic abstract expression and links this expression to the instruction.
        TRITON_EXPORT const triton::engines::symbolic::SharedSymbolicExpression& createSymbolicExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const triton::arch::OperandWrapper& dst, const std::string& comment="");

        //! [**symbolic api**] - Returns the new symbolic memory expression and links this expression to the instruction.
        TRITON_EXPORT const triton::engines::symbolic::SharedSymbolicExpression& createSymbolicMemoryExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const triton::arch::MemoryAccess& mem, const std::string& comment="");

        //! [**symbolic api**] - Returns the new symbolic register expression and links this expression to the instruction.
        TRITON_EXPORT const triton::engines::symbolic::SharedSymbolicExpression& createSymbolicRegisterExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const triton::arch::Register& reg, const std::string& comment="");

        //! [**symbolic api**] - Returns the new symbolic volatile expression and links this expression to the instruction.
        TRITON_EXPORT const triton::engines::symbolic::SharedSymbolicExpression& createSymbolicVolatileExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const std::string& comment="");

        //! [**symbolic api**] - Assigns a symbolic expression to a memory.
        TRITON_EXPORT void assignSymbolicExpressionToMemory(const triton::engines::symbolic::SharedSymbolicExpression& se, const triton::arch::MemoryAccess& mem);

        //! [**symbolic api**] - Assigns a symbolic expression to a register.
        TRITON_EXPORT void assignSymbolicExpressionToRegister(const triton::engines::symbolic::SharedSymbolicExpression& se, const triton::arch::Register& reg);

        //! [**symbolic api**] - Processes all recorded AST simplifications, uses solver's simplifications if `usingSolver` is true or LLVM is `usingLLVM` is true. Returns the simplified AST.
        TRITON_EXPORT triton::ast::SharedAbstractNode simplify(const triton::ast::SharedAbstractNode& node, bool usingSolver=false, bool usingLLVM=false) const;

        //! [**symbolic api**] - Processes a dead store elimination simplification on a given basic block. If `padding` is true, keep addresses aligned and padds with NOP instructions.
        TRITON_EXPORT triton::arch::BasicBlock simplify(const triton::arch::BasicBlock& block, bool padding=false) const;

        //! [**symbolic api**] - Returns the symbolic expression corresponding to an id.
        TRITON_EXPORT triton::engines::symbolic::SharedSymbolicExpression getSymbolicExpression(triton::usize symExprId) const;

        //! [**symbolic api**] - Returns the symbolic variable corresponding to the symbolic variable id.
        TRITON_EXPORT triton::engines::symbolic::SharedSymbolicVariable getSymbolicVariable(triton::usize symVarId) const;

        //! [**symbolic api**] - Returns the symbolic variable corresponding to the symbolic variable name.
        TRITON_EXPORT triton::engines::symbolic::SharedSymbolicVariable getSymbolicVariable(const std::string& symVarName) const;

        //! [**symbolic api**] - Returns the logical conjunction vector of path constraints.
        TRITON_EXPORT const std::vector<triton::engines::symbolic::PathConstraint>& getPathConstraints(void) const;

        //! [**symbolic api**] - Returns the logical conjunction vector of path constraints from a given range.
        TRITON_EXPORT std::vector<triton::engines::symbolic::PathConstraint> getPathConstraints(triton::usize start, triton::usize end) const;

        //! [**symbolic api**] - Returns the logical conjunction vector of path constraint of a given thread.
        TRITON_EXPORT std::vector<triton::engines::symbolic::PathConstraint> getPathConstraintsOfThread(triton::uint32 threadId) const;

        //! [**symbolic api**] - Returns the current path predicate as an AST of logical conjunction of each taken branch.
        TRITON_EXPORT triton::ast::SharedAbstractNode getPathPredicate(void);

        //! [**symbolic api**] - Returns path predicates which may reach the targeted address.
        TRITON_EXPORT std::vector<triton::ast::SharedAbstractNode> getPredicatesToReachAddress(triton::uint64 addr);

        //! [**symbolic api**] - Returns the size of the path constraints
        TRITON_EXPORT triton::usize getSizeOfPathConstraints(void) const;

        //! [**symbolic api**] - Pushes constraint created from node to the current path predicate.
        TRITON_EXPORT void pushPathConstraint(const triton::ast::SharedAbstractNode& node, const std::string& comment="");

        //! [**symbolic api**] - Pushes constraint to the current path predicate.
        TRITON_EXPORT void pushPathConstraint(const triton::engines::symbolic::PathConstraint& pco);

        //! [**symbolic api**] - Pops the last constraints added to the path predicate.
        TRITON_EXPORT void popPathConstraint(void);

        //! [**symbolic api**] - Clears the current path predicate.
        TRITON_EXPORT void clearPathConstraints(void);

        //! [**symbolic api**] - Returns true if the symbolic expression ID exists.
        TRITON_EXPORT bool isSymbolicExpressionExists(triton::usize symExprId) const;

        //! [**symbolic api**] - Returns true if memory cell expressions contain symbolic variables.
        TRITON_EXPORT bool isMemorySymbolized(const triton::arch::MemoryAccess& mem) const;

        //! [**symbolic api**] - Returns true if memory cell expressions contain symbolic variables.
        TRITON_EXPORT bool isMemorySymbolized(triton::uint64 addr, triton::uint32 size=1) const;

        //! [**symbolic api**] - Returns true if the register expression contains a symbolic variable.
        TRITON_EXPORT bool isRegisterSymbolized(const triton::arch::Register& reg) const;

        //! [**symbolic api**] - Converts a symbolic expression to a symbolic variable. `symVarSize` must be in bits.
        TRITON_EXPORT triton::engines::symbolic::SharedSymbolicVariable symbolizeExpression(triton::usize exprId, triton::uint32 symVarSize, const std::string& symVarAlias="");

        //! [**symbolic api**] - Converts a symbolic memory expression to a symbolic variable.
        TRITON_EXPORT triton::engines::symbolic::SharedSymbolicVariable symbolizeMemory(const triton::arch::MemoryAccess& mem, const std::string& symVarAlias="");

        //! [**symbolic api**] - Converts a symbolic memory area to 8-bits symbolic variables.
        TRITON_EXPORT void symbolizeMemory(triton::uint64 addr, triton::usize size);

        //! [**symbolic api**] - Converts a symbolic register expression to a symbolic variable.
        TRITON_EXPORT triton::engines::symbolic::SharedSymbolicVariable symbolizeRegister(const triton::arch::Register& reg, const std::string& symVarAlias="");

        //! [**symbolic api**] - Concretizes all symbolic memory cells.
        TRITON_EXPORT void concretizeAllMemory(void);

        //! [**symbolic api**] - Concretizes all symbolic register.
        TRITON_EXPORT void concretizeAllRegister(void);

        //! [**symbolic api**] - Concretizes symbolic memory cells.
        TRITON_EXPORT void concretizeMemory(const triton::arch::MemoryAccess& mem);

        //! [**symbolic api**] - Concretizes a symbolic memory cell.
        TRITON_EXPORT void concretizeMemory(triton::uint64 addr);

        //! [**symbolic api**] - Concretizes a symbolic register.
        TRITON_EXPORT void concretizeRegister(const triton::arch::Register& reg);

        //! [**symbolic api**] - Initializes the effective address of a memory access.
        TRITON_EXPORT void initLeaAst(triton::arch::MemoryAccess& mem, bool force=true) const;

        //! [**symbolic api**] - Slices all expressions from a given one.
        TRITON_EXPORT std::unordered_map<triton::usize, triton::engines::symbolic::SharedSymbolicExpression> sliceExpressions(const triton::engines::symbolic::SharedSymbolicExpression& expr);

        //! [**symbolic api**] - Returns the list of the tainted symbolic expressions.
        TRITON_EXPORT std::vector<triton::engines::symbolic::SharedSymbolicExpression> getTaintedSymbolicExpressions(void) const;

        //! [**symbolic api**] - Returns all symbolic expressions as a map of <SymExprId : SymExpr>
        TRITON_EXPORT std::unordered_map<triton::usize, triton::engines::symbolic::SharedSymbolicExpression> getSymbolicExpressions(void) const;

        //! [**symbolic api**] - Returns all symbolic variables as a map of <SymVarId : SymVar>
        TRITON_EXPORT std::map<triton::usize, triton::engines::symbolic::SharedSymbolicVariable> getSymbolicVariables(void) const;

        //! [**symbolic api**] - Gets the concrete value of a symbolic variable.
        TRITON_EXPORT triton::uint512 getConcreteVariableValue(const triton::engines::symbolic::SharedSymbolicVariable& symVar) const;

        //! [**symbolic api**] - Sets the concrete value of a symbolic variable.
        TRITON_EXPORT void setConcreteVariableValue(const triton::engines::symbolic::SharedSymbolicVariable& symVar, const triton::uint512& value);



        /* Solver engine API ============================================================================= */

        /*!
         * \brief [**solver api**] - Computes and returns a model from a symbolic constraint. State is returned in the `status` pointer as well as the solving time. A `timeout` can also be defined.
         *
         * \details
         * **item1**: symbolic variable id<br>
         * **item2**: model
         */
        TRITON_EXPORT std::unordered_map<triton::usize, triton::engines::solver::SolverModel> getModel(const triton::ast::SharedAbstractNode& node, triton::engines::solver::status_e* status = nullptr, triton::uint32 timeout = 0, triton::uint32* solvingTime = nullptr) const;

        /*!
         * \brief [**solver api**] - Computes and returns several models from a symbolic constraint. The `limit` is the number of models returned. State is returned in the `status` pointer as well as the solving time. A `timeout` can also be defined.
         *
         * \details
         * **item1**: symbolic variable id<br>
         * **item2**: model
         */
        TRITON_EXPORT std::vector<std::unordered_map<triton::usize, triton::engines::solver::SolverModel>> getModels(const triton::ast::SharedAbstractNode& node, triton::uint32 limit, triton::engines::solver::status_e* status = nullptr, triton::uint32 timeout = 0, triton::uint32* solvingTime = nullptr) const;

        //! Returns true if an expression is satisfiable.
        TRITON_EXPORT bool isSat(const triton::ast::SharedAbstractNode& node, triton::engines::solver::status_e* status = nullptr, triton::uint32 timeout = 0, triton::uint32* solvingTime = nullptr) const;

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

        //! [**solver api**] - Evaluates a Triton's AST via the solver and returns a concrete value.
        TRITON_EXPORT triton::uint512 evaluateAstViaSolver(const triton::ast::SharedAbstractNode& node) const;

        //! [**solver api**] - Converts a Triton's AST to a solver's AST, perform a simplification and returns a Triton's AST.
        TRITON_EXPORT triton::ast::SharedAbstractNode simplifyAstViaSolver(const triton::ast::SharedAbstractNode& node) const;

        //! [**solver api**] - Defines a solver timeout (in milliseconds).
        TRITON_EXPORT void setSolverTimeout(triton::uint32 ms);

        //! [**solver api**] - Defines a solver memory consumption limit (in megabytes).
        TRITON_EXPORT void setSolverMemoryLimit(triton::uint32 limit);



        /* Taint engine API ============================================================================== */

        //! [**taint api**] - Returns the instance of the taint engine.
        TRITON_EXPORT triton::engines::taint::TaintEngine* getTaintEngine(void);

        //! [**taint api**] - Returns the tainted addresses.
        TRITON_EXPORT const std::unordered_set<triton::uint64>& getTaintedMemory(void) const;

        //! [**taint api**] - Returns the tainted registers.
        TRITON_EXPORT std::unordered_set<const triton::arch::Register*> getTaintedRegisters(void) const;

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



        /* Synthesizer engine API ============================================================================== */

        //! [**synthesizer api**] - Synthesizes a given node. If `constant` is true, performa a constant synthesis. If `opaque` is true, perform opaque constant synthesis. If `subexpr` is true, analyze children AST.
        TRITON_EXPORT triton::engines::synthesis::SynthesisResult synthesize(const triton::ast::SharedAbstractNode& node, bool constant=true, bool subexpr=true, bool opaque=false);



        /* Lifters engine API ================================================================================= */

        //! [**lifting api**] - Lifts an AST and all its references to LLVM format. `fname` represents the name of the LLVM function.
        TRITON_EXPORT std::ostream& liftToLLVM(std::ostream& stream, const triton::ast::SharedAbstractNode& node, const char* fname="__triton", bool optimize=false);

        //! [**lifting api**] - Lifts a symbolic expression and all its references to LLVM format. `fname` represents the name of the LLVM function.
        TRITON_EXPORT std::ostream& liftToLLVM(std::ostream& stream, const triton::engines::symbolic::SharedSymbolicExpression& expr, const char* fname="__triton", bool optimize=false);

        //! [**lifting api**] - Lifts a symbolic expression and all its references to Python format. If `icomment` is true, then print instructions assembly in expression comments.
        TRITON_EXPORT std::ostream& liftToPython(std::ostream& stream, const triton::engines::symbolic::SharedSymbolicExpression& expr, bool icomment=false);

        //! [**lifting api**] - Lifts a symbolic expression and all its references to SMT format. If `assert_` is true, then (assert <expr>). If `icomment` is true, then print instructions assembly in expression comments.
        TRITON_EXPORT std::ostream& liftToSMT(std::ostream& stream, const triton::engines::symbolic::SharedSymbolicExpression& expr, bool assert_=false, bool icomment=false);

        //! [**lifting api**] - Lifts an AST and all its references to Dot format.
        TRITON_EXPORT std::ostream& liftToDot(std::ostream& stream, const triton::ast::SharedAbstractNode& node);

        //! [**lifting api**] - Lifts a symbolic expression and all its references to Dot format.
        TRITON_EXPORT std::ostream& liftToDot(std::ostream& stream, const triton::engines::symbolic::SharedSymbolicExpression& expr);

        //! [**lifting api**] - Lifts and simplify an AST using LLVM
        TRITON_EXPORT triton::ast::SharedAbstractNode simplifyAstViaLLVM(const triton::ast::SharedAbstractNode& node) const;
    };

/*! @} End of triton namespace */
};

#endif /* TRITON_CONTEXT_H */
