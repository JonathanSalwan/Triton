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
#include <triton/astGarbageCollector.hpp>
#include <triton/astRepresentation.hpp>
#include <triton/callbacks.hpp>
#include <triton/immediate.hpp>
#include <triton/instruction.hpp>
#include <triton/irBuilder.hpp>
#include <triton/memoryAccess.hpp>
#include <triton/modes.hpp>
#include <triton/operandWrapper.hpp>
#include <triton/register.hpp>
#include <triton/registerSpecification.hpp>
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
        triton::modes::Modes* modes = nullptr;

        //! The taint engine.
        triton::engines::taint::TaintEngine* taint = nullptr;

        //! The symbolic engine.
        triton::engines::symbolic::SymbolicEngine* symbolic = nullptr;

        //! The solver engine.
        triton::engines::solver::SolverEngine* solver = nullptr;

        //! The AST garbage collector interface.
        triton::ast::AstGarbageCollector* astGarbageCollector = nullptr;

        //! The IR builder.
        triton::arch::IrBuilder* irBuilder = nullptr;

        //! The Z3 interface between Triton and Z3
        triton::ast::Z3Interface* z3Interface = nullptr;


      public:
        //! Constructor of the API.
        API();

        //! Destructor of the API.
        virtual ~API();



        /* Architecture API ============================================================================== */

        //! [**Architecture api**] - Returns true if the architecture is valid.
        bool isArchitectureValid(void) const;

        //! [**architecture api**] - Returns the architecture as triton::arch::architectures_e.
        triton::uint32 getArchitecture(void) const;

        //! [**architecture api**] - Raises an exception if the architecture is not initialized.
        void checkArchitecture(void) const;

        //! [**architecture api**] - Returns the CPU instance.
        triton::arch::CpuInterface* getCpu(void);

        //! [**architecture api**] - Setup an architecture. \sa triton::arch::architectures_e.
        void setArchitecture(triton::uint32 arch);

        //! [**architecture api**] - Clears the architecture states (registers and memory).
        void clearArchitecture(void);

        //! [**architecture api**] - Returns true if the register id is a flag. \sa triton::arch::x86::registers_e.
        bool isFlag(triton::uint32 regId) const;

        //! [**architecture api**] - Returns true if the register id is a flag.
        bool isFlag(const triton::arch::Register& reg) const;

        //! [**architecture api**] - Returns true if the regId is a register. \sa triton::arch::x86::registers_e.
        bool isRegister(triton::uint32 regId) const;

        //! [**architecture api**] - Returns true if the regId is a register.
        bool isRegister(const triton::arch::Register& reg) const;

        //! [**architecture api**] - Returns true if the regId is a register or a flag. \sa triton::arch::x86::registers_e.
        bool isRegisterValid(triton::uint32 regId) const;

        //! [**architecture api**] - Returns true if the regId is a register or a flag.
        bool isRegisterValid(const triton::arch::Register& reg) const;

        //! [**architecture api**] - Returns the max size (in bit) of the CPU register (GPR).
        triton::uint32 getRegisterBitSize(void) const;

        //! [**architecture api**] - Returns the max size (in byte) of the CPU register (GPR).
        triton::uint32 getRegisterSize(void) const;

        //! [**architecture api**] - Returns the number of registers according to the CPU architecture.
        triton::uint32 getNumberOfRegisters(void) const;

        //! [**architecture api**] - Returns all information about the register.
        triton::arch::RegisterSpecification getRegisterSpecification(triton::uint32 regId) const;

        //! [**architecture api**] - Returns all registers. \sa triton::arch::x86::registers_e.
        std::set<triton::arch::Register*> getAllRegisters(void) const;

        //! [**architecture api**] - Returns all parent registers. \sa triton::arch::x86::registers_e.
        std::set<triton::arch::Register*> getParentRegisters(void) const;

        //! [**architecture api**] - Returns the concrete value of a memory cell.
        triton::uint8 getConcreteMemoryValue(triton::uint64 addr) const;

        //! [**architecture api**] - Returns the concrete value of memory cells.
        triton::uint512 getConcreteMemoryValue(const triton::arch::MemoryAccess& mem, bool execCallbacks=true) const;

        //! [**architecture api**] - Returns the concrete value of a memory area.
        std::vector<triton::uint8> getConcreteMemoryAreaValue(triton::uint64 baseAddr, triton::usize size, bool execCallbacks=true) const;

        //! [**architecture api**] - Returns the concrete value of a register.
        triton::uint512 getConcreteRegisterValue(const triton::arch::Register& reg, bool execCallbacks=true) const;

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a memory cell.
         *
         * \description Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        void setConcreteMemoryValue(triton::uint64 addr, triton::uint8 value);

        /*!
         * \brief [**architecture api**] - Sets the concrete value of memory cells.
         *
         * \description Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        void setConcreteMemoryValue(const triton::arch::MemoryAccess& mem);

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a memory area.
         *
         * \description Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        void setConcreteMemoryAreaValue(triton::uint64 baseAddr, const std::vector<triton::uint8>& values);

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a memory area.
         *
         * \description Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        void setConcreteMemoryAreaValue(triton::uint64 baseAddr, const triton::uint8* area, triton::usize size);

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a register.
         *
         * \description Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        void setConcreteRegisterValue(const triton::arch::Register& reg);

        //! [**architecture api**] - Returns true if the range `[baseAddr:size]` is mapped into the internal memory representation. \sa getConcreteMemoryValue() and getConcreteMemoryAreaValue().
        bool isMemoryMapped(triton::uint64 baseAddr, triton::usize size=1);

        //! [**architecture api**] - Removes the range `[baseAddr:size]` from the internal memory representation. \sa isMemoryMapped().
        void unmapMemory(triton::uint64 baseAddr, triton::usize size=1);

        //! [**architecture api**] - Disassembles the instruction and setup operands. You must define an architecture before. \sa processing().
        void disassembly(triton::arch::Instruction& inst) const;



        /* Processing API ================================================================================ */

        //! [**proccesing api**] - Processes an instruction and updates engines according to the instruction semantics. Returns true if the instruction is supported.
        bool processing(triton::arch::Instruction& inst);

        //! [**proccesing api**] - Initialize everything.
        void initEngines(void);

        //! [**proccesing api**] - Remove everything.
        void removeEngines(void);

        //! [**proccesing api**] - Reset everything.
        void resetEngines(void);



        /* IR API ======================================================================================== */

        //! [**IR builder api**] - Raises an exception if the IR builder is not initialized.
        void checkIrBuilder(void) const;

        //! [**IR builder api**] - Builds the instruction semantics. Returns true if the instruction is supported. You must define an architecture before. \sa processing().
        bool buildSemantics(triton::arch::Instruction& inst);



        /* AST Garbage Collector API ===================================================================== */

        //! [**AST garbage collector api**] - Raises an exception if the AST garbage collector interface is not initialized.
        void checkAstGarbageCollector(void) const;

        //! [**AST garbage collector api**] - Go through every allocated nodes and free them.
        void freeAllAstNodes(void);

        //! [**AST garbage collector api**] - Frees a set of nodes and removes them from the global container.
        void freeAstNodes(std::set<triton::ast::AbstractNode*>& nodes);

        //! [**AST garbage collector api**] - Extracts all unique nodes from a partial AST into the uniqueNodes set.
        void extractUniqueAstNodes(std::set<triton::ast::AbstractNode*>& uniqueNodes, triton::ast::AbstractNode* root) const;

        //! [**AST garbage collector api**] - Records the allocated node or returns the same node if it already exists inside the dictionaries.
        triton::ast::AbstractNode* recordAstNode(triton::ast::AbstractNode* node);

        //! [**AST garbage collector api**] - Records a variable AST node.
        void recordVariableAstNode(const std::string& name, triton::ast::AbstractNode* node);

        //! [**AST garbage collector api**] - Returns all allocated nodes.
        const std::set<triton::ast::AbstractNode*>& getAllocatedAstNodes(void) const;

        //! [**AST garbage collector api**] - Returns all stats about AST Dictionaries.
        std::map<std::string, triton::usize> getAstDictionariesStats(void) const;

        //! [**AST garbage collector api**] - Returns all variable nodes recorded.
        const std::map<std::string, triton::ast::AbstractNode*>& getAstVariableNodes(void) const;

        //! [**AST garbage collector api**] - Returns the node of a recorded variable.
        triton::ast::AbstractNode* getAstVariableNode(const std::string& name) const;

        //! [**AST garbage collector api**] - Sets all allocated nodes.
        void setAllocatedAstNodes(const std::set<triton::ast::AbstractNode*>& nodes);

        //! [**AST garbage collector api**] - Sets all variable nodes recorded.
        void setAstVariableNodes(const std::map<std::string, triton::ast::AbstractNode*>& nodes);



        /* AST Representation API ======================================================================== */

        //! [**AST representation api**] - Returns the AST representation mode as triton::ast::representations::mode_e.
        triton::uint32 getAstRepresentationMode(void) const;

        //! [**AST representation api**] - Sets the AST representation mode.
        void setAstRepresentationMode(triton::uint32 mode);



        /* Callbacks API ================================================================================= */

        //! [**callbacks api**] - Adds a GET_CONCRETE_MEMORY_VALUE callback.
        void addCallback(triton::callbacks::getConcreteMemoryValueCallback cb);

        //! [**callbacks api**] - Adds a GET_CONCRETE_REGISTER_VALUE callback.
        void addCallback(triton::callbacks::getConcreteRegisterValueCallback cb);

        //! [**callbacks api**] - Adds a SYMBOLIC_SIMPLIFICATION callback.
        void addCallback(triton::callbacks::symbolicSimplificationCallback cb);

        //! [**callbacks api**] - Removes all recorded callbacks.
        void removeAllCallbacks(void);

        //! [**callbacks api**] - Deletes a GET_CONCRETE_MEMORY_VALUE callback.
        void removeCallback(triton::callbacks::getConcreteMemoryValueCallback cb);

        //! [**callbacks api**] - Deletes a GET_CONCRETE_REGISTER_VALUE callback.
        void removeCallback(triton::callbacks::getConcreteRegisterValueCallback cb);

        //! [**callbacks api**] - Deletes a SYMBOLIC_SIMPLIFICATION callback.
        void removeCallback(triton::callbacks::symbolicSimplificationCallback cb);

        //! [**callbacks api**] - Processes callbacks according to the kind and the C++ polymorphism.
        triton::ast::AbstractNode* processCallbacks(triton::callbacks::callback_e kind, triton::ast::AbstractNode* node) const;

        //! [**callbacks api**] - Processes callbacks according to the kind and the C++ polymorphism.
        void processCallbacks(triton::callbacks::callback_e kind, const triton::arch::MemoryAccess& mem) const;

        //! [**callbacks api**] - Processes callbacks according to the kind and the C++ polymorphism.
        void processCallbacks(triton::callbacks::callback_e kind, const triton::arch::Register& reg) const;



        /* Modes API====================================================================================== */

        //! [**modes api**] - Raises an exception if modes interface is not initialized.
        void checkModes(void) const;

        //! [**modes api**] - Enables or disables a specific mode.
        void enableMode(enum triton::modes::mode_e mode, bool flag);

        //! [**modes api**] - Returns true if the mode is enabled.
        bool isModeEnabled(enum triton::modes::mode_e mode) const;



        /* Symbolic engine API =========================================================================== */

        //! [**symbolic api**] - Raises an exception if the symbolic engine is not initialized.
        void checkSymbolic(void) const;

        //! [**symbolic api**] - Returns the instance of the symbolic engine.
        triton::engines::symbolic::SymbolicEngine* getSymbolicEngine(void);

        //! [**symbolic api**] - Returns the map of symbolic registers defined.
        std::map<triton::arch::Register, triton::engines::symbolic::SymbolicExpression*> getSymbolicRegisters(void) const;

        //! [**symbolic api**] - Returns the map (<Addr : SymExpr>) of symbolic memory defined.
        std::map<triton::uint64, triton::engines::symbolic::SymbolicExpression*> getSymbolicMemory(void) const;

        //! [**symbolic api**] - Returns the symbolic expression id corresponding to the memory address.
        triton::usize getSymbolicMemoryId(triton::uint64 addr) const;

        //! [**symbolic api**] - Returns the symbolic expression id corresponding to the register.
        triton::usize getSymbolicRegisterId(const triton::arch::Register& reg) const;

        //! [**symbolic api**] - Returns the symbolic memory value.
        triton::uint8 getSymbolicMemoryValue(triton::uint64 address);

        //! [**symbolic api**] - Returns the symbolic memory value.
        triton::uint512 getSymbolicMemoryValue(const triton::arch::MemoryAccess& mem);

        //! [**symbolic api**] - Returns the symbolic values of a memory area.
        std::vector<triton::uint8> getSymbolicMemoryAreaValue(triton::uint64 baseAddr, triton::usize size);

        //! [**symbolic api**] - Returns the symbolic register value.
        triton::uint512 getSymbolicRegisterValue(const triton::arch::Register& reg);

        //! [**symbolic api**] - Converts a symbolic expression to a symbolic variable. `symVarSize` must be in bits.
        triton::engines::symbolic::SymbolicVariable* convertExpressionToSymbolicVariable(triton::usize exprId, triton::uint32 symVarSize, const std::string& symVarComment="");

        //! [**symbolic api**] - Converts a symbolic memory expression to a symbolic variable.
        triton::engines::symbolic::SymbolicVariable* convertMemoryToSymbolicVariable(const triton::arch::MemoryAccess& mem, const std::string& symVarComment="");

        //! [**symbolic api**] - Converts a symbolic register expression to a symbolic variable.
        triton::engines::symbolic::SymbolicVariable* convertRegisterToSymbolicVariable(const triton::arch::Register& reg, const std::string& symVarComment="");

        //! [**symbolic api**] - Returns a symbolic operand.
        triton::ast::AbstractNode* buildSymbolicOperand(triton::arch::OperandWrapper& op);

        //! [**symbolic api**] - Returns a symbolic operand.
        triton::ast::AbstractNode* buildSymbolicOperand(triton::arch::Instruction& inst, triton::arch::OperandWrapper& op);

        //! [**symbolic api**] - Returns an immediate symbolic.
        triton::ast::AbstractNode* buildSymbolicImmediate(const triton::arch::Immediate& imm);

        //! [**symbolic api**] - Returns an immediate symbolic and defines the immediate as input of the instruction..
        triton::ast::AbstractNode* buildSymbolicImmediate(triton::arch::Instruction& inst, triton::arch::Immediate& imm);

        //! [**symbolic api**] - Returns a symbolic memory cell.
        triton::ast::AbstractNode* buildSymbolicMemory(const triton::arch::MemoryAccess& mem);

        //! [**symbolic api**] - Returns a symbolic memory cell and defines the memory cell as input of the instruction.
        triton::ast::AbstractNode* buildSymbolicMemory(triton::arch::Instruction& inst, triton::arch::MemoryAccess& mem);

        //! [**symbolic api**] - Returns a symbolic register.
        triton::ast::AbstractNode* buildSymbolicRegister(const triton::arch::Register& reg);

        //! [**symbolic api**] - Returns a symbolic register and defines the register as input of the instruction.
        triton::ast::AbstractNode* buildSymbolicRegister(triton::arch::Instruction& inst, triton::arch::Register& reg);

        //! [**symbolic api**] - Returns a new symbolic expression. Note that if there are simplification passes recorded, simplification will be applied.
        triton::engines::symbolic::SymbolicExpression* newSymbolicExpression(triton::ast::AbstractNode* node, const std::string& comment="");

        //! [**symbolic api**] - Returns a new symbolic variable.
        triton::engines::symbolic::SymbolicVariable* newSymbolicVariable(triton::uint32 varSize, const std::string& comment="");

        //! [**symbolic api**] - Removes the symbolic expression corresponding to the id.
        void removeSymbolicExpression(triton::usize symExprId);

        //! [**symbolic api**] - Returns the new symbolic abstract expression and links this expression to the instruction.
        triton::engines::symbolic::SymbolicExpression* createSymbolicExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, triton::arch::OperandWrapper& dst, const std::string& comment="");

        //! [**symbolic api**] - Returns the new symbolic memory expression and links this expression to the instruction.
        triton::engines::symbolic::SymbolicExpression* createSymbolicMemoryExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, triton::arch::MemoryAccess& mem, const std::string& comment="");

        //! [**symbolic api**] - Returns the new symbolic register expression and links this expression to the instruction.
        triton::engines::symbolic::SymbolicExpression* createSymbolicRegisterExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, triton::arch::Register& reg, const std::string& comment="");

        //! [**symbolic api**] - Returns the new symbolic flag expression and links this expression to the instruction.
        triton::engines::symbolic::SymbolicExpression* createSymbolicFlagExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, triton::arch::Register& flag, const std::string& comment="");

        //! [**symbolic api**] - Returns the new symbolic volatile expression and links this expression to the instruction.
        triton::engines::symbolic::SymbolicExpression* createSymbolicVolatileExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, const std::string& comment="");

        //! [**symbolic api**] - Assigns a symbolic expression to a memory.
        void assignSymbolicExpressionToMemory(triton::engines::symbolic::SymbolicExpression* se, const triton::arch::MemoryAccess& mem);

        //! [**symbolic api**] - Assigns a symbolic expression to a register.
        void assignSymbolicExpressionToRegister(triton::engines::symbolic::SymbolicExpression* se, const triton::arch::Register& reg);

        //! [**symbolic api**] - Processes all recorded simplifications. Returns the simplified node.
        triton::ast::AbstractNode* processSimplification(triton::ast::AbstractNode* node, bool z3=false) const;

        //! [**symbolic api**] - Returns the symbolic expression corresponding to an id.
        triton::engines::symbolic::SymbolicExpression* getSymbolicExpressionFromId(triton::usize symExprId) const;

        //! [**symbolic api**] - Returns the symbolic variable corresponding to the symbolic variable id.
        triton::engines::symbolic::SymbolicVariable* getSymbolicVariableFromId(triton::usize symVarId) const;

        //! [**symbolic api**] - Returns the symbolic variable corresponding to the symbolic variable name.
        triton::engines::symbolic::SymbolicVariable* getSymbolicVariableFromName(const std::string& symVarName) const;

        //! [**symbolic api**] - Returns the logical conjunction vector of path constraints.
        const std::vector<triton::engines::symbolic::PathConstraint>& getPathConstraints(void) const;

        //! [**symbolic api**] - Returns the logical conjunction AST of path constraints.
        triton::ast::AbstractNode* getPathConstraintsAst(void);

        //! [**symbolic api**] - Adds a path constraint.
        void addPathConstraint(const triton::arch::Instruction& inst, triton::engines::symbolic::SymbolicExpression* expr);

        //! [**symbolic api**] - Clears the logical conjunction vector of path constraints.
        void clearPathConstraints(void);

        //! [**symbolic api**] - Enables or disables the symbolic execution engine.
        void enableSymbolicEngine(bool flag);

        //! [**symbolic api**] - Returns true if the symbolic execution engine is enabled.
        bool isSymbolicEngineEnabled(void) const;

        //! [**symbolic api**] - Returns true if the symbolic expression ID exists.
        bool isSymbolicExpressionIdExists(triton::usize symExprId) const;

        //! [**symbolic api**] - Returns true if memory cell expressions contain symbolic variables.
        bool isMemorySymbolized(const triton::arch::MemoryAccess& mem) const;

        //! [**symbolic api**] - Returns true if memory cell expressions contain symbolic variables.
        bool isMemorySymbolized(triton::uint64 addr, triton::uint32 size=1) const;

        //! [**symbolic api**] - Returns true if the register expression contains a symbolic variable.
        bool isRegisterSymbolized(const triton::arch::Register& reg) const;

        //! [**symbolic api**] - Concretizes all symbolic memory references.
        void concretizeAllMemory(void);

        //! [**symbolic api**] - Concretizes all symbolic register references.
        void concretizeAllRegister(void);

        //! [**symbolic api**] - Concretizes a specific symbolic memory reference.
        void concretizeMemory(const triton::arch::MemoryAccess& mem);

        //! [**symbolic api**] - Concretizes a specific symbolic memory reference.
        void concretizeMemory(triton::uint64 addr);

        //! [**symbolic api**] - Concretizes a specific symbolic register reference.
        void concretizeRegister(const triton::arch::Register& reg);

        //! [**symbolic api**] - Returns the partial AST from a symbolic expression id.
        triton::ast::AbstractNode* getAstFromId(triton::usize symExprId);

        //! [**symbolic api**] - Returns the full AST of a root node.
        triton::ast::AbstractNode* getFullAst(triton::ast::AbstractNode* node);

        //! [**symbolic api**] - Returns the full AST from a symbolic expression id.
        triton::ast::AbstractNode* getFullAstFromId(triton::usize symExprId);

        //! [**symbolic api**] - Slices all expressions from a given one.
        std::map<triton::usize, triton::engines::symbolic::SymbolicExpression*> sliceExpressions(triton::engines::symbolic::SymbolicExpression* expr);

        //! [**symbolic api**] - Returns the list of the tainted symbolic expressions.
        std::list<triton::engines::symbolic::SymbolicExpression*> getTaintedSymbolicExpressions(void) const;

        //! [**symbolic api**] - Returns all symbolic expressions as a map of <SymExprId : SymExpr>
        const std::map<triton::usize, triton::engines::symbolic::SymbolicExpression*>& getSymbolicExpressions(void) const;

        //! [**symbolic api**] - Returns all symbolic variables as a map of <SymVarId : SymVar>
        const std::map<triton::usize, triton::engines::symbolic::SymbolicVariable*>& getSymbolicVariables(void) const;



        /* Solver engine API ============================================================================= */

        //! [**solver api**] - Raises an exception if the solver engine is not initialized.
        void checkSolver(void) const;

        /*!
         * \brief [**solver api**] - Computes and returns a model from a symbolic constraint.
         *
         * \description
         * **item1**: symbolic variable id<br>
         * **item2**: model
         */
        std::map<triton::uint32, triton::engines::solver::SolverModel> getModel(triton::ast::AbstractNode* node) const;

        /*!
         * \brief [**solver api**] - Computes and returns several models from a symbolic constraint. The `limit` is the number of models returned.
         *
         * \description
         * **item1**: symbolic variable id<br>
         * **item2**: model
         */
        std::list<std::map<triton::uint32, triton::engines::solver::SolverModel>> getModels(triton::ast::AbstractNode* node, triton::uint32 limit) const;



        /* Z3 interface API ============================================================================== */

        //! [**z3 api**] - Raises an exception if the z3 interface is not initialized.
        void checkZ3Interface(void) const;

        //! [**z3 api**] - Evaluates a Triton's AST via Z3 and returns a concrete value.
        triton::uint512 evaluateAstViaZ3(triton::ast::AbstractNode* node) const;

        //! [**z3 api**] - Converts a Triton's AST to a Z3's AST, perform a Z3 simplification and returns a Triton's AST.
        triton::ast::AbstractNode* processZ3Simplification(triton::ast::AbstractNode* node) const;



        /* Taint engine API ============================================================================== */

        //! [**taint api**] - Raises an exception if the taint engine is not initialized.
        void checkTaint(void) const;

        //! [**taint api**] - Returns the instance of the taint engine.
        triton::engines::taint::TaintEngine* getTaintEngine(void);

        //! [**taint api**] - Returns the tainted addresses.
        const std::set<triton::uint64>& getTaintedMemory(void) const;

        //! [**taint api**] - Returns the tainted registers.
        const std::set<triton::arch::Register>& getTaintedRegisters(void) const;

        //! [**taint api**] - Enables or disables the taint engine.
        void enableTaintEngine(bool flag);

        //! [**taint api**] - Returns true if the taint engine is enabled.
        bool isTaintEngineEnabled(void) const;

        //! [**taint api**] - Abstract taint verification. Returns true if the operand is tainted.
        bool isTainted(const triton::arch::OperandWrapper& op) const;

        //! [**taint api**] - Returns true if the address:size is tainted.
        bool isMemoryTainted(triton::uint64 addr, triton::uint32 size=1) const;

        //! [**taint api**] - Returns true if the memory is tainted.
        bool isMemoryTainted(const triton::arch::MemoryAccess& mem) const;

        //! [**taint api**] - Returns true if the register is tainted.
        bool isRegisterTainted(const triton::arch::Register& reg) const;

        //! [**taint api**] - Sets the flag (taint or untaint) to an abstract operand (Register or Memory).
        bool setTaint(const triton::arch::OperandWrapper& op, bool flag);

        //! [**taint api**] - Sets the flag (taint or untaint) to a memory.
        bool setTaintMemory(const triton::arch::MemoryAccess& mem, bool flag);

        //! [**taint api**] - Sets the flag (taint or untaint) to a register.
        bool setTaintRegister(const triton::arch::Register& reg, bool flag);

        //! [**taint api**] - Taints an address. Returns TAINTED if the address has been tainted correctly. Otherwise it returns the last defined state.
        bool taintMemory(triton::uint64 addr);

        //! [**taint api**] - Taints a memory. Returns TAINTED if the memory has been tainted correctly. Otherwise it returns the last defined state.
        bool taintMemory(const triton::arch::MemoryAccess& mem);

        //! [**taint api**] - Taints a register. Returns TAINTED if the register has been tainted correctly. Otherwise it returns the last defined state.
        bool taintRegister(const triton::arch::Register& reg);

        //! [**taint api**] - Untaints an address. Returns !TAINTED if the address has been untainted correctly. Otherwise it returns the last defined state.
        bool untaintMemory(triton::uint64 addr);

        //! [**taint api**] - Untaints a memory. Returns !TAINTED if the memory has been untainted correctly. Otherwise it returns the last defined state.
        bool untaintMemory(const triton::arch::MemoryAccess& mem);

        //! [**taint api**] - Untaints a register. Returns !TAINTED if the register has been untainted correctly. Otherwise it returns the last defined state.
        bool untaintRegister(const triton::arch::Register& reg);

        //! [**taint api**] - Abstract union tainting.
        bool taintUnion(const triton::arch::OperandWrapper& op1, const triton::arch::OperandWrapper& op2);

        //! [**taint api**] - Abstract assignment tainting.
        bool taintAssignment(const triton::arch::OperandWrapper& op1, const triton::arch::OperandWrapper& op2);

        //! [**taint api**] - Taints MemoryImmediate with union. Returns true if the memDst is TAINTED.
        bool taintUnionMemoryImmediate(const triton::arch::MemoryAccess& memDst);

        //! [**taint api**] - Taints MemoryMemory with union. Returns true if the memDst or memSrc are TAINTED.
        bool taintUnionMemoryMemory(const triton::arch::MemoryAccess& memDst, const triton::arch::MemoryAccess& memSrc);

        //! [**taint api**] - Taints MemoryRegister with union. Returns true if the memDst or regSrc are TAINTED.
        bool taintUnionMemoryRegister(const triton::arch::MemoryAccess& memDst, const triton::arch::Register& regSrc);

        //! [**taint api**] - Taints RegisterImmediate with union. Returns true if the regDst is TAINTED.
        bool taintUnionRegisterImmediate(const triton::arch::Register& regDst);

        //! [**taint api**] - Taints RegisterMemory with union. Returns true if the regDst or memSrc are TAINTED.
        bool taintUnionRegisterMemory(const triton::arch::Register& regDst, const triton::arch::MemoryAccess& memSrc);

        //! [**taint api**] - Taints RegisterRegister with union. Returns true if the regDst or regSrc are TAINTED.
        bool taintUnionRegisterRegister(const triton::arch::Register& regDst, const triton::arch::Register& regSrc);

        //! [**taint api**] - Taints MemoryImmediate with assignment. Returns always false.
        bool taintAssignmentMemoryImmediate(const triton::arch::MemoryAccess& memDst);

        //! [**taint api**] - Taints MemoryMemory with assignment. Returns true if the memDst is tainted.
        bool taintAssignmentMemoryMemory(const triton::arch::MemoryAccess& memDst, const triton::arch::MemoryAccess& memSrc);

        //! [**taint api**] - Taints MemoryRegister with assignment. Returns true if the memDst is tainted.
        bool taintAssignmentMemoryRegister(const triton::arch::MemoryAccess& memDst, const triton::arch::Register& regSrc);

        //! [**taint api**] - Taints RegisterImmediate with assignment. Returns always false.
        bool taintAssignmentRegisterImmediate(const triton::arch::Register& regDst);

        //! [**taint api**] - Taints RegisterMemory with assignment. Returns true if the regDst is tainted.
        bool taintAssignmentRegisterMemory(const triton::arch::Register& regDst, const triton::arch::MemoryAccess& memSrc);

        //! [**taint api**] - Taints RegisterRegister with assignment. Returns true if the regDst is tainted.
        bool taintAssignmentRegisterRegister(const triton::arch::Register& regDst, const triton::arch::Register& regSrc);
    };

    //! The API can be accessed everywhere (WIP: will be removed).
    extern triton::API api;

/*! @} End of triton namespace */
};

#endif /* TRITON_API_H */

