//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_API_H
#define TRITON_API_H

#include "architecture.hpp"
#include "astGarbageCollector.hpp"
#include "astRepresentation.hpp"
#include "immediateOperand.hpp"
#include "instruction.hpp"
#include "memoryOperand.hpp"
#include "operandWrapper.hpp"
#include "registerOperand.hpp"
#include "ast.hpp"
#include "solverEngine.hpp"
#include "symbolicEngine.hpp"
#include "taintEngine.hpp"
#include "tritonTypes.hpp"

#ifdef TRITON_PYTHON_BINDINGS
  #include "pythonBindings.hpp"
#endif



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

    /*! \class API
     *  \brief This is the master class and must be used as C++ API. */
    class API {

      protected:
        //! The architecture entry.
        triton::arch::Architecture arch;

        //! The taint engine.
        triton::engines::taint::TaintEngine* taint;

        //! The symbolic engine.
        triton::engines::symbolic::SymbolicEngine* sym;

        //! The backuped symbolic engine. Some optimizations need to perform an undo. This instance is used for that.
        triton::engines::symbolic::SymbolicEngine* symBackup;

        //! The solver engine.
        triton::engines::solver::SolverEngine* solver;

        //! The AST garbage collector interface.
        triton::ast::AstGarbageCollector* astGarbageCollector;

        //! The AST representation interface.
        triton::ast::representations::AstRepresentation* astRepresentation;

      public:

        /* Constructor and destructor of the API ========================================================= */
        //! Constructor.
        API();

        //! Destructor.
        ~API();



        /* Architecture API ============================================================================== */

        //! [**Architecture api**] - Returns true if the architecture is valid.
        bool isArchitectureValid(void) const;

        //! [**architecture api**] - Returns the architecture as triton::arch::architecture_e.
        triton::uint32 getArchitecture(void) const;

        //! [**architecture api**] - Raises an exception if the architecture is not initialized.
        void checkArchitecture(void) const;

        //! [**architecture api**] - Returns the CPU instance.
        triton::arch::cpuInterface* getCpu(void);

        //! [**architecture api**] - Setup an architecture.
        /*!
          \param arch the architecture.
        */
        void setArchitecture(triton::uint32 arch);

        //! [**architecture api**] - Clears the architecture states (registers and memory).
        void clearArchitecture(void);

        //! [**architecture api**] - Returns true if the regId is a flag.
        /*!
          \param regId the register id.
        */
        bool isCpuFlag(triton::uint32 regId) const;

        //! [**architecture api**] - Returns true if the regId is a register.
        /*!
          \param regId the register id.
        */
        bool isCpuRegister(triton::uint32 regId) const;

        //! [**architecture api**] - Returns true if the regId is a register or a flag.
        /*!
          \param regId the register id.
        */
        bool isCpuRegisterValid(triton::uint32 regId) const;

        //! [**architecture api**] - Returns the max size (in byte) of the CPU register (GPR).
        triton::uint32 cpuRegisterSize(void) const;

        //! [**architecture api**] - Returns the max size (in bit) of the CPU register (GPR).
        triton::uint32 cpuRegisterBitSize(void) const;

        //! [**architecture api**] - Returns the invalid CPU register id.
        triton::uint32 cpuInvalidRegister(void) const;

        //! [**architecture api**] - Returns the number of registers according to the CPU architecture.
        triton::uint32 cpuNumberOfRegisters(void) const;

        //! [**architecture api**] - Returns all information about the register.
        /*!
          \param reg the register id.
          \return std::tuple<name, b-high, b-low, parentId>
        */
        std::tuple<std::string, triton::uint32, triton::uint32, triton::uint32> getCpuRegInformation(triton::uint32 reg) const;

        //! [**architecture api**] - Returns all registers.
        std::set<triton::arch::RegisterOperand*> getAllRegisters(void) const;

        //! [**architecture api**] - Returns all parent registers.
        std::set<triton::arch::RegisterOperand*> getParentRegisters(void) const;

        //! [**architecture api**] - Returns the last concrete value recorded of a memory access.
        triton::uint8 getLastMemoryValue(triton::__uint addr) const;

        //! [**architecture api**] - Returns the last concrete value recorded of a memory access.
        triton::uint512 getLastMemoryValue(const triton::arch::MemoryOperand& mem) const;

        //! [**architecture api**] - Returns the last concrete values of a memory area.
        std::vector<triton::uint8> getLastMemoryAreaValue(triton::__uint baseAddr, triton::uint32 size) const;

        //! [**architecture api**] - Returns the last concrete value recorded of a register state.
        triton::uint512 getLastRegisterValue(const triton::arch::RegisterOperand& reg) const;

        //! [**architecture api**] - Sets the last concrete value of a memory access.
        void setLastMemoryValue(triton::__uint addr, triton::uint8 value);

        //! [**architecture api**] - Sets the last concrete value of a memory access.
        void setLastMemoryValue(const triton::arch::MemoryOperand& mem);

        //! [**architecture api**] - Sets the last concrete values of a memory area.
        void setLastMemoryAreaValue(triton::__uint baseAddr, const std::vector<triton::uint8>& values);

        //! [**architecture api**] - Sets the last concrete value of a register state. You cannot set an isolated flag, if so, use the flags registers like EFLAGS.
        void setLastRegisterValue(const triton::arch::RegisterOperand& reg);

        //! [**architecture api**] - Disassembles the instruction and setup operands. You must define an architecture before. \sa  processing().
        void disassembly(triton::arch::Instruction &inst) const;

        //! [**architecture api**] - Builds the instruction semantics. You must define an architecture before. \sa processing().
        void buildSemantics(triton::arch::Instruction &inst);



        /* Processing API ================================================================================ */

        //! [**proccesing api**] - The main function. This function processes everything (engine, IR, optimization, state, ...) from a given instruction.
        void processing(triton::arch::Instruction &inst);

        //! [**proccesing api**] - Initialize everything.
        void initEngines(void);

        //! [**proccesing api**] - Remove everything.
        void removeEngines(void);

        //! [**proccesing api**] - Reset everything.
        void resetEngines(void);



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

        //! [**AST garbage collector api**] - Returns all variable nodes recorded.
        const std::map<std::string, triton::ast::AbstractNode*>& getAstVariableNodes(void) const;

        //! [**AST garbage collector api**] - Returns the node of a recorded variable.
        triton::ast::AbstractNode* getAstVariableNode(const std::string& name) const;

        //! [**AST garbage collector api**] - Sets all allocated nodes.
        void setAllocatedAstNodes(const std::set<triton::ast::AbstractNode*>& nodes);

        //! [**AST garbage collector api**] - Sets all variable nodes recorded.
        void setAstVariableNodes(const std::map<std::string, triton::ast::AbstractNode*>& nodes);



        /* AST Representation API ======================================================================== */

        //! [**AST representation api**] - Raises an exception if the AST representation interface is not initialized.
        void checkAstRepresentation(void) const;

        //! [**AST representation api**] - Display a node according to the AST representation mode.
        std::ostream& printAstRepresentation(std::ostream& stream, triton::ast::AbstractNode* node);

        //! [**AST representation api**] - Returns the AST representation mode as triton::ast::representations::mode_e.
        triton::uint32 getAstRepresentationMode(void) const;

        //! [**AST representation api**] - Sets the AST representation mode.
        void setAstRepresentationMode(triton::uint32 mode);



        /* Symbolic engine API =========================================================================== */

        //! [**symbolic api**] - Raises an exception if the symbolic engine is not initialized.
        void checkSymbolic(void) const;

        //! [**symbolic api**] - Returns the instance of the symbolic engine.
        triton::engines::symbolic::SymbolicEngine* getSymbolicEngine(void);

        //! [**symbolic api**] - Applies a backup of the symbolic engine.
        void backupSymbolicEngine(void);

        //! [**symbolic api**] - Restores the last taken backup of the symbolic engine.
        void restoreSymbolicEngine(void);

        //! [**symbolic api**] - Returns the map of symbolic registers defined.
        std::map<triton::arch::RegisterOperand, triton::engines::symbolic::SymbolicExpression*> getSymbolicRegisters(void) const;

        //! [**symbolic api**] - Returns the map of symbolic memory defined.
        std::map<triton::__uint, triton::engines::symbolic::SymbolicExpression*> getSymbolicMemory(void) const;

        //! [**symbolic api**] - Returns the symbolic expression id corresponding to the memory address.
        triton::__uint getSymbolicMemoryId(triton::__uint addr) const;

        //! [**symbolic api**] - Returns the symbolic expression id corresponding to the register.
        triton::__uint getSymbolicRegisterId(const triton::arch::RegisterOperand& reg) const;

        //! [**symbolic api**] - Returns the symbolic memory value.
        triton::uint8 getSymbolicMemoryValue(triton::__uint address);

        //! [**symbolic api**] - Returns the symbolic memory value.
        triton::uint512 getSymbolicMemoryValue(const triton::arch::MemoryOperand& mem);

        //! [**symbolic api**] - Returns the symbolic values of a memory area.
        std::vector<triton::uint8> getSymbolicMemoryAreaValue(triton::__uint baseAddr, triton::uint32 size);

        //! [**symbolic api**] - Returns the symbolic register value.
        triton::uint512 getSymbolicRegisterValue(const triton::arch::RegisterOperand& reg);

        //! [**symbolic api**] - If emulation enabled, returns `getSymbolicMemoryValue()` otherwise `getLastMemoryValue()`.
        triton::uint8 getMemoryValue(triton::__uint addr);

        //! [**symbolic api**] - If emulation enabled, returns `getSymbolicMemoryValue()` otherwise `getLastMemoryValue()`.
        triton::uint512 getMemoryValue(const triton::arch::MemoryOperand& mem);

        //! [**symbolic api**] - If emulation enabled, returns `getSymbolicMemoryAreaValue()` otherwise `getLastMemoryAreaValue()`.
        std::vector<triton::uint8> getMemoryAreaValue(triton::__uint baseAddr, triton::uint32 size);

        //! [**symbolic api**] - If emulation enabled, returns `getSymbolicRegisterValue()` otherwise `getLastRegisterValue()`.
        triton::uint512 getRegisterValue(const triton::arch::RegisterOperand& reg);

        //! [**symbolic api**] - Converts a symbolic expression to a symbolic variable. `symVarSize` must be in bits.
        triton::engines::symbolic::SymbolicVariable* convertExpressionToSymbolicVariable(triton::__uint exprId, triton::uint32 symVarSize, const std::string& symVarComment="");

        //! [**symbolic api**] - Converts a symbolic memory expression to a symbolic variable.
        triton::engines::symbolic::SymbolicVariable* convertMemoryToSymbolicVariable(const triton::arch::MemoryOperand& mem, const std::string& symVarComment="");

        //! [**symbolic api**] - Converts a symbolic register expression to a symbolic variable.
        triton::engines::symbolic::SymbolicVariable* convertRegisterToSymbolicVariable(const triton::arch::RegisterOperand& reg, const std::string& symVarComment="");

        //! [**symbolic api**] - Returns a symbolic operand.
        triton::ast::AbstractNode* buildSymbolicOperand(triton::arch::OperandWrapper& op);

        //! [**symbolic api**] - Returns a symbolic operand.
        triton::ast::AbstractNode* buildSymbolicOperand(triton::arch::Instruction& inst, triton::arch::OperandWrapper& op);

        //! [**symbolic api**] - Returns an immediate symbolic operand.
        triton::ast::AbstractNode* buildSymbolicImmediateOperand(const triton::arch::ImmediateOperand& imm);

        //! [**symbolic api**] - Returns an immediate symbolic operand.
        triton::ast::AbstractNode* buildSymbolicImmediateOperand(triton::arch::Instruction& inst, triton::arch::ImmediateOperand& imm);

        //! [**symbolic api**] - Returns a symbolic memory operand.
        triton::ast::AbstractNode* buildSymbolicMemoryOperand(const triton::arch::MemoryOperand& mem);

        //! [**symbolic api**] - Returns a symbolic memory operand.
        triton::ast::AbstractNode* buildSymbolicMemoryOperand(triton::arch::Instruction& inst, triton::arch::MemoryOperand& mem);

        //! [**symbolic api**] - Returns a symbolic register operand.
        triton::ast::AbstractNode* buildSymbolicRegisterOperand(const triton::arch::RegisterOperand& reg);

        //! [**symbolic api**] - Returns a symbolic register operand.
        triton::ast::AbstractNode* buildSymbolicRegisterOperand(triton::arch::Instruction& inst, triton::arch::RegisterOperand& reg);

        //! [**symbolic api**] - Returns a new symbolic expression. Note that if there are simplification passes recorded, simplification will be applied.
        triton::engines::symbolic::SymbolicExpression* newSymbolicExpression(triton::ast::AbstractNode* node, const std::string& comment="");

        //! [**symbolic api**] - Returns a new symbolic variable.
        triton::engines::symbolic::SymbolicVariable* newSymbolicVariable(triton::uint32 varSize, const std::string& comment="");

        //! [**symbolic api**] - Removes the symbolic expression corresponding to the id.
        void removeSymbolicExpression(triton::__uint symExprId);

        //! [**symbolic api**] - Returns the new symbolic abstract expression and links this expression to the instruction.
        triton::engines::symbolic::SymbolicExpression* createSymbolicExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, triton::arch::OperandWrapper& dst, const std::string& comment="");

        //! [**symbolic api**] - Returns the new symbolic memory expression and links this expression to the instruction.
        triton::engines::symbolic::SymbolicExpression* createSymbolicMemoryExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, triton::arch::MemoryOperand& mem, const std::string& comment="");

        //! [**symbolic api**] - Returns the new symbolic register expression and links this expression to the instruction.
        triton::engines::symbolic::SymbolicExpression* createSymbolicRegisterExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, triton::arch::RegisterOperand& reg, const std::string& comment="");

        //! [**symbolic api**] - Returns the new symbolic flag expression and links this expression to the instruction.
        triton::engines::symbolic::SymbolicExpression* createSymbolicFlagExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, triton::arch::RegisterOperand& flag, const std::string& comment="");

        //! [**symbolic api**] - Returns the new symbolic volatile expression and links this expression to the instruction.
        triton::engines::symbolic::SymbolicExpression* createSymbolicVolatileExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, const std::string& comment="");

        //! [**symbolic api**] - Assigns a symbolic expression to a memory.
        void assignSymbolicExpressionToMemory(triton::engines::symbolic::SymbolicExpression* se, const triton::arch::MemoryOperand& mem);

        //! [**symbolic api**] - Assigns a symbolic expression to a register.
        void assignSymbolicExpressionToRegister(triton::engines::symbolic::SymbolicExpression* se, const triton::arch::RegisterOperand& reg);

        //! [**symbolic api**] - Records a simplification callback.
        void recordSimplificationCallback(triton::engines::symbolic::sfp cb);

        #ifdef TRITON_PYTHON_BINDINGS
        //! [**symbolic api**] - Records a python simplification callback.
        void recordSimplificationCallback(PyObject* cb);
        #endif

        //! [**symbolic api**] - Removes a simplification callback.
        void removeSimplificationCallback(triton::engines::symbolic::sfp cb);

        #ifdef TRITON_PYTHON_BINDINGS
        //! [**symbolic api**] - Removes a python simplification callback.
        void removeSimplificationCallback(PyObject* cb);
        #endif

        //! [**symbolic api**] - Browses AST Dictionaries if the optimization `AST_DICTIONARIES` is enabled.
        triton::ast::AbstractNode* browseAstDictionaries(triton::ast::AbstractNode* node);

        //! [**symbolic api**] - Returns all stats about AST Dictionaries.
        std::map<std::string, triton::uint32> getAstDictionariesStats(void);

        //! [**symbolic api**] - Processes all recorded simplifications. Returns the simplified node.
        triton::ast::AbstractNode* processSimplification(triton::ast::AbstractNode* node, bool z3=false) const;

        //! [**symbolic api**] - Returns the symbolic expression corresponding to the id.
        triton::engines::symbolic::SymbolicExpression* getSymbolicExpressionFromId(triton::__uint symExprId) const;

        //! [**symbolic api**] - Returns the symbolic variable corresponding to the symbolic variable id.
        triton::engines::symbolic::SymbolicVariable* getSymbolicVariableFromId(triton::__uint symVarId) const;

        //! [**symbolic api**] - Returns the symbolic variable corresponding to the symbolic variable name.
        triton::engines::symbolic::SymbolicVariable* getSymbolicVariableFromName(const std::string& symVarName) const;

        //! [**symbolic api**] - Returns the logical conjunction vector of path constraints.
        const std::vector<triton::engines::symbolic::PathConstraint>& getPathConstraints(void) const;

        //! [**symbolic api**] - Returns the logical conjunction AST of path constraints.
        triton::ast::AbstractNode* getPathConstraintsAst(void);

        //! [**symbolic api**] - Adds a path constraint.
        void addPathConstraint(triton::engines::symbolic::SymbolicExpression* expr);

        //! [**symbolic api**] - Clears the logical conjunction vector of path constraints.
        void clearPathConstraints(void);

        //! [**symbolic api**] - Enables or disables the symbolic execution engine.
        void enableSymbolicEngine(bool flag);

        //! [**symbolic api**] - Enables or disables the symbolic emulation.
        void enableSymbolicEmulation(bool flag);

        //! [**symbolic api**] - Enabled, Triton will use the simplification passes of z3 before to call its recorded simplification passes.
        void enableSymbolicZ3Simplification(bool flag);

        //! [**symbolic api**] - Enables or disables a symbolic optimization.
        void enableSymbolicOptimization(enum triton::engines::symbolic::optimization_e opti, bool flag);

        /*! \brief [**symbolic api**] - Returns true if we perform a full symbolic emulation.
         *
         * \description
         * **true**: full symbolic execution (emulation).
         * **false**: concolic execution.
         */
        bool isSymbolicEmulationEnabled(void) const;

        //! [**symbolic api**] - Returns true if the symbolic execution engine is enabled.
        bool isSymbolicEngineEnabled(void) const;

        //! [**symbolic api**] - Returns true if Triton can use the simplification passes of z3.
        bool isSymbolicZ3SimplificationEnabled(void) const;

        //! [**symbolic api**] - Returns true if the symbolic expression ID exists.
        bool isSymbolicExpressionIdExists(triton::__uint symExprId) const;

        //! [**symbolic api**] - Returns true if the symbolic optimization is enabled.
        bool isSymbolicOptimizationEnabled(enum triton::engines::symbolic::optimization_e opti);

        //! [**symbolic api**] - Concretizes all symbolic memory references.
        void concretizeAllMemory(void);

        //! [**symbolic api**] - Concretizes all symbolic register references.
        void concretizeAllRegister(void);

        //! [**symbolic api**] - Concretizes a specific symbolic memory reference.
        void concretizeMemory(const triton::arch::MemoryOperand& mem);

        //! [**symbolic api**] - Concretizes a specific symbolic memory reference.
        void concretizeMemory(triton::__uint addr);

        //! [**symbolic api**] - Concretizes a specific symbolic register reference.
        void concretizeRegister(const triton::arch::RegisterOperand& reg);

        //! [**symbolic api**] - Returns the partial AST from a symbolic expression id.
        triton::ast::AbstractNode* getAstFromId(triton::__uint symExprId);

        //! [**symbolic api**] - Returns the full AST of a root node.
        triton::ast::AbstractNode* getFullAst(triton::ast::AbstractNode* node);

        //! [**symbolic api**] - Returns the full AST from a symbolic expression id.
        triton::ast::AbstractNode* getFullAstFromId(triton::__uint symExprId);

        //! [**symbolic api**] - Returns the list of the tainted symbolic expressions.
        std::list<triton::engines::symbolic::SymbolicExpression*> getTaintedSymbolicExpressions(void) const;

        //! [**symbolic api**] - Returns all symbolic expressions as a map of <SymExprId : SymExpr>
        const std::map<triton::__uint, triton::engines::symbolic::SymbolicExpression*>& getSymbolicExpressions(void) const;

        //! [**symbolic api**] - Returns all symbolic variables as a map of <SymVarId : SymVar>
        const std::map<triton::__uint, triton::engines::symbolic::SymbolicVariable*>& getSymbolicVariables(void) const;

        //! [**symbolic api**] - Returns all variable declarations representation.
        std::string getVariablesDeclaration(void) const;



        /* Solver engine API ============================================================================= */

        //! [**solver api**] - Raises an exception if the solver engine is not initialized.
        void checkSolver(void) const;

        //! [**solver api**] - Computes and returns a model from a symbolic constraint.
        /*! \brief map of symbolic variable id -> model
         *
         * \description
         * **item1**: symbolic variable id<br>
         * **item2**: model
         */
        std::map<triton::uint32, triton::engines::solver::SolverModel> getModel(triton::ast::AbstractNode *node) const;

        //! [**solver api**] - Computes and returns several models from a symbolic constraint. The `limit` is the number of models returned.
        /*! \brief list of map of symbolic variable id -> model
         *
         * \description
         * **item1**: symbolic variable id<br>
         * **item2**: model
         */
        std::list<std::map<triton::uint32, triton::engines::solver::SolverModel>> getModels(triton::ast::AbstractNode *node, triton::uint32 limit) const;

        //! [**solver api**] - Evaluates an AST via Z3 and returns the symbolic value.
        triton::uint512 evaluateAstViaZ3(triton::ast::AbstractNode *node) const;



        /* Taint engine API ============================================================================== */

        //! [**taint api**] - Raises an exception if the taint engine is not initialized.
        void checkTaint(void) const;

        //! [**taint api**] - Returns the instance of the taint engine.
        triton::engines::taint::TaintEngine* getTaintEngine(void);

        //! [**taint api**] - Enables or disables the taint engine.
        void enableTaintEngine(bool flag);

        //! [**taint api**] - Returns true if the taint engine is enabled.
        bool isTaintEngineEnabled(void) const;

        //! [**taint api**] - Abstract taint verification.
        bool isTainted(const triton::arch::OperandWrapper& op) const;

        //! [**taint api**] - Returns true if the addr is tainted.
        /*!
          \param addr the targeted address.
          \param size the access' size
        */
        bool isMemoryTainted(triton::__uint addr, triton::uint32 size=1) const;

        //! [**taint api**] - Returns true if the memory is tainted.
        /*!
          \param mem the memory operand.
        */
        bool isMemoryTainted(const triton::arch::MemoryOperand& mem) const;

        //! [**taint api**] - Returns true if the register is tainted.
        /*!
          \param reg the register operand.
        */
        bool isRegisterTainted(const triton::arch::RegisterOperand& reg) const;

        //! [**taint api**] - Sets abstract flag of the operand.
        /*!
          \param op the abstract operand.
          \param flag TAINTED or !TAINTED
          \return flag
        */
        bool setTaint(const triton::arch::OperandWrapper& op, bool flag);


        //! [**taint api**] - Sets memory flag.
        /*!
          \param mem the memory operand.
          \param flag TAINTED or !TAINTED
          \return flag
        */
        bool setTaintMemory(const triton::arch::MemoryOperand& mem, bool flag);

        //! [**taint api**] - Sets register flag.
        /*!
          \param reg the register operand.
          \param flag TAINTED or !TAINTED
          \return flag
        */
        bool setTaintRegister(const triton::arch::RegisterOperand& reg, bool flag);

        //! [**taint api**] - Taints an address.
        /*!
          \param addr the targeted address.
          \return triton::engines::taint::TAINTED
        */
        bool taintMemory(triton::__uint addr);

        //! [**taint api**] - Taints a memory.
        /*!
          \param mem the memory operand.
          \return triton::engines::taint::TAINTED
        */
        bool taintMemory(const triton::arch::MemoryOperand& mem);

        //! [**taint api**] - Taints a register.
        /*!
          \param reg the register operand.
          \return triton::engines::taint::TAINTED
        */
        bool taintRegister(const triton::arch::RegisterOperand& reg);

        //! [**taint api**] - Untaints an address.
        /*!
          \param addr the targeted address.
          \return triton::engines::taint::UNTAINTED
        */
        bool untaintMemory(triton::__uint addr);

        //! [**taint api**] - Untaints a memory.
        /*!
          \param mem the memory operand.
          \return triton::engines::taint::UNTAINTED
        */
        bool untaintMemory(const triton::arch::MemoryOperand& mem);

        //! [**taint api**] - Untaints a register.
        /*!
          \param reg the register operand.
          \return triton::engines::taint::UNTAINTED
        */
        bool untaintRegister(const triton::arch::RegisterOperand& reg);

        //! [**taint api**] - Abstract union tainting.
        bool taintUnion(const triton::arch::OperandWrapper& op1, const triton::arch::OperandWrapper& op2);

        //! [**taint api**] - Abstract assignment tainting.
        bool taintAssignment(const triton::arch::OperandWrapper& op1, const triton::arch::OperandWrapper& op2);

        //! [**taint api**] - Taints MemoryImmediate with union.
        /*!
          \param memDst the memory destination.
          \return true if the memDst is TAINTED.
        */
        bool taintUnionMemoryImmediate(const triton::arch::MemoryOperand& memDst);

        //! [**taint api**] - Taints MemoryMemory with union.
        /*!
          \param memDst the memory destination.
          \param memSrc the memory source.
          \return true if the memDst or memSrc are TAINTED.
        */
        bool taintUnionMemoryMemory(const triton::arch::MemoryOperand& memDst, const triton::arch::MemoryOperand& memSrc);

        //! [**taint api**] - Taints MemoryRegister with union.
        /*!
          \param memDst the memory destination.
          \param regSrc the register source.
          \return true if the memDst or regSrc are TAINTED.
        */
        bool taintUnionMemoryRegister(const triton::arch::MemoryOperand& memDst, const triton::arch::RegisterOperand& regSrc);

        //! [**taint api**] - Taints RegisterImmediate with union.
        /*!
          \param regDst the register source.
          \return true if the regDst is TAINTED.
        */
        bool taintUnionRegisterImmediate(const triton::arch::RegisterOperand& regDst);

        //! [**taint api**] - Taints RegisterMemory with union.
        /*!
          \param regDst the register destination.
          \param memSrc the memory source.
          \return true if the regDst or memSrc are TAINTED.
        */
        bool taintUnionRegisterMemory(const triton::arch::RegisterOperand& regDst, const triton::arch::MemoryOperand& memSrc);

        //! [**taint api**] - Taints RegisterRegister with union.
        /*!
          \param regDst the register destination.
          \param regSrc the register source.
          \return true if the regDst or regSrc are TAINTED.
        */
        bool taintUnionRegisterRegister(const triton::arch::RegisterOperand& regDst, const triton::arch::RegisterOperand& regSrc);

        //! [**taint api**] - Taints MemoryImmediate with assignment.
        /*!
          \param memDst the memory destination.
          \return always false.
        */
        bool taintAssignmentMemoryImmediate(const triton::arch::MemoryOperand& memDst);

        //! [**taint api**] - Taints MemoryMemory with assignment.
        /*!
          \param memDst the memory destination.
          \param memSrc the memory source.
          \return true if the memDst is tainted.
        */
        bool taintAssignmentMemoryMemory(const triton::arch::MemoryOperand& memDst, const triton::arch::MemoryOperand& memSrc);

        //! [**taint api**] - Taints MemoryRegister with assignment.
        /*!
          \param memDst the memory destination.
          \param regSrc the register source.
          \return true if the memDst is tainted.
        */
        bool taintAssignmentMemoryRegister(const triton::arch::MemoryOperand& memDst, const triton::arch::RegisterOperand& regSrc);

        //! [**taint api**] - Taints RegisterImmediate with assignment.
        /*!
          \param regDst the register destination.
          \return always false.
        */
        bool taintAssignmentRegisterImmediate(const triton::arch::RegisterOperand& regDst);

        //! [**taint api**] - Taints RegisterMemory with assignment.
        /*!
          \param regDst the register destination.
          \param memSrc the memory source.
          \return true if the regDst is tainted.
        */
        bool taintAssignmentRegisterMemory(const triton::arch::RegisterOperand& regDst, const triton::arch::MemoryOperand& memSrc);

        //! [**taint api**] - Taints RegisterRegister with assignment.
        /*!
          \param regDst the register destination.
          \param regSrc the register source.
          \return true if the regDst is tainted.
        */
        bool taintAssignmentRegisterRegister(const triton::arch::RegisterOperand& regDst, const triton::arch::RegisterOperand& regSrc);
    };

    //! The API can be accessed as everywhere.
    extern API api;

/*! @} End of triton namespace */
};

#endif /* TRITON_API_H */

