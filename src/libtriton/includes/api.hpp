//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_API_H
#define TRITON_API_H

#include "architecture.hpp"
#include "immediateOperand.hpp"
#include "instruction.hpp"
#include "memoryOperand.hpp"
#include "operandWrapper.hpp"
#include "registerOperand.hpp"
#include "smt2lib.hpp"
#include "solverEngine.hpp"
#include "symbolicEngine.hpp"
#include "taintEngine.hpp"
#include "tritonTypes.hpp"

#ifdef TRITON_PYTHON_BINDINGS
  #ifdef __unix__
    #include <python2.7/Python.h>
  #elif _WIN32
    #include <Python.h>
  #endif
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

      public:

        /* Constructor and destructor of the API ========================================================= */
        //! Constructor.
        API();

        //! Destructor.
        ~API();



        /* Architecture API ============================================================================== */

        //! [**Architecture api**] - Returns true if the architecture is valid.
        bool isArchitectureValid(void);

        //! [**architecture api**] - Returns the architecture as triton::arch::architecture_e.
        triton::uint32 getArchitecture(void) const;

        //! [**architecture api**] - Raises an exception if the architecture is not initialized.
        void checkArchitecture(void);

        //! [**architecture api**] - Returns the CPU instance.
        triton::arch::AbstractCpu* getCpu(void);

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
        bool isCpuFlag(triton::uint32 regId);

        //! [**architecture api**] - Returns true if the regId is a register.
        /*!
          \param regId the register id.
        */
        bool isCpuReg(triton::uint32 regId);

        //! [**architecture api**] - Returns true if the regId is a register or a flag.
        /*!
          \param regId the register id.
        */
        bool isCpuRegValid(triton::uint32 regId);

        //! [**architecture api**] - Returns the max size (in byte) of the CPU register (GPR).
        triton::uint32 cpuRegSize(void);

        //! [**architecture api**] - Returns the max size (in bit) of the CPU register (GPR).
        triton::uint32 cpuRegBitSize(void);

        //! [**architecture api**] - Returns the invalid CPU register id.
        triton::uint32 cpuInvalidReg(void);

        //! [**architecture api**] - Returns the number of registers according to the CPU architecture.
        triton::uint32 cpuNumberOfReg(void);

        //! [**architecture api**] - Returns all information about the register.
        /*!
          \param reg the register id.
          \return std::tuple<name, b-high, b-low, parentId>
        */
        std::tuple<std::string, triton::uint32, triton::uint32, triton::uint32> getCpuRegInformation(triton::uint32 reg);

        //! [**architecture api**] - Returns all parent registers.
        std::set<triton::arch::RegisterOperand*> getParentRegister(void);

        //! [**architecture api**] - Returns the last concrete value recorded of a memory access.
        triton::uint8 getLastMemoryValue(triton::__uint addr);

        //! [**architecture api**] - Returns the last concrete value recorded of a memory access.
        triton::uint128 getLastMemoryValue(triton::arch::MemoryOperand& mem);

        //! [**architecture api**] - Returns the last concrete value recorded of a register state.
        triton::uint128 getLastRegisterValue(triton::arch::RegisterOperand& reg);

        //! [**architecture api**] - Sets the last concrete value of a memory access.
        void setLastMemoryValue(triton::__uint addr, triton::uint8 value);

        //! [**architecture api**] - Sets the last concrete value of a memory access.
        void setLastMemoryValue(triton::arch::MemoryOperand& mem);

        //! [**architecture api**] - Sets the last concrete value of a register state. You cannot set an isolated flag, if so, use the flags registers like EFLAGS or RFLAGS.
        void setLastRegisterValue(triton::arch::RegisterOperand& reg);

        //! [**architecture api**] - Disassembles the instruction and setup operands. You must define an architecture before. \sa  processing().
        void disassembly(triton::arch::Instruction &inst);

        //! [**architecture api**] - Builds the instruction semantics based on the SMT2-Lib representation. You must define an architecture before. \sa processing().
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


        /* Symbolic engine API =========================================================================== */

        //! [**symbolic api**] - Raises an exception if the symbolic engine is not initialized.
        void checkSymbolic(void);

        //! [**symbolic api**] - Returns the symbolic engine's instance.
        triton::engines::symbolic::SymbolicEngine* getSymbolicEngine(void);

        //! [**symbolic api**] - Applies a backup of the symbolic engine.
        void backupSymbolicEngine(void);

        //! [**symbolic api**] - Restores the last taken backup of the symbolic engine.
        void restoreSymbolicEngine(void);

        //! [**symbolic api**] - Returns the map of symbolic registers defined.
        std::map<triton::arch::RegisterOperand, triton::engines::symbolic::SymbolicExpression*> getSymbolicRegister(void);

        //! [**symbolic api**] - Returns the map of symbolic memory defined.
        std::map<triton::__uint, triton::engines::symbolic::SymbolicExpression*> getSymbolicMemory(void);

        //! [**symbolic api**] - Returns the symbolic expression id corresponding to the memory address.
        triton::__uint getSymbolicMemoryId(triton::__uint addr);

        //! [**symbolic api**] - Returns the symbolic expression id corresponding to the register.
        triton::__uint getSymbolicRegisterId(triton::arch::RegisterOperand& reg);

        //! [**symbolic api**] - Returns the symbolic memory value.
        triton::uint8 getSymbolicMemoryValue(triton::__uint address);

        //! [**symbolic api**] - Returns the symbolic memory value.
        triton::uint128 getSymbolicMemoryValue(triton::arch::MemoryOperand& mem);

        //! [**symbolic api**] - Returns the symbolic register value.
        triton::uint128 getSymbolicRegisterValue(triton::arch::RegisterOperand& reg);

        //! [**symbolic api**] - If emulation enabled, returns `getSymbolicMemoryValue()` otherwise `getLastMemoryValue()`.
        triton::uint8 getMemoryValue(triton::__uint addr);

        //! [**symbolic api**] - If emulation enabled, returns `getSymbolicMemoryValue()` otherwise `getLastMemoryValue()`.
        triton::uint128 getMemoryValue(triton::arch::MemoryOperand& mem);

        //! [**symbolic api**] - If emulation enabled, returns `getSymbolicRegisterValue()` otherwise `getLastRegisterValue()`.
        triton::uint128 getRegisterValue(triton::arch::RegisterOperand& reg);

        //! [**symbolic api**] - Converts a symbolic expression to a symbolic variable. `symVarSize` must be in bits.
        triton::engines::symbolic::SymbolicVariable* convertExprToSymVar(triton::__uint exprId, triton::uint32 symVarSize, std::string symVarComment="");

        //! [**symbolic api**] - Converts a symbolic memory expression to a symbolic variable.
        triton::engines::symbolic::SymbolicVariable* convertMemToSymVar(triton::arch::MemoryOperand mem, std::string symVarComment="");

        //! [**symbolic api**] - Converts a symbolic register expression to a symbolic variable.
        triton::engines::symbolic::SymbolicVariable* convertRegToSymVar(triton::arch::RegisterOperand reg, std::string symVarComment="");

        //! [**symbolic api**] - Returns a symbolic operand.
        smt2lib::smtAstAbstractNode* buildSymbolicOperand(triton::arch::OperandWrapper& op);

        //! [**symbolic api**] - Returns an immediate symbolic operand.
        smt2lib::smtAstAbstractNode* buildSymbolicImmediateOperand(triton::arch::ImmediateOperand& imm);

        //! [**symbolic api**] - Returns a symbolic memory operand.
        smt2lib::smtAstAbstractNode* buildSymbolicMemoryOperand(triton::arch::MemoryOperand& mem);

        //! [**symbolic api**] - Returns a symbolic register operand.
        smt2lib::smtAstAbstractNode* buildSymbolicRegisterOperand(triton::arch::RegisterOperand& reg);

        //! [**symbolic api**] - Returns a new symbolic expression. Note that if there are simplification passes recorded, simplification will be applied.
        triton::engines::symbolic::SymbolicExpression* newSymbolicExpression(smt2lib::smtAstAbstractNode* node, std::string comment="");

        //! [**symbolic api**] - Returns a new symbolic variable.
        triton::engines::symbolic::SymbolicVariable* newSymbolicVariable(triton::uint32 varSize, std::string comment="");

        //! [**symbolic api**] - Removes the symbolic expression corresponding to the id.
        void removeSymbolicExpression(triton::__uint symExprId);

        //! [**symbolic api**] - Returns the new symbolic abstract expression and links this expression to the instruction.
        triton::engines::symbolic::SymbolicExpression* createSymbolicExpression(triton::arch::Instruction& inst, smt2lib::smtAstAbstractNode* node, triton::arch::OperandWrapper& dst, std::string comment="");

        //! [**symbolic api**] - Returns the new symbolic memory expression and links this expression to the instruction.
        triton::engines::symbolic::SymbolicExpression* createSymbolicMemoryExpression(triton::arch::Instruction& inst, smt2lib::smtAstAbstractNode* node, triton::arch::MemoryOperand& mem, std::string comment="");

        //! [**symbolic api**] - Returns the new symbolic register expression and links this expression to the instruction.
        triton::engines::symbolic::SymbolicExpression* createSymbolicRegisterExpression(triton::arch::Instruction& inst, smt2lib::smtAstAbstractNode* node, triton::arch::RegisterOperand& reg, std::string comment="");

        //! [**symbolic api**] - Returns the new symbolic flag expression and links this expression to the instruction.
        triton::engines::symbolic::SymbolicExpression* createSymbolicFlagExpression(triton::arch::Instruction& inst, smt2lib::smtAstAbstractNode* node, triton::arch::RegisterOperand& flag, std::string comment="");

        //! [**symbolic api**] - Returns the new symbolic volatile expression and links this expression to the instruction.
        triton::engines::symbolic::SymbolicExpression* createSymbolicVolatileExpression(triton::arch::Instruction& inst, smt2lib::smtAstAbstractNode* node, std::string comment="");

        //! [**symbolic api**] - Assigns a symbolic expression to a register.
        void assignSymbolicExpressionToRegister(triton::engines::symbolic::SymbolicExpression* se, triton::arch::RegisterOperand& reg);

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

        //! [**symbolic api**] - Browses AST Summaries if the optimization `AST_SUMMARIES` is enabled.
        smt2lib::smtAstAbstractNode* browseAstSummaries(smt2lib::smtAstAbstractNode* node);

        //! [**symbolic api**] - Returns all stats about AST Summaries.
        std::map<std::string, triton::uint32> getAstSummariesStats(void);

        //! [**symbolic api**] - Processes all recorded simplifications. Returns the simplified node.
        smt2lib::smtAstAbstractNode* processSimplification(smt2lib::smtAstAbstractNode* node);

        //! [**symbolic api**] - Returns the symbolic expression corresponding to the id.
        triton::engines::symbolic::SymbolicExpression* getSymbolicExpressionFromId(triton::__uint symExprId);

        //! [**symbolic api**] - Returns the symbolic variable corresponding to the symbolic variable id.
        triton::engines::symbolic::SymbolicVariable* getSymbolicVariableFromId(triton::__uint symVarId);

        //! [**symbolic api**] - Returns the symbolic variable corresponding to the symbolic variable name.
        triton::engines::symbolic::SymbolicVariable* getSymbolicVariableFromName(std::string& symVarName);

        //! [**symbolic api**] - Enables or disables the symbolic execution engine.
        void enableSymbolicEngine(bool flag);

        //! [**symbolic api**] - Enables or disables the symbolic emulation.
        void enableSymbolicEmulation(bool flag);

        //! [**symbolic api**] - Enables a symbolic optimization.
        void enableSymbolicOptimization(enum triton::engines::symbolic::optimization_e opti);

        //! [**symbolic api**] - Disables a symbolic optimization.
        void disableSymbolicOptimization(enum triton::engines::symbolic::optimization_e opti);

        /*! \brief [**symbolic api**] - Returns true if we perform a full symbolic emulation.
         *
         * \description
         * **true**: full symbolic execution (emulation).
         * **false**: concolic execution.
         */
        bool isSymbolicEmulationEnabled(void);

        //! [**symbolic api**] - Returns true if the symbolic execution engine is enabled.
        bool isSymbolicEngineEnabled(void);

        //! [**symbolic api**] - Returns true if the symbolic expression ID exists.
        bool isSymbolicExpressionIdExists(triton::__uint symExprId);

        //! [**symbolic api**] - Returns true if the symbolic optimization is enabled.
        bool isSymbolicOptimizationEnabled(enum triton::engines::symbolic::optimization_e opti);

        //! [**symbolic api**] - Concretizes all symbolic memory references.
        void concretizeAllMem(void);

        //! [**symbolic api**] - Concretizes all symbolic register references.
        void concretizeAllReg(void);

        //! [**symbolic api**] - Concretizes a specific symbolic memory reference.
        void concretizeMem(triton::arch::MemoryOperand& mem);

        //! [**symbolic api**] - Concretizes a specific symbolic memory reference.
        void concretizeMem(triton::__uint addr);

        //! [**symbolic api**] - Concretizes a specific symbolic register reference.
        void concretizeReg(triton::arch::RegisterOperand& reg);

        //! [**symbolic api**] - Returns the partial AST from a symbolic expression id.
        smt2lib::smtAstAbstractNode* getAstFromId(triton::__uint symExprId);

        //! [**symbolic api**] - Returns the full AST of a root node.
        smt2lib::smtAstAbstractNode* getFullAst(smt2lib::smtAstAbstractNode* node);

        //! [**symbolic api**] - Returns the full AST from a symbolic expression id.
        smt2lib::smtAstAbstractNode* getFullAstFromId(triton::__uint symExprId);

        //! [**symbolic api**] - Returns the list of the tainted symbolic expressions.
        std::list<triton::engines::symbolic::SymbolicExpression*> getTaintedSymbolicExpressions(void);

        //! [**symbolic api**] - Returns all symbolic expressions as a map of <SymExprId : SymExpr>
        std::map<triton::__uint, triton::engines::symbolic::SymbolicExpression*>& getSymbolicExpressions(void);

        //! [**symbolic api**] - Returns all symbolic variables as a map of <SymVarId : SymVar>
        std::map<triton::__uint, triton::engines::symbolic::SymbolicVariable*>& getSymbolicVariables(void);

        //! [**symbolic api**] - Returns all variable declarations syntax.
        std::string getVariablesDeclaration(void);



        /* Solver engine API ============================================================================= */

        //! [**solver api**] - Raises an exception if the solver engine is not initialized.
        void checkSolver(void);

        //! [**solver api**] - Computes and returns a model from a symbolic constraint.
        /*! \brief map of symbolic variable id -> model
         *
         * \description
         * **item1**: symbolic variable id<br>
         * **item2**: model
         */
        std::map<triton::uint32, triton::engines::solver::SolverModel> getModel(smt2lib::smtAstAbstractNode *node);

        //! [**solver api**] - Computes and returns several models from a symbolic constraint. The `limit` is the number of models returned.
        /*! \brief list of map of symbolic variable id -> model
         *
         * \description
         * **item1**: symbolic variable id<br>
         * **item2**: model
         */
        std::list<std::map<triton::uint32, triton::engines::solver::SolverModel>> getModels(smt2lib::smtAstAbstractNode *node, triton::uint32 limit);

        //! [**solver api**] - Evaluates an AST and returns the symbolic value.
        triton::uint512 evaluateAst(smt2lib::smtAstAbstractNode *node);



        /* Taint engine API ============================================================================== */

        //! [**taint api**] - Raises an exception if the taint engine is not initialized.
        void checkTaint(void);

        //! [**taint api**] - Returns the taint engine's instance.
        triton::engines::taint::TaintEngine* getTaintEngine(void);

        //! [**taint api**] - Enables or disables the taint engine.
        void enableTaintEngine(bool flag);

        //! [**taint api**] - Returns true if the taint engine is enabled.
        bool isTaintEngineEnabled(void);

        //! [**taint api**] - Returns true if the addr is tainted.
        /*!
          \param addr the targeted address.
          \param size the access' size
        */
        bool isAddrTainted(triton::__uint addr, triton::uint32 size=1);

        //! [**taint api**] - Abstract taint verification.
        bool isTainted(triton::arch::OperandWrapper& op);

        //! [**taint api**] - Returns true if the memory is tainted.
        /*!
          \param mem the memory operand.
        */
        bool isMemTainted(triton::arch::MemoryOperand &mem);

        //! [**taint api**] - Returns true if the register is tainted.
        /*!
          \param reg the register operand.
        */
        bool isRegTainted(triton::arch::RegisterOperand& reg);

        //! [**taint api**] - Sets abstract operand's flag.
        /*!
          \param op the abstract operand.
          \param flag TAINTED or !TAINTED
          \return flag
        */
        bool setTaint(triton::arch::OperandWrapper& op, bool flag);


        //! [**taint api**] - Sets memory's flag.
        /*!
          \param mem the memory operand.
          \param flag TAINTED or !TAINTED
          \return flag
        */
        bool setTaintMem(triton::arch::MemoryOperand& mem, bool flag);

        //! [**taint api**] - Sets register's flag.
        /*!
          \param reg the register operand.
          \param flag TAINTED or !TAINTED
          \return flag
        */
        bool setTaintReg(triton::arch::RegisterOperand& reg, bool flag);

        //! [**taint api**] - Taints an address.
        /*!
          \param addr the targeted address.
          \return triton::engines::taint::TAINTED
        */
        bool taintAddr(triton::__uint addr);

        //! [**taint api**] - Taints a memory.
        /*!
          \param mem the memory operand.
          \return triton::engines::taint::TAINTED
        */
        bool taintMem(triton::arch::MemoryOperand& mem);

        //! [**taint api**] - Taints a register.
        /*!
          \param reg the register operand.
          \return triton::engines::taint::TAINTED
        */
        bool taintReg(triton::arch::RegisterOperand& reg);

        //! [**taint api**] - Untaints an address.
        /*!
          \param addr the targeted address.
          \return triton::engines::taint::UNTAINTED
        */
        bool untaintAddr(triton::__uint addr);

        //! [**taint api**] - Untaints a memory.
        /*!
          \param mem the memory operand.
          \return triton::engines::taint::UNTAINTED
        */
        bool untaintMem(triton::arch::MemoryOperand& mem);

        //! [**taint api**] - Untaints a register.
        /*!
          \param reg the register operand.
          \return triton::engines::taint::UNTAINTED
        */
        bool untaintReg(triton::arch::RegisterOperand& reg);

        //! [**taint api**] - Abstract union tainting.
        bool taintUnion(triton::arch::OperandWrapper& op1, triton::arch::OperandWrapper& op2);

        //! [**taint api**] - Abstract assignment tainting.
        bool taintAssignment(triton::arch::OperandWrapper& op1, triton::arch::OperandWrapper& op2);

        //! [**taint api**] - Taints MemImm with union.
        /*!
          \param memDst the memory destination.
          \return true if the memDst is TAINTED.
        */
        bool taintUnionMemImm(triton::arch::MemoryOperand& memDst);

        //! [**taint api**] - Taints MemMem with union.
        /*!
          \param memDst the memory destination.
          \param memSrc the memory source.
          \return true if the memDst or memSrc are TAINTED.
        */
        bool taintUnionMemMem(triton::arch::MemoryOperand& memDst, triton::arch::MemoryOperand& memSrc);

        //! [**taint api**] - Taints MemReg with union.
        /*!
          \param memDst the memory destination.
          \param regSrc the register source.
          \return true if the memDst or regSrc are TAINTED.
        */
        bool taintUnionMemReg(triton::arch::MemoryOperand& memDst, triton::arch::RegisterOperand& regSrc);

        //! [**taint api**] - Taints RegImm with union.
        /*!
          \param regDst the register source.
          \return true if the regDst is TAINTED.
        */
        bool taintUnionRegImm(triton::arch::RegisterOperand& regDst);

        //! [**taint api**] - Taints RegMem with union.
        /*!
          \param regDst the register destination.
          \param memSrc the memory source.
          \return true if the regDst or memSrc are TAINTED.
        */
        bool taintUnionRegMem(triton::arch::RegisterOperand& regDst, triton::arch::MemoryOperand& memSrc);

        //! [**taint api**] - Taints RegReg with union.
        /*!
          \param regDst the register destination.
          \param regSrc the register source.
          \return true if the regDst or regSrc are TAINTED.
        */
        bool taintUnionRegReg(triton::arch::RegisterOperand& regDst, triton::arch::RegisterOperand& regSrc);

        //! [**taint api**] - Taints MemImm with assignment.
        /*!
          \param memDst the memory destination.
          \return always false.
        */
        bool taintAssignmentMemImm(triton::arch::MemoryOperand& memDst);

        //! [**taint api**] - Taints MemMem with assignment.
        /*!
          \param memDst the memory destination.
          \param memSrc the memory source.
          \return true if the memDst is tainted.
        */
        bool taintAssignmentMemMem(triton::arch::MemoryOperand& memDst, triton::arch::MemoryOperand& memSrc);

        //! [**taint api**] - Taints MemReg with assignment.
        /*!
          \param memDst the memory destination.
          \param regSrc the register source.
          \return true if the memDst is tainted.
        */
        bool taintAssignmentMemReg(triton::arch::MemoryOperand& memDst, triton::arch::RegisterOperand& regSrc);

        //! [**taint api**] - Taints RegImm with assignment.
        /*!
          \param regDst the register destination.
          \return always false.
        */
        bool taintAssignmentRegImm(triton::arch::RegisterOperand& regDst);

        //! [**taint api**] - Taints RegMem with assignment.
        /*!
          \param regDst the register destination.
          \param memSrc the memory source.
          \return true if the regDst is tainted.
        */
        bool taintAssignmentRegMem(triton::arch::RegisterOperand& regDst, triton::arch::MemoryOperand& memSrc);

        //! [**taint api**] - Taints RegReg with assignment.
        /*!
          \param regDst the register destination.
          \param regSrc the register source.
          \return true if the regDst is tainted.
        */
        bool taintAssignmentRegReg(triton::arch::RegisterOperand& regDst, triton::arch::RegisterOperand& regSrc);
    };

    //! The API can be accessed as everywhere.
    extern API api;

/*! @} End of triton namespace */
};

#endif /* TRITON_API_H */

