//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/


#ifdef TRITON_PYTHON_BINDINGS

#ifndef TRITON_PYOBJECT_H
#define TRITON_PYOBJECT_H

#include "ast.hpp"
#include "bitsVector.hpp"
#include "immediate.hpp"
#include "instruction.hpp"
#include "memoryAccess.hpp"
#include "pathConstraint.hpp"
#include "pythonBindings.hpp"
#include "registerOperand.hpp"
#include "solverModel.hpp"
#include "symbolicExpression.hpp"
#include "symbolicVariable.hpp"



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Bindings namespace
  namespace bindings {
  /*!
   *  \ingroup triton
   *  \addtogroup bindings
   *  @{
   */

    //! The Python namespace
    namespace python {
    /*!
     *  \ingroup bindings
     *  \addtogroup python
     *  @{
     */

      //! Creates the AstNode python class.
      PyObject* PyAstNode(triton::ast::AbstractNode* node);

      //! Creates the Bitvector python class.
      PyObject* PyBitvector(const triton::arch::Immediate& imm);

      //! Creates the Bitvector python class.
      PyObject* PyBitvector(const triton::arch::MemoryAccess& mem);

      //! Creates the Bitvector python class.
      PyObject* PyBitvector(const triton::arch::Register& reg);

      //! Creates the Bitvector python class.
      PyObject* PyBitvector(triton::uint32 high, triton::uint32 low);

      //! Creates the Immediate python class.
      PyObject* PyImmediate(const triton::arch::Immediate& imm);

      //! Creates the Instruction python class.
      PyObject* PyInstruction(void);

      //! Creates the Instruction python class.
      PyObject* PyInstruction(const triton::arch::Instruction& inst);

      //! Creates the Memory python class.
      PyObject* PyMemoryAccess(const triton::arch::MemoryAccess& mem);

      //! Creates the PathConstraint python class.
      PyObject* PyPathConstraint(const triton::engines::symbolic::PathConstraint& pc);

      //! Creates the Register python class.
      PyObject* PyRegister(const triton::arch::Register& reg);

      //! Creates the SolverModel python class.
      PyObject* PySolverModel(const triton::engines::solver::SolverModel& model);

      //! Creates the SymbolicExpression python class.
      PyObject* PySymbolicExpression(triton::engines::symbolic::SymbolicExpression* expr);

      //! Creates the SymbolicVariable python class.
      PyObject* PySymbolicVariable(triton::engines::symbolic::SymbolicVariable* symVar);

      /* AstNode ======================================================== */

      //! pyAstNode object.
      typedef struct {
        PyObject_HEAD
        triton::ast::AbstractNode* node;
      } AstNode_Object;

      //! pyAstNode type.
      extern PyTypeObject AstNode_Type;

      /* Bitvector ====================================================== */

      //! pyBitvector object.
      typedef struct {
        PyObject_HEAD
        triton::uint32 low;
        triton::uint32 high;
      } Bitvector_Object;

      //! pyBitvector type.
      extern PyTypeObject Bitvector_Type;

      /* Immediate =============================================== */

      //! pyImmediate object.
      typedef struct {
        PyObject_HEAD
        triton::arch::Immediate* imm;
      } Immediate_Object;

      //! pyImmediate type.
      extern PyTypeObject Immediate_Type;

      /* Instruction ==================================================== */

      //! pyInstruction object.
      typedef struct {
        PyObject_HEAD
        triton::arch::Instruction* inst;
      } Instruction_Object;

      //! pyInstruction type.
      extern PyTypeObject Instruction_Type;

      /* MemoryAccess ================================================== */

      //! pyMemory object.
      typedef struct {
        PyObject_HEAD
        triton::arch::MemoryAccess* mem;
      } MemoryAccess_Object;

      //! pyMemory type.
      extern PyTypeObject MemoryAccess_Type;

      /* PathConstraint ================================================= */

      //! pyPathConstraint object.
      typedef struct {
        PyObject_HEAD
        triton::engines::symbolic::PathConstraint* pc;
      } PathConstraint_Object;

      //! pyPathConstraint type.
      extern PyTypeObject PathConstraint_Type;

      /* Register ================================================ */

      //! pyRegister object.
      typedef struct {
        PyObject_HEAD
        triton::arch::Register* reg;
      } Register_Object;

      //! pyRegister type.
      extern PyTypeObject Register_Type;

      /* SolverModel ==================================================== */

      //! pySolverModel object.
      typedef struct {
        PyObject_HEAD
        triton::engines::solver::SolverModel* model;
      } SolverModel_Object;

      //! pySolverModel type.
      extern PyTypeObject SolverModel_Type;

      /* SymbolicExpression ============================================= */

      //! pySymbolicExpression object.
      typedef struct {
        PyObject_HEAD
        triton::engines::symbolic::SymbolicExpression* symExpr;
      } SymbolicExpression_Object;

      //! pySymbolicExpression type.
      extern PyTypeObject SymbolicExpression_Type;

      /* SymbolicVariable =============================================== */

      //! pySymbolicVariable object.
      typedef struct {
        PyObject_HEAD
        triton::engines::symbolic::SymbolicVariable* symVar;
      } SymbolicVariable_Object;

      //! pySymbolicVariable type.
      extern PyTypeObject SymbolicVariable_Type;

    /*! @} End of python namespace */
    };
  /*! @} End of bindings namespace */
  };
/*! @} End of triton namespace */
};


/*! Returns the triton::ast::AbstractNode. */
#define PyAstNode_AsAstNode(v) (((triton::bindings::python::AstNode_Object*)(v))->node)

/*! Checks if the pyObject is a triton::arch::BitsVector. */
#define PyBitvector_Check(v)  ((v)->ob_type == &triton::bindings::python::Bitvector_Type)

/*! Returns the triton::arch::BitsVector::high. */
#define PyBitvector_AsHigh(v) (((triton::bindings::python::Bitvector_Object*)(v))->high)

/*! Returns the triton::arch::BitsVector::low. */
#define PyBitvector_AsLow(v)  (((triton::bindings::python::Bitvector_Object*)(v))->low)

/*! Checks if the pyObject is an triton::arch::Immediate. */
#define PyImmediate_Check(v) ((v)->ob_type == &triton::bindings::python::Immediate_Type)

/*! Returns the triton::arch::Immediate. */
#define PyImmediate_AsImmediate(v) (((triton::bindings::python::Immediate_Object*)(v))->imm)

/*! Checks if the pyObject is an triton::arch::Instruction. */
#define PyInstruction_Check(v) ((v)->ob_type == &triton::bindings::python::Instruction_Type)

/*! Returns the triton::arch::Instruction. */
#define PyInstruction_AsInstruction(v) (((triton::bindings::python::Instruction_Object*)(v))->inst)

/*! Checks if the pyObject is a triton::arch::MemoryAccess. */
#define PyMemoryAccess_Check(v) ((v)->ob_type == &triton::bindings::python::MemoryAccess_Type)

/*! Returns the triton::arch::MemoryAccess. */
#define PyMemoryAccess_AsMemoryAccess(v) (((triton::bindings::python::MemoryAccess_Object*)(v))->mem)

/*! Checks if the pyObject is a triton::engines::symbolic::PathConstraint. */
#define PyPathConstraint_Check(v) ((v)->ob_type == &triton::bindings::python::PathConstraint_Type)

/*! Returns the triton::engines::symbolic::PathConstraint. */
#define PyPathConstraint_AsPathConstraint(v) (((triton::bindings::python::PathConstraint_Object*)(v))->pc)

/*! Checks if the pyObject is a triton::arch::Register. */
#define PyRegister_Check(v) ((v)->ob_type == &triton::bindings::python::Register_Type)

/*! Returns the triton::arch::Register. */
#define PyRegister_AsRegister(v) (((triton::bindings::python::Register_Object*)(v))->reg)

/*! Checks if the pyObject is a triton::engines::solver::SolverModel. */
#define PySolverModel_Check(v) ((v)->ob_type == &triton::bindings::python::SolverModel_Type)

/*! Returns the triton::engines::solver::SolverModel. */
#define PySolverModel_AsSolverModel(v) (((triton::bindings::python::SolverModel_Object*)(v))->model)

/*! Checks if the pyObject is a triton::ast::AbstractNode. */
#define PyAstNode_Check(v) ((v)->ob_type == &triton::bindings::python::AstNode_Type)

/*! Checks if the pyObject is a triton::engines::symbolic::SymbolicExpression. */
#define PySymbolicExpression_Check(v) ((v)->ob_type == &triton::bindings::python::SymbolicExpression_Type)

/*! Returns the triton::engines::symbolic::SymbolicExpression. */
#define PySymbolicExpression_AsSymbolicExpression(v) (((triton::bindings::python::SymbolicExpression_Object*)(v))->symExpr)

/*! Checks if the pyObject is a triton::engines::symbolic::SymbolicVariable. */
#define PySymbolicVariable_Check(v) ((v)->ob_type == &triton::bindings::python::SymbolicVariable_Type)

/*! Returns the triton::engines::symbolic::SymbolicVariable. */
#define PySymbolicVariable_AsSymbolicVariable(v) (((triton::bindings::python::SymbolicVariable_Object*)(v))->symVar)

#endif /* TRITON_PYOBJECT_H */
#endif /* TRITON_PYTHON_BINDINGS */

