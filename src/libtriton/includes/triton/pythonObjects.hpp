//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/


#ifndef TRITON_PYOBJECT_H
#define TRITON_PYOBJECT_H

#include <triton/triton_export.h>
#include <triton/pythonBindings.hpp>

#include <triton/archEnums.hpp>
#include <triton/ast.hpp>
#include <triton/bitsVector.hpp>
#include <triton/immediate.hpp>
#include <triton/instruction.hpp>
#include <triton/memoryAccess.hpp>
#include <triton/pathConstraint.hpp>
#include <triton/register.hpp>
#include <triton/solverModel.hpp>
#include <triton/symbolicExpression.hpp>
#include <triton/symbolicVariable.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  class API;

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
      TRITON_EXPORT PyObject* PyAstNode(const triton::ast::SharedAbstractNode& node);

      //! Creates the BitsVector python class.
      template <typename T> TRITON_EXPORT PyObject* PyBitsVector(const T& op);

      //! Creates the Immediate python class.
      TRITON_EXPORT PyObject* PyImmediate(const triton::arch::Immediate& imm);

      //! Creates the Instruction python class.
      TRITON_EXPORT PyObject* PyInstruction(void);

      //! Creates the Instruction python class.
      TRITON_EXPORT PyObject* PyInstruction(const triton::arch::Instruction& inst);

      //! Creates the Instruction python class.
      TRITON_EXPORT PyObject* PyInstruction(const triton::uint8* opcodes, triton::uint32 opSize);

      //! Creates the Memory python class.
      TRITON_EXPORT PyObject* PyMemoryAccess(const triton::arch::MemoryAccess& mem);

      //! Creates the PathConstraint python class.
      TRITON_EXPORT PyObject* PyPathConstraint(const triton::engines::symbolic::PathConstraint& pc);

      //! Creates the new TritonContext python class.
      TRITON_EXPORT PyObject* PyTritonContext(void);

      //! Creates the new TritonContext python class.
      TRITON_EXPORT PyObject* PyTritonContext(triton::arch::architecture_e arch);

      //! Creates a TritonContext python class which is a reference to another Context.
      TRITON_EXPORT PyObject* PyTritonContextRef(triton::API& api);

      //! Creates an AstContext python class.
      TRITON_EXPORT PyObject* PyAstContext(const triton::ast::SharedAstContext& ctxt);

      //! Creates the Register python class.
      TRITON_EXPORT PyObject* PyRegister(const triton::arch::Register& reg);

      //! Creates the SolverModel python class.
      TRITON_EXPORT PyObject* PySolverModel(const triton::engines::solver::SolverModel& model);

      //! Creates the SymbolicExpression python class.
      TRITON_EXPORT PyObject* PySymbolicExpression(const triton::engines::symbolic::SharedSymbolicExpression& expr);

      //! Creates the SymbolicVariable python class.
      TRITON_EXPORT PyObject* PySymbolicVariable(const triton::engines::symbolic::SharedSymbolicVariable& symVar);

      /* AstNode ======================================================== */

      //! pyAstNode object.
      typedef struct {
        PyObject_HEAD
        triton::ast::SharedAbstractNode node;
      } AstNode_Object;

      //! pyAstNode type.
      TRITON_EXPORT extern PyTypeObject AstNode_Type;

      /* BitsVector ====================================================== */

      //! pyBitsVector object.
      typedef struct {
        PyObject_HEAD
        triton::arch::BitsVector* bv;
      } BitsVector_Object;

      //! pyBitsVector type.
      TRITON_EXPORT extern PyTypeObject BitsVector_Type;

      /* Immediate ====================================================== */

      //! pyImmediate object.
      typedef struct {
        PyObject_HEAD
        triton::arch::Immediate* imm;
      } Immediate_Object;

      //! pyImmediate type.
      TRITON_EXPORT extern PyTypeObject Immediate_Type;

      /* Instruction ==================================================== */

      //! pyInstruction object.
      typedef struct {
        PyObject_HEAD
        triton::arch::Instruction* inst;
      } Instruction_Object;

      //! pyInstruction type.
      TRITON_EXPORT extern PyTypeObject Instruction_Type;

      /* MemoryAccess =================================================== */

      //! pyMemory object.
      typedef struct {
        PyObject_HEAD
        triton::arch::MemoryAccess* mem;
      } MemoryAccess_Object;

      //! pyMemory type.
      TRITON_EXPORT extern PyTypeObject MemoryAccess_Type;

      /* PathConstraint ================================================= */

      //! pyPathConstraint object.
      typedef struct {
        PyObject_HEAD
        triton::engines::symbolic::PathConstraint* pc; //! Pointer to the cpp path constraints
      } PathConstraint_Object;

      //! pyPathConstraint type.
      TRITON_EXPORT extern PyTypeObject PathConstraint_Type;

      /* Register ======================================================= */

      //! pyRegister object.
      typedef struct {
        PyObject_HEAD
        triton::arch::Register* reg; //! Pointer to the cpp register
      } Register_Object;

      //! pyRegister type.
      TRITON_EXPORT extern PyTypeObject Register_Type;

      /* TrytonContext ======================================================= */

      //! pyTritonContext object.
      typedef struct {
        PyObject_HEAD
        triton::API* api;   //! Pointer to the cpp triton context
        bool ref;           //! Determine if this instance is a reference or not.
        PyObject* regAttr;  //! Pointer to the registers attribute
      } TritonContext_Object;

      //! pyRegister type.
      TRITON_EXPORT extern PyTypeObject TritonContextObject_Type;

      /* AstContext ======================================================= */

      //! pyAstContext object.
      typedef struct {
        PyObject_HEAD
        triton::ast::SharedAstContext ctxt;
      } AstContext_Object;

      //! pyRegister type.
      TRITON_EXPORT extern PyTypeObject AstContextObject_Type;

      /* SolverModel ==================================================== */

      //! pySolverModel object.
      typedef struct {
        PyObject_HEAD
        triton::engines::solver::SolverModel* model; //! Pointer to the cpp solver model
      } SolverModel_Object;

      //! pySolverModel type.
      TRITON_EXPORT extern PyTypeObject SolverModel_Type;

      /* SymbolicExpression ============================================= */

      //! pySymbolicExpression object.
      typedef struct {
        PyObject_HEAD
        triton::engines::symbolic::SharedSymbolicExpression symExpr;
      } SymbolicExpression_Object;

      //! pySymbolicExpression type.
      TRITON_EXPORT extern PyTypeObject SymbolicExpression_Type;

      /* SymbolicVariable =============================================== */

      //! pySymbolicVariable object.
      typedef struct {
        PyObject_HEAD
        triton::engines::symbolic::SharedSymbolicVariable symVar;
      } SymbolicVariable_Object;

      //! pySymbolicVariable type.
      TRITON_EXPORT extern PyTypeObject SymbolicVariable_Type;

    /*! @} End of python namespace */
    };
  /*! @} End of bindings namespace */
  };
/*! @} End of triton namespace */
};


/*! Returns the triton::ast::SharedAbstractNode. */
#define PyAstNode_AsAstNode(v) (((triton::bindings::python::AstNode_Object*)(v))->node)

/*! Checks if the pyObject is a triton::arch::BitsVector. */
#define PyBitsVector_Check(v) ((v)->ob_type == &triton::bindings::python::BitsVector_Type)

/*! Returns the triton::arch::BitsVector. */
#define PyBitsVector_AsBitsVector(v) (((triton::bindings::python::BitsVector_Object*)(v))->bv)

/*! Checks if the pyObject is a triton::arch::Immediate. */
#define PyImmediate_Check(v) ((v)->ob_type == &triton::bindings::python::Immediate_Type)

/*! Returns the triton::arch::Immediate. */
#define PyImmediate_AsImmediate(v) (((triton::bindings::python::Immediate_Object*)(v))->imm)

/*! Checks if the pyObject is a triton::arch::Instruction. */
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

/*! Checks if the pyObject is a triton::arch::TritonContext. */
#define PyTritonContext_Check(v) ((v)->ob_type == &triton::bindings::python::TritonContext_Type)

/*! Returns the triton::arch::TritonContext. */
#define PyTritonContext_AsTritonContext(v) (((triton::bindings::python::TritonContext_Object*)(v))->api)

/*! Checks if the pyObject is a triton::arch::AstContext. */
#define PyAstContext_Check(v) ((v)->ob_type == &triton::bindings::python::AstContext_Type)

/*! Returns the triton::arch::AstContext. */
#define PyAstContext_AsAstContext(v) (((triton::bindings::python::AstContext_Object*)(v))->ctxt)

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
