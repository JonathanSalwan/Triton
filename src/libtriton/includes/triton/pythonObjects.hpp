//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/


#ifndef TRITON_PYOBJECT_H
#define TRITON_PYOBJECT_H

#include <triton/ast.hpp>
#include <triton/bitsVector.hpp>
#include <triton/elf.hpp>
#include <triton/elfDynamicTable.hpp>
#include <triton/elfHeader.hpp>
#include <triton/elfProgramHeader.hpp>
#include <triton/elfRelocationTable.hpp>
#include <triton/elfSectionHeader.hpp>
#include <triton/elfSymbolTable.hpp>
#include <triton/pe.hpp>
#include <triton/peHeader.hpp>
#include <triton/immediate.hpp>
#include <triton/instruction.hpp>
#include <triton/memoryAccess.hpp>
#include <triton/pathConstraint.hpp>
#include <triton/pythonBindings.hpp>
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

      //! Creates the Elf python class.
      PyObject* PyElf(const std::string& elf);

      //! Creates the ElfDynamicTable python class.
      PyObject* PyElfDynamicTable(const triton::format::elf::ElfDynamicTable& dyn);

      //! Creates the ElfHeader python class.
      PyObject* PyElfHeader(const triton::format::elf::ElfHeader& header);

      //! Creates the ElfProgramHeader python class.
      PyObject* PyElfProgramHeader(const triton::format::elf::ElfProgramHeader& phdr);

      //! Creates the ElfRelocationTable python class.
      PyObject* PyElfRelocationTable(const triton::format::elf::ElfRelocationTable& rel);

      //! Creates the ElfSectionHeader python class.
      PyObject* PyElfSectionHeader(const triton::format::elf::ElfSectionHeader& shdr);

      //! Creates the ElfSymbolTable python class.
      PyObject* PyElfSymbolTable(const triton::format::elf::ElfSymbolTable& sym);

      //! Creates the Pe python class.
      PyObject* PyPe(const std::string& pe);

      //! Creates the PeHeader python class.
      PyObject* PyPeHeader(const triton::format::pe::PeHeader& header);

      //! Creates the PeSectionHeader python class.
      PyObject* PyPeSectionHeader(const triton::format::pe::PeSectionHeader& shdr);

      //! Creates the PeImportTable python class.
      PyObject* PyPeImportTable(const triton::format::pe::PeImportDirectory& shdr);

      //! Creates the PeImportLookup python class.
      PyObject* PyPeImportLookup(const triton::format::pe::PeImportLookup& shdr);

      //! Creates the PeExportTable python class.
      PyObject* PyPeExportTable(const triton::format::pe::PeExportDirectory& shdr);

      //! Creates the PeExportEntry python class.
      PyObject* PyPeExportEntry(const triton::format::pe::PeExportEntry& shdr);

      //! Creates the Immediate python class.
      PyObject* PyImmediate(const triton::arch::Immediate& imm);

      //! Creates the Instruction python class.
      PyObject* PyInstruction(void);

      //! Creates the Instruction python class.
      PyObject* PyInstruction(const triton::arch::Instruction& inst);

      //! Creates the Instruction python class.
      PyObject* PyInstruction(const triton::uint8* opcodes, triton::uint32 opSize);

      //! Creates the Memory python class.
      PyObject* PyMemoryAccess(const triton::arch::MemoryAccess& mem);

      //! Creates the PathConstraint python class.
      PyObject* PyPathConstraint(const triton::engines::symbolic::PathConstraint& pc);

      //! Creates the Register python class.
      PyObject* PyRegister(const triton::arch::Register& reg);

      //! Creates the Register python class.
      PyObject* PyRegister(const triton::arch::Register& reg, triton::uint512 concreteValue);

      //! Creates the Register python class.
      PyObject* PyRegister(const triton::arch::Register& reg, triton::uint512 concreteValue, bool isImmutable);

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

      /* Elf  =========================================================== */

      //! pyElf object.
      typedef struct {
        PyObject_HEAD
        triton::format::elf::Elf* elf;
      } Elf_Object;

      //! pyElf type.
      extern PyTypeObject Elf_Type;

      /* ElfDynamicTable  =============================================== */

      //! pyElfDynamicTable object.
      typedef struct {
        PyObject_HEAD
        triton::format::elf::ElfDynamicTable* dyn;
      } ElfDynamicTable_Object;

      //! pyElfDynamicTable type.
      extern PyTypeObject ElfDynamicTable_Type;

      /* ElfHeader  ===================================================== */

      //! pyElfHeader object.
      typedef struct {
        PyObject_HEAD
        triton::format::elf::ElfHeader* header;
      } ElfHeader_Object;

      //! pyElfHeader type.
      extern PyTypeObject ElfHeader_Type;

      /* ElfProgramHeader  ============================================== */

      //! pyElfProgramHeader object.
      typedef struct {
        PyObject_HEAD
        triton::format::elf::ElfProgramHeader* phdr;
      } ElfProgramHeader_Object;

      //! pyElfProgramHeader type.
      extern PyTypeObject ElfProgramHeader_Type;

      /* ElfRelocationTable  =========================================== */

      //! pyElfRelocationTable object.
      typedef struct {
        PyObject_HEAD
        triton::format::elf::ElfRelocationTable* rel;
      } ElfRelocationTable_Object;

      //! pyElfRelocationTable type.
      extern PyTypeObject ElfRelocationTable_Type;

      /* ElfSectionHeader  ============================================== */

      //! pyElfSectionHeader object.
      typedef struct {
        PyObject_HEAD
        triton::format::elf::ElfSectionHeader* shdr;
      } ElfSectionHeader_Object;

      //! pyElfSectionHeader type.
      extern PyTypeObject ElfSectionHeader_Type;

      /* ElfSymbolTable  ================================================ */

      //! pyElfSymbolTable object.
      typedef struct {
        PyObject_HEAD
        triton::format::elf::ElfSymbolTable* sym;
      } ElfSymbolTable_Object;

      //! pyElfSymbolTable type.
      extern PyTypeObject ElfSymbolTable_Type;

      /* Pe   =========================================================== */

      //! pyPe object.
      typedef struct {
        PyObject_HEAD
        triton::format::pe::Pe* pe;
      } Pe_Object;

      //! pyPe type.
      extern PyTypeObject Pe_Type;

      /* PeHeader   ===================================================== */

      //! pyPeHeader object.
      typedef struct {
        PyObject_HEAD
        triton::format::pe::PeHeader* header;
      } PeHeader_Object;

      //! pyPeHeader type.
      extern PyTypeObject PeHeader_Type;

      /* PeSectionHeader  ============================================== */

      //! pyPeSectionHeader object.
      typedef struct {
        PyObject_HEAD
        triton::format::pe::PeSectionHeader* shdr;
      } PeSectionHeader_Object;

      //! pyPeSectionHeader type.
      extern PyTypeObject PeSectionHeader_Type;

      /* PeImportTable    ============================================== */

      //! pyPeImportTable object.
      typedef struct {
        PyObject_HEAD
        triton::format::pe::PeImportDirectory* impt;
      } PeImportTable_Object;

      //! pyPeImportTable type.
      extern PyTypeObject PeImportTable_Type;

      /* PeImportLookup    ============================================== */

      //! pyPeImportLookup object.
      typedef struct {
        PyObject_HEAD
        triton::format::pe::PeImportLookup* impt;
      } PeImportLookup_Object;

      //! pyPeImportTable type.
      extern PyTypeObject PeImportLookup_Type;

      /* PeImportTable    ============================================== */

      //! pyPeExportTable object.
      typedef struct {
        PyObject_HEAD
        triton::format::pe::PeExportDirectory* expt;
      } PeExportTable_Object;

      //! pyPeExportTable type.
      extern PyTypeObject PeExportTable_Type;

      /* PeExportEntry    ============================================== */

      //! pyPeExportEntry object.
      typedef struct {
        PyObject_HEAD
        triton::format::pe::PeExportEntry* impt;
      } PeExportEntry_Object;

      //! pyPeExportEntry type.
      extern PyTypeObject PeExportEntry_Type;

      /* Immediate ====================================================== */

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

      /* MemoryAccess =================================================== */

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

      /* Register ======================================================= */

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

/*! Checks if the pyObject is a triton::format::efl::Elf. */
#define PyElf_Check(v) ((v)->ob_type == &triton::bindings::python::Elf_Type)

/*! Returns the triton::format::elf::Elf. */
#define PyElf_AsElf(v) (((triton::bindings::python::Elf_Object*)(v))->elf)

/*! Checks if the pyObject is a triton::format::efl::ElfDynamicTable. */
#define PyElfDynamicTable_Check(v) ((v)->ob_type == &triton::bindings::python::ElfDynamicTable_Type)

/*! Returns the triton::format::elf::ElfDynamicTable. */
#define PyElfDynamicTable_AsElfDynamicTable(v) (((triton::bindings::python::ElfDynamicTable_Object*)(v))->dyn)

/*! Checks if the pyObject is a triton::format::efl::ElfHeader. */
#define PyElfHeader_Check(v) ((v)->ob_type == &triton::bindings::python::ElfHeader_Type)

/*! Returns the triton::format::elf::ElfHeader. */
#define PyElfHeader_AsElfHeader(v) (((triton::bindings::python::ElfHeader_Object*)(v))->header)

/*! Checks if the pyObject is a triton::format::efl::ElfProgramHeader. */
#define PyElfProgramHeader_Check(v) ((v)->ob_type == &triton::bindings::python::ElfProgramHeader_Type)

/*! Returns the triton::format::elf::ElfProgramHeader. */
#define PyElfProgramHeader_AsElfProgramHeader(v) (((triton::bindings::python::ElfProgramHeader_Object*)(v))->phdr)

/*! Checks if the pyObject is a triton::format::efl::ElfRelocationTable. */
#define PyElfRelocationTable_Check(v) ((v)->ob_type == &triton::bindings::python::ElfRelocationTable_Type)

/*! Returns the triton::format::elf::ElfRelocationTable. */
#define PyElfRelocationTable_AsElfRelocationTable(v) (((triton::bindings::python::ElfRelocationTable_Object*)(v))->rel)

/*! Checks if the pyObject is a triton::format::efl::ElfSectionHeader. */
#define PyElfSectionHeader_Check(v) ((v)->ob_type == &triton::bindings::python::ElfSectionHeader_Type)

/*! Returns the triton::format::elf::ElfSectionHeader. */
#define PyElfSectionHeader_AsElfSectionHeader(v) (((triton::bindings::python::ElfSectionHeader_Object*)(v))->shdr)

/*! Checks if the pyObject is a triton::format::efl::ElfSymbolTable. */
#define PyElfSymbolTable_Check(v) ((v)->ob_type == &triton::bindings::python::ElfSymbolTable_Type)

/*! Returns the triton::format::elf::ElfSymbolTable. */
#define PyElfSymbolTable_AsElfSymbolTable(v) (((triton::bindings::python::ElfSymbolTable_Object*)(v))->sym)

/*! Checks if the pyObject is a triton::format::pe::Pe. */
#define PyPe_Check(v) ((v)->ob_type == &triton::bindings::python::Pe_Type)

/*! Returns the triton::format::pe::Pe. */
#define PyPe_AsPe(v) (((triton::bindings::python::Pe_Object*)(v))->pe)

/*! Checks if the pyObject is a triton::format::pe::PeHeader. */
#define PyPeHeader_Check(v) ((v)->ob_type == &triton::bindings::python::PeHeader_Type)

/*! Returns the triton::format::pe::PeHeader. */
#define PyPeHeader_AsPeHeader(v) (((triton::bindings::python::PeHeader_Object*)(v))->header)

/*! Checks if the pyObject is a triton::format::pe::PeSectionHeader. */
#define PyPeSectionHeader_Check(v) ((v)->ob_type == &triton::bindings::python::PeSectionHeader_Type)

/*! Returns the triton::format::pe::PeSectionHeader. */
#define PyPeSectionHeader_AsPeSectionHeader(v) (((triton::bindings::python::PeSectionHeader_Object*)(v))->shdr)

/*! Checks if the pyObject is a triton::format::pe::PeImportDirectory. */
#define PyPeImportTable_Check(v) ((v)->ob_type == &triton::bindings::python::PeImportTable_Type)

/*! Returns the triton::format::pe::PeImportDirectory. */
#define PyPeImportTable_AsPeImportDirectory(v) (((triton::bindings::python::PeImportTable_Object*)(v))->impt)

/*! Checks if the pyObject is a triton::format::pe::PeImportLookup. */
#define PyPeImportLookup_Check(v) ((v)->ob_type == &triton::bindings::python::PeImportLookup_Type)

/*! Returns the triton::format::pe::PeImportLookup. */
#define PyPeImportLookup_AsPeImportLookup(v) (((triton::bindings::python::PeImportLookup_Object*)(v))->impt)

/*! Checks if the pyObject is a triton::format::pe::PeExportDirectory. */
#define PyPeExportTable_Check(v) ((v)->ob_type == &triton::bindings::python::PeExportTable_Type)

/*! Returns the triton::format::pe::PeExportDirectory. */
#define PyPeExportTable_AsPeExportDirectory(v) (((triton::bindings::python::PeExportTable_Object*)(v))->expt)

/*! Checks if the pyObject is a triton::format::pe::PeExportEntry. */
#define PyPeExportEntry_Check(v) ((v)->ob_type == &triton::bindings::python::PeExportEntry_Type)

/*! Returns the triton::format::pe::PeExportEntry. */
#define PyPeExportEntry_AsPeExportEntry(v) (((triton::bindings::python::PeExportEntry_Object*)(v))->impt)

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
