//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_EXCEPTIONS_H
#define TRITON_EXCEPTIONS_H

#include <exception>
#include <string>

#include <triton/tritonTypes.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Exceptions namespace
  namespace exceptions {
  /*!
   *  \ingroup triton
   *  \addtogroup exceptions
   *  @{
   */

    /*! \class Exception
     *  \brief The root class of all exceptions. */
    class Exception : public std::exception {
      protected:
        //! Defines the exception message.
        std::string message;

      public:
        //! Constructor.
        Exception(const char* message) {
          this->message = std::string(message);
        };

        //! Constructor.
        Exception(const std::string& message) {
          this->message = message;
        };

        //! Destructor.
        virtual ~Exception() throw() {
        };

        //! Returns the exception message.
        const char* what() const throw () {
          return this->message.c_str();
        };
    };


    /*! \class Engines
     *  \brief The exception class used by all engines. */
    class Engines : public triton::exceptions::Exception {
      public:
        //! Constructor.
        Engines(const char* message) : triton::exceptions::Exception(message) {};

        //! Constructor.
        Engines(const std::string& message) : triton::exceptions::Exception(message) {};
    };


    /*! \class SymbolicEngine
     *  \brief The exception class used by the symbolic engine. */
    class SymbolicEngine : public triton::exceptions::Engines {
      public:
        //! Constructor.
        SymbolicEngine(const char* message) : triton::exceptions::Engines(message) {};

        //! Constructor.
        SymbolicEngine(const std::string& message) : triton::exceptions::Engines(message) {};
    };


    /*! \class SymbolicExpression
     *  \brief The exception class used by symbolic expressions. */
    class SymbolicExpression : public triton::exceptions::SymbolicEngine {
      public:
        //! Constructor.
        SymbolicExpression(const char* message) : triton::exceptions::SymbolicEngine(message) {};

        //! Constructor.
        SymbolicExpression(const std::string& message) : triton::exceptions::SymbolicEngine(message) {};
    };


    /*! \class SymbolicSimplification
     *  \brief The exception class used by symbolic simplifications. */
    class SymbolicSimplification : public triton::exceptions::SymbolicEngine {
      public:
        //! Constructor.
        SymbolicSimplification(const char* message) : triton::exceptions::SymbolicEngine(message) {};

        //! Constructor.
        SymbolicSimplification(const std::string& message) : triton::exceptions::SymbolicEngine(message) {};
    };


    /*! \class SymbolicVariable
     *  \brief The exception class used by symbolic variables. */
    class SymbolicVariable : public triton::exceptions::SymbolicEngine {
      public:
        //! Constructor.
        SymbolicVariable(const char* message) : triton::exceptions::SymbolicEngine(message) {};

        //! Constructor.
        SymbolicVariable(const std::string& message) : triton::exceptions::SymbolicEngine(message) {};
    };


    /*! \class PathConstraint
     *  \brief The exception class used by path constraints. */
    class PathConstraint : public triton::exceptions::SymbolicEngine {
      public:
        //! Constructor.
        PathConstraint(const char* message) : triton::exceptions::SymbolicEngine(message) {};

        //! Constructor.
        PathConstraint(const std::string& message) : triton::exceptions::SymbolicEngine(message) {};
    };


    /*! \class PathManager
     *  \brief The exception class used by the path manager. */
    class PathManager : public triton::exceptions::SymbolicEngine {
      public:
        //! Constructor.
        PathManager(const char* message) : triton::exceptions::SymbolicEngine(message) {};

        //! Constructor.
        PathManager(const std::string& message) : triton::exceptions::SymbolicEngine(message) {};
    };


    /*! \class TaintEngine
     *  \brief The exception class used by the taint engine. */
    class TaintEngine : public triton::exceptions::Engines {
      public:
        //! Constructor.
        TaintEngine(const char* message) : triton::exceptions::Engines(message) {};

        //! Constructor.
        TaintEngine(const std::string& message) : triton::exceptions::Engines(message) {};
    };


    /*! \class SolverEngine
     *  \brief The exception class used by the solver engine. */
    class SolverEngine : public triton::exceptions::Engines {
      public:
        //! Constructor.
        SolverEngine(const char* message) : triton::exceptions::Engines(message) {};

        //! Constructor.
        SolverEngine(const std::string& message) : triton::exceptions::Engines(message) {};
    };


    /*! \class SolverModel
     *  \brief The exception class used by solver models. */
    class SolverModel : public triton::exceptions::SolverEngine {
      public:
        //! Constructor.
        SolverModel(const char* message) : triton::exceptions::SolverEngine(message) {};

        //! Constructor.
        SolverModel(const std::string& message) : triton::exceptions::SolverEngine(message) {};
    };


    /*! \class API
     *  \brief The exception class used by the Triton's API. */
    class API : public triton::exceptions::Exception {
      public:
        //! Constructor.
        API(const char* message) : triton::exceptions::Exception(message) {};

        //! Constructor.
        API(const std::string& message) : triton::exceptions::Exception(message) {};
    };


    /*! \class Architecture
     *  \brief The exception class used by architectures. */
    class Architecture : public triton::exceptions::Exception {
      public:
        //! Constructor.
        Architecture(const char* message) : triton::exceptions::Exception(message) {};

        //! Constructor.
        Architecture(const std::string& message) : triton::exceptions::Exception(message) {};
    };


    /*! \class BitsVector
     *  \brief The exception class used by bitvectors. */
    class BitsVector : public triton::exceptions::Architecture {
      public:
        //! Constructor.
        BitsVector(const char* message) : triton::exceptions::Architecture(message) {};

        //! Constructor.
        BitsVector(const std::string& message) : triton::exceptions::Architecture(message) {};
    };


    /*! \class Immediate
     *  \brief The exception class used by immediates. */
    class Immediate : public triton::exceptions::Architecture {
      public:
        //! Constructor.
        Immediate(const char* message) : triton::exceptions::Architecture(message) {};

        //! Constructor.
        Immediate(const std::string& message) : triton::exceptions::Architecture(message) {};
    };


    /*! \class Register
     *  \brief The exception class used by register operands. */
    class Register : public triton::exceptions::Architecture {
      public:
        //! Constructor.
        Register(const char* message) : triton::exceptions::Architecture(message) {};

        //! Constructor.
        Register(const std::string& message) : triton::exceptions::Architecture(message) {};
    };


    /*! \class MemoryAccess
     *  \brief The exception class used by memory access. */
    class MemoryAccess : public triton::exceptions::Architecture {
      public:
        //! Constructor.
        MemoryAccess(const char* message) : triton::exceptions::Architecture(message) {};

        //! Constructor.
        MemoryAccess(const std::string& message) : triton::exceptions::Architecture(message) {};
    };


    /*! \class OperandWrapper
     *  \brief The exception class used by operand wrappers. */
    class OperandWrapper : public triton::exceptions::Architecture {
      public:
        //! Constructor.
        OperandWrapper(const char* message) : triton::exceptions::Architecture(message) {};

        //! Constructor.
        OperandWrapper(const std::string& message) : triton::exceptions::Architecture(message) {};
    };


    /*! \class Instruction
     *  \brief The exception class used by an instruction. */
    class Instruction : public triton::exceptions::Architecture {
      public:
        //! Constructor.
        Instruction(const char* message) : triton::exceptions::Architecture(message) {};

        //! Constructor.
        Instruction(const std::string& message) : triton::exceptions::Architecture(message) {};
    };


    /*! \class Cpu
     *  \brief The exception class used by all CPUs. */
    class Cpu : public triton::exceptions::Architecture {
      public:
        //! Constructor.
        Cpu(const char* message) : triton::exceptions::Architecture(message) {};

        //! Constructor.
        Cpu(const std::string& message) : triton::exceptions::Architecture(message) {};
    };


    /*! \class IrBuilder
     *  \brief The exception class used by the IR builder. */
    class IrBuilder : public triton::exceptions::Architecture {
      public:
        //! Constructor.
        IrBuilder(const char* message) : triton::exceptions::Architecture(message) {};

        //! Constructor.
        IrBuilder(const std::string& message) : triton::exceptions::Architecture(message) {};
    };


    /*! \class Disassembly
     *  \brief The exception class used by the disassembler. */
    class Disassembly : public triton::exceptions::Cpu {
      public:
        //! Constructor.
        Disassembly(const char* message) : triton::exceptions::Cpu(message) {};

        //! Constructor.
        Disassembly(const std::string& message) : triton::exceptions::Cpu(message) {};
    };


    /*! \class Semantics
     *  \brief The exception class used by all semantics. */
    class Semantics : public triton::exceptions::Cpu {
      public:
        //! Constructor.
        Semantics(const char* message) : triton::exceptions::Cpu(message) {};

        //! Constructor.
        Semantics(const std::string& message) : triton::exceptions::Cpu(message) {};
    };


    /*! \class Ast
     *  \brief The exception class used by all AST nodes. */
    class Ast : public triton::exceptions::Exception {
      public:
        //! Constructor.
        Ast(const char* message) : triton::exceptions::Exception(message) {};

        //! Constructor.
        Ast(const std::string& message) : triton::exceptions::Exception(message) {};
    };


    /*! \class AstRepresentation
     *  \brief The exception class used by all AST node representations. */
    class AstRepresentation : public triton::exceptions::Ast {
      public:
        //! Constructor.
        AstRepresentation(const char* message) : triton::exceptions::Ast(message) {};

        //! Constructor.
        AstRepresentation(const std::string& message) : triton::exceptions::Ast(message) {};
    };


    /*! \class AstTranslations
     *  \brief The exception class used by all AST translations (`z3 <-> triton`). */
    class AstTranslations : public triton::exceptions::Ast {
      public:
        //! Constructor.
        AstTranslations(const char* message) : triton::exceptions::Ast(message) {};

        //! Constructor.
        AstTranslations(const std::string& message) : triton::exceptions::Ast(message) {};
    };


    /*! \class AstGarbageCollector
     *  \brief The exception class used by all AST garbage collector. */
    class AstGarbageCollector : public triton::exceptions::Ast {
      public:
        //! Constructor.
        AstGarbageCollector(const char* message) : triton::exceptions::Ast(message) {};

        //! Constructor.
        AstGarbageCollector(const std::string& message) : triton::exceptions::Ast(message) {};
    };


    /*! \class Bindings
     *  \brief The exception class used by bindings. */
    class Bindings : public triton::exceptions::Exception {
      public:
        //! Constructor.
        Bindings(const char* message) : triton::exceptions::Exception(message) {};

        //! Constructor.
        Bindings(const std::string& message) : triton::exceptions::Exception(message) {};
    };


    /*! \class Format
     *  \brief The exception class used by all binary formats. */
    class Format : public triton::exceptions::Exception {
      public:
        //! Constructor.
        Format(const char* message) : triton::exceptions::Exception(message) {};

        //! Constructor.
        Format(const std::string& message) : triton::exceptions::Exception(message) {};
    };


    /*! \class Elf
     *  \brief The exception class used by the ELF format. */
    class Elf : public triton::exceptions::Format {
      public:
        //! Constructor.
        Elf(const char* message) : triton::exceptions::Format(message) {};

        //! Constructor.
        Elf(const std::string& message) : triton::exceptions::Format(message) {};
    };


    /*! \class Pe
     *  \brief The exception class used by the PE format. */
    class Pe : public triton::exceptions::Format {
      public:
        //! Constructor.
        Pe(const char* message) : triton::exceptions::Format(message) {};

        //! Constructor.
        Pe(const std::string& message) : triton::exceptions::Format(message) {};
    };


    /*! \class Callbacks
     *  \brief The exception class used by callbacks. */
    class Callbacks : public triton::exceptions::Exception {
      public:
        //! Constructor.
        Callbacks(const char* message) : triton::exceptions::Exception(message) {};

        //! Constructor.
        Callbacks(const std::string& message) : triton::exceptions::Exception(message) {};
    };

  /*! @} End of exceptions namespace */
  };
/*! @} End of exceptions namespace */
};

#endif /* TRITON_EXCEPTIONS_HPP */
