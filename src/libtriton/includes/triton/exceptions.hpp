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

#include <triton/triton_export.h>
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
        TRITON_EXPORT Exception(const char* message) {
          this->message = std::string(message);
        };

        //! Constructor.
        TRITON_EXPORT Exception(const std::string& message) {
          this->message = message;
        };

        //! Destructor.
        TRITON_EXPORT virtual ~Exception() throw() {
        };

        //! Returns the exception message.
        TRITON_EXPORT const char* what() const throw () {
          return this->message.c_str();
        };
    };


    /*! \class Engines
     *  \brief The exception class used by all engines. */
    class Engines : public triton::exceptions::Exception {
      public:
        //! Constructor.
        TRITON_EXPORT Engines(const char* message) : triton::exceptions::Exception(message) {};

        //! Constructor.
        TRITON_EXPORT Engines(const std::string& message) : triton::exceptions::Exception(message) {};
    };


    /*! \class SymbolicEngine
     *  \brief The exception class used by the symbolic engine. */
    class SymbolicEngine : public triton::exceptions::Engines {
      public:
        //! Constructor.
        TRITON_EXPORT SymbolicEngine(const char* message) : triton::exceptions::Engines(message) {};

        //! Constructor.
        TRITON_EXPORT SymbolicEngine(const std::string& message) : triton::exceptions::Engines(message) {};
    };


    /*! \class SymbolicExpression
     *  \brief The exception class used by symbolic expressions. */
    class SymbolicExpression : public triton::exceptions::SymbolicEngine {
      public:
        //! Constructor.
        TRITON_EXPORT SymbolicExpression(const char* message) : triton::exceptions::SymbolicEngine(message) {};

        //! Constructor.
        TRITON_EXPORT SymbolicExpression(const std::string& message) : triton::exceptions::SymbolicEngine(message) {};
    };


    /*! \class SymbolicSimplification
     *  \brief The exception class used by symbolic simplifications. */
    class SymbolicSimplification : public triton::exceptions::SymbolicEngine {
      public:
        //! Constructor.
        TRITON_EXPORT SymbolicSimplification(const char* message) : triton::exceptions::SymbolicEngine(message) {};

        //! Constructor.
        TRITON_EXPORT SymbolicSimplification(const std::string& message) : triton::exceptions::SymbolicEngine(message) {};
    };


    /*! \class SymbolicVariable
     *  \brief The exception class used by symbolic variables. */
    class SymbolicVariable : public triton::exceptions::SymbolicEngine {
      public:
        //! Constructor.
        TRITON_EXPORT SymbolicVariable(const char* message) : triton::exceptions::SymbolicEngine(message) {};

        //! Constructor.
        TRITON_EXPORT SymbolicVariable(const std::string& message) : triton::exceptions::SymbolicEngine(message) {};
    };


    /*! \class PathConstraint
     *  \brief The exception class used by path constraints. */
    class PathConstraint : public triton::exceptions::SymbolicEngine {
      public:
        //! Constructor.
        TRITON_EXPORT PathConstraint(const char* message) : triton::exceptions::SymbolicEngine(message) {};

        //! Constructor.
        TRITON_EXPORT PathConstraint(const std::string& message) : triton::exceptions::SymbolicEngine(message) {};
    };


    /*! \class PathManager
     *  \brief The exception class used by the path manager. */
    class PathManager : public triton::exceptions::SymbolicEngine {
      public:
        //! Constructor.
        TRITON_EXPORT PathManager(const char* message) : triton::exceptions::SymbolicEngine(message) {};

        //! Constructor.
        TRITON_EXPORT PathManager(const std::string& message) : triton::exceptions::SymbolicEngine(message) {};
    };


    /*! \class TaintEngine
     *  \brief The exception class used by the taint engine. */
    class TaintEngine : public triton::exceptions::Engines {
      public:
        //! Constructor.
        TRITON_EXPORT TaintEngine(const char* message) : triton::exceptions::Engines(message) {};

        //! Constructor.
        TRITON_EXPORT TaintEngine(const std::string& message) : triton::exceptions::Engines(message) {};
    };


    /*! \class SolverEngine
     *  \brief The exception class used by the solver engine. */
    class SolverEngine : public triton::exceptions::Engines {
      public:
        //! Constructor.
        TRITON_EXPORT SolverEngine(const char* message) : triton::exceptions::Engines(message) {};

        //! Constructor.
        TRITON_EXPORT SolverEngine(const std::string& message) : triton::exceptions::Engines(message) {};
    };


    /*! \class SolverModel
     *  \brief The exception class used by solver models. */
    class SolverModel : public triton::exceptions::SolverEngine {
      public:
        //! Constructor.
        TRITON_EXPORT SolverModel(const char* message) : triton::exceptions::SolverEngine(message) {};

        //! Constructor.
        TRITON_EXPORT SolverModel(const std::string& message) : triton::exceptions::SolverEngine(message) {};
    };


    /*! \class API
     *  \brief The exception class used by the Triton's API. */
    class API : public triton::exceptions::Exception {
      public:
        //! Constructor.
        TRITON_EXPORT API(const char* message) : triton::exceptions::Exception(message) {};

        //! Constructor.
        TRITON_EXPORT API(const std::string& message) : triton::exceptions::Exception(message) {};
    };


    /*! \class Architecture
     *  \brief The exception class used by architectures. */
    class Architecture : public triton::exceptions::Exception {
      public:
        //! Constructor.
        TRITON_EXPORT Architecture(const char* message) : triton::exceptions::Exception(message) {};

        //! Constructor.
        TRITON_EXPORT Architecture(const std::string& message) : triton::exceptions::Exception(message) {};
    };


    /*! \class BitsVector
     *  \brief The exception class used by bitvectors. */
    class BitsVector : public triton::exceptions::Architecture {
      public:
        //! Constructor.
        TRITON_EXPORT BitsVector(const char* message) : triton::exceptions::Architecture(message) {};

        //! Constructor.
        TRITON_EXPORT BitsVector(const std::string& message) : triton::exceptions::Architecture(message) {};
    };


    /*! \class Immediate
     *  \brief The exception class used by immediates. */
    class Immediate : public triton::exceptions::Architecture {
      public:
        //! Constructor.
        TRITON_EXPORT Immediate(const char* message) : triton::exceptions::Architecture(message) {};

        //! Constructor.
        TRITON_EXPORT Immediate(const std::string& message) : triton::exceptions::Architecture(message) {};
    };


    /*! \class Register
     *  \brief The exception class used by register operands. */
    class Register : public triton::exceptions::Architecture {
      public:
        //! Constructor.
        TRITON_EXPORT Register(const char* message) : triton::exceptions::Architecture(message) {};

        //! Constructor.
        TRITON_EXPORT Register(const std::string& message) : triton::exceptions::Architecture(message) {};
    };


    /*! \class MemoryAccess
     *  \brief The exception class used by memory access. */
    class MemoryAccess : public triton::exceptions::Architecture {
      public:
        //! Constructor.
        TRITON_EXPORT MemoryAccess(const char* message) : triton::exceptions::Architecture(message) {};

        //! Constructor.
        TRITON_EXPORT MemoryAccess(const std::string& message) : triton::exceptions::Architecture(message) {};
    };


    /*! \class OperandWrapper
     *  \brief The exception class used by operand wrappers. */
    class OperandWrapper : public triton::exceptions::Architecture {
      public:
        //! Constructor.
        TRITON_EXPORT OperandWrapper(const char* message) : triton::exceptions::Architecture(message) {};

        //! Constructor.
        TRITON_EXPORT OperandWrapper(const std::string& message) : triton::exceptions::Architecture(message) {};
    };


    /*! \class Instruction
     *  \brief The exception class used by an instruction. */
    class Instruction : public triton::exceptions::Architecture {
      public:
        //! Constructor.
        TRITON_EXPORT Instruction(const char* message) : triton::exceptions::Architecture(message) {};

        //! Constructor.
        TRITON_EXPORT Instruction(const std::string& message) : triton::exceptions::Architecture(message) {};
    };


    /*! \class Cpu
     *  \brief The exception class used by all CPUs. */
    class Cpu : public triton::exceptions::Architecture {
      public:
        //! Constructor.
        TRITON_EXPORT Cpu(const char* message) : triton::exceptions::Architecture(message) {};

        //! Constructor.
        TRITON_EXPORT Cpu(const std::string& message) : triton::exceptions::Architecture(message) {};
    };


    /*! \class AArch64OperandProperties
     *  \brief The exception class used by shift mode. */
    class AArch64OperandProperties : public triton::exceptions::Architecture {
      public:
        //! Constructor.
        TRITON_EXPORT AArch64OperandProperties(const char* message) : triton::exceptions::Architecture(message) {};

        //! Constructor.
        TRITON_EXPORT AArch64OperandProperties(const std::string& message) : triton::exceptions::Architecture(message) {};
    };


    /*! \class IrBuilder
     *  \brief The exception class used by the IR builder. */
    class IrBuilder : public triton::exceptions::Architecture {
      public:
        //! Constructor.
        TRITON_EXPORT IrBuilder(const char* message) : triton::exceptions::Architecture(message) {};

        //! Constructor.
        TRITON_EXPORT IrBuilder(const std::string& message) : triton::exceptions::Architecture(message) {};
    };


    /*! \class Disassembly
     *  \brief The exception class used by the disassembler. */
    class Disassembly : public triton::exceptions::Cpu {
      public:
        //! Constructor.
        TRITON_EXPORT Disassembly(const char* message) : triton::exceptions::Cpu(message) {};

        //! Constructor.
        TRITON_EXPORT Disassembly(const std::string& message) : triton::exceptions::Cpu(message) {};
    };


    /*! \class Semantics
     *  \brief The exception class used by all semantics. */
    class Semantics : public triton::exceptions::Cpu {
      public:
        //! Constructor.
        TRITON_EXPORT Semantics(const char* message) : triton::exceptions::Cpu(message) {};

        //! Constructor.
        TRITON_EXPORT Semantics(const std::string& message) : triton::exceptions::Cpu(message) {};
    };


    /*! \class Ast
     *  \brief The exception class used by all AST nodes. */
    class Ast : public triton::exceptions::Exception {
      public:
        //! Constructor.
        TRITON_EXPORT Ast(const char* message) : triton::exceptions::Exception(message) {};

        //! Constructor.
        TRITON_EXPORT Ast(const std::string& message) : triton::exceptions::Exception(message) {};
    };


    /*! \class AstRepresentation
     *  \brief The exception class used by all AST node representations. */
    class AstRepresentation : public triton::exceptions::Ast {
      public:
        //! Constructor.
        TRITON_EXPORT AstRepresentation(const char* message) : triton::exceptions::Ast(message) {};

        //! Constructor.
        TRITON_EXPORT AstRepresentation(const std::string& message) : triton::exceptions::Ast(message) {};
    };


    /*! \class AstTranslations
     *  \brief The exception class used by all AST translations (`z3 <-> triton`). */
    class AstTranslations : public triton::exceptions::Ast {
      public:
        //! Constructor.
        TRITON_EXPORT AstTranslations(const char* message) : triton::exceptions::Ast(message) {};

        //! Constructor.
        TRITON_EXPORT AstTranslations(const std::string& message) : triton::exceptions::Ast(message) {};
    };


    /*! \class Bindings
     *  \brief The exception class used by bindings. */
    class Bindings : public triton::exceptions::Exception {
      public:
        //! Constructor.
        TRITON_EXPORT Bindings(const char* message) : triton::exceptions::Exception(message) {};

        //! Constructor.
        TRITON_EXPORT Bindings(const std::string& message) : triton::exceptions::Exception(message) {};
    };


    /*! \class Callbacks
     *  \brief The exception class used by callbacks. */
    class Callbacks : public triton::exceptions::Exception {
      public:
        //! Constructor.
        TRITON_EXPORT Callbacks(const char* message) : triton::exceptions::Exception(message) {};

        //! Constructor.
        TRITON_EXPORT Callbacks(const std::string& message) : triton::exceptions::Exception(message) {};
    };

    /*! \class Callbacks
     *  \brief The exception class used by python callbacks. */
    class PyCallbacks : public triton::exceptions::Exception {
    public:
      //! Constructor.
      TRITON_EXPORT PyCallbacks() : triton::exceptions::Exception("exception info is stored in python state") {};
    };

  /*! @} End of exceptions namespace */
  };
/*! @} End of exceptions namespace */
};

#endif /* TRITON_EXCEPTIONS_HPP */
