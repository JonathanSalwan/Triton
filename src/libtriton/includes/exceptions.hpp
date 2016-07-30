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

#include "tritonTypes.hpp"



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


    /*! \class SymbolicOptimization
     *  \brief The exception class used by symbolic optimizations. */
    class SymbolicOptimization : public triton::exceptions::SymbolicEngine {
      public:
        //! Constructor.
        SymbolicOptimization(const char* message) : triton::exceptions::SymbolicEngine(message) {};

        //! Constructor.
        SymbolicOptimization(const std::string& message) : triton::exceptions::SymbolicEngine(message) {};
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


    /*! \class ImmediateOperand
     *  \brief The exception class used by immediate operands. */
    class ImmediateOperand : public triton::exceptions::Architecture {
      public:
        //! Constructor.
        ImmediateOperand(const char* message) : triton::exceptions::Architecture(message) {};

        //! Constructor.
        ImmediateOperand(const std::string& message) : triton::exceptions::Architecture(message) {};
    };


    /*! \class RegisterOperand
     *  \brief The exception class used by register operands. */
    class RegisterOperand : public triton::exceptions::Architecture {
      public:
        //! Constructor.
        RegisterOperand(const char* message) : triton::exceptions::Architecture(message) {};

        //! Constructor.
        RegisterOperand(const std::string& message) : triton::exceptions::Architecture(message) {};
    };


    /*! \class MemoryOperand
     *  \brief The exception class used by memory operands. */
    class MemoryOperand : public triton::exceptions::Architecture {
      public:
        //! Constructor.
        MemoryOperand(const char* message) : triton::exceptions::Architecture(message) {};

        //! Constructor.
        MemoryOperand(const std::string& message) : triton::exceptions::Architecture(message) {};
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


    /*! \class CPU
     *  \brief The exception class used by all CPUs. */
    class CPU : public triton::exceptions::Architecture {
      public:
        //! Constructor.
        CPU(const char* message) : triton::exceptions::Architecture(message) {};

        //! Constructor.
        CPU(const std::string& message) : triton::exceptions::Architecture(message) {};
    };


    /*! \class Disassembly
     *  \brief The exception class used by the disassembler. */
    class Disassembly : public triton::exceptions::CPU {
      public:
        //! Constructor.
        Disassembly(const char* message) : triton::exceptions::CPU(message) {};

        //! Constructor.
        Disassembly(const std::string& message) : triton::exceptions::CPU(message) {};
    };


    /*! \class Semantics
     *  \brief The exception class used by all semantics. */
    class Semantics : public triton::exceptions::CPU {
      public:
        //! Constructor.
        Semantics(const char* message) : triton::exceptions::CPU(message) {};

        //! Constructor.
        Semantics(const std::string& message) : triton::exceptions::CPU(message) {};
    };


    /*! \class AST
     *  \brief The exception class used by all AST nodes. */
    class AST : public triton::exceptions::Exception {
      public:
        //! Constructor.
        AST(const char* message) : triton::exceptions::Exception(message) {};

        //! Constructor.
        AST(const std::string& message) : triton::exceptions::Exception(message) {};
    };


    /*! \class ASTRepresentation
     *  \brief The exception class used by all AST node representations. */
    class ASTRepresentation : public triton::exceptions::AST {
      public:
        //! Constructor.
        ASTRepresentation(const char* message) : triton::exceptions::AST(message) {};

        //! Constructor.
        ASTRepresentation(const std::string& message) : triton::exceptions::AST(message) {};
    };


    /*! \class ASTTranslations
     *  \brief The exception class used by all AST translations (`z3 <-> triton`). */
    class ASTTranslations : public triton::exceptions::AST {
      public:
        //! Constructor.
        ASTTranslations(const char* message) : triton::exceptions::AST(message) {};

        //! Constructor.
        ASTTranslations(const std::string& message) : triton::exceptions::AST(message) {};
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


    /*! \class ELF
     *  \brief The exception class used by the ELF format. */
    class ELF : public triton::exceptions::Format {
      public:
        //! Constructor.
        ELF(const char* message) : triton::exceptions::Format(message) {};

        //! Constructor.
        ELF(const std::string& message) : triton::exceptions::Format(message) {};
    };

  /*! @} End of exceptions namespace */
  };
/*! @} End of exceptions namespace */
};

#endif /* TRITON_EXCEPTIONS_HPP */
