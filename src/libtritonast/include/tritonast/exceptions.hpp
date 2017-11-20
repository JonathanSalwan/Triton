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

//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The ast namespace
  namespace ast {
  /*!
   *  \ingroup triton
   *  \addtogroup ast
   *  @{
   */

    //! The Exceptions namespace
    namespace exceptions {
    /*!
     *  \ingroup ast
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


      /*! \class SolverEngine
       *  \brief The exception class used by the solver engine. */
      class SolverEngine : public Exception {
        public:
          //! Constructor.
          SolverEngine(const char* message) : Exception(message) {};

          //! Constructor.
          SolverEngine(const std::string& message) : Exception(message) {};
      };


      /*! \class SolverModel
       *  \brief The exception class used by solver models. */
      class SolverModel : public Exception {
        public:
          //! Constructor.
          SolverModel(const char* message) : Exception(message) {};

          //! Constructor.
          SolverModel(const std::string& message) : Exception(message) {};
      };


      /*! \class Ast
       *  \brief The exception class used by all AST nodes. */
      class Ast : public Exception {
        public:
          //! Constructor.
          Ast(const char* message) : Exception(message) {};

          //! Constructor.
          Ast(const std::string& message) : Exception(message) {};
      };


      /*! \class Representation
       *  \brief The exception class used by all AST node representations. */
      class Representation : public triton::ast::exceptions::Ast {
        public:
          //! Constructor.
          Representation(const char* message) : triton::ast::exceptions::Ast(message) {};

          //! Constructor.
          Representation(const std::string& message) : triton::ast::exceptions::Ast(message) {};
      };


      /*! \class AstTranslations
       *  \brief The exception class used by all AST translations (`z3 <-> triton`). */
      class AstTranslations : public triton::ast::exceptions::Ast {
        public:
          //! Constructor.
          AstTranslations(const char* message) : triton::ast::exceptions::Ast(message) {};

          //! Constructor.
          AstTranslations(const std::string& message) : triton::ast::exceptions::Ast(message) {};
      };

    /*! @} End of exceptions namespace */
    };
  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_EXCEPTIONS_HPP */
