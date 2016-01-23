//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_SYMBOLICSUMMARY_H
#define TRITON_SYMBOLICSUMMARY_H

#include <list>

#include "smt2lib.hpp"
#include "tritonTypes.hpp"



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The Engines namespace
  namespace engines {
  /*!
   *  \ingroup triton
   *  \addtogroup engines
   *  @{
   */

    //! \module The Symbolic Execution namespace
    namespace symbolic {
    /*!
     *  \ingroup engines
     *  \addtogroup symbolic
     *  @{
     */

      /*! \class SymbolicSummary
          \brief The symbolic summary class. */
      class SymbolicSummary {

        protected:
          //! The node.
          triton::smt2lib::smtAstAbstractNode* node;

          //! The evaluated result.
          triton::uint512 result;

          //! The evaluated result size.
          triton::uint32 size;

          //! The number of references to this summary.
          triton::uint32 reference;

        public:
          //! Constructor.
          SymbolicSummary(triton::smt2lib::smtAstAbstractNode* node);

          //! Constructor by copy.
          SymbolicSummary(const SymbolicSummary& other);

          //! Destructor.
          ~SymbolicSummary();

          //! Returns the node.
          triton::smt2lib::smtAstAbstractNode* getNode(void);

          //! Returns the number of references to this summary.
          triton::uint32 getReference(void);

          //! Returns the evaluated result.
          triton::uint512 getResult(void);

          //! Returns the evaluated result size.
          triton::uint32 getSize(void);

          //! Increments the number of references to this summary.
          void incReference(void);

          //! Copies a SymbolicSummary.
          void operator=(const SymbolicSummary& other);
      };

      //! Compares two summaries
      bool operator==(SymbolicSummary& summary1, SymbolicSummary& summary2);

      //! The map for AST summaries.
      //! \brief <hash:summaries>
      extern std::map<triton::uint512, std::list<triton::engines::symbolic::SymbolicSummary>> astSummaries;

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SYMBOLICSUMMARY_H */

