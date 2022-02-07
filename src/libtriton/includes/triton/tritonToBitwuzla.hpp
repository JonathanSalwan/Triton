//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_TRITONTOBITWUZLA_H
#define TRITON_TRITONTOBITWUZLA_H

#include <map>
#include <unordered_map>

#include <bitwuzla/bitwuzla.h>

#include <triton/ast.hpp>
#include <triton/dllexport.hpp>
#include <triton/tritonTypes.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The AST namespace
  namespace ast {
  /*!
   *  \ingroup triton
   *  \addtogroup ast
   *  @{
   */

    //! \class TritonToBitwuzla
    /*! \brief Converts a Triton's AST to Bitwuzla's AST. */
    class TritonToBitwuzla {
      public:
        //! Constructor.
        TRITON_EXPORT TritonToBitwuzla(bool eval=false);

        //! Destructor.
        TRITON_EXPORT ~TritonToBitwuzla();

        //! Converts to Bitwuzla's AST
        TRITON_EXPORT const BitwuzlaTerm* convert(const SharedAbstractNode& node, Bitwuzla* bzla);

        //! Returns symbolic variables and its assosiated Bitwuzla terms to process the solver model.
        TRITON_EXPORT const std::unordered_map<const BitwuzlaTerm*, triton::engines::symbolic::SharedSymbolicVariable>& getVariables(void) const;

        //! Returns bitvector sorts.
        TRITON_EXPORT const std::map<size_t, const BitwuzlaSort*>& getBitvectorSorts(void) const;

      private:
        //! The map of Triton's AST nodes translated to the Bitwuzla terms.
        std::unordered_map<SharedAbstractNode, const BitwuzlaTerm*> translatedNodes;

        //! The set of symbolic variables contained in the expression.
        std::unordered_map<const BitwuzlaTerm*, triton::engines::symbolic::SharedSymbolicVariable> variables;

        //! The map of symbols. E.g: (let (symbols expr1) expr2)
        std::unordered_map<std::string, triton::ast::SharedAbstractNode> symbols;

        //! All bitvector sorts that used in the expression.
        std::map<size_t, const BitwuzlaSort*> bvSorts;

        //! This flag define if the conversion is used to evaluated a node or not.
        bool isEval;

        //! The convert internal process.
        const BitwuzlaTerm* translate(const SharedAbstractNode& node, Bitwuzla* bzla);
    };

  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_TRITONTOBITWUZLA_H */
