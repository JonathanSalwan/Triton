//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>
#include <smt2libPythonSyntax.hpp>



namespace triton {
  namespace smt2lib {
    namespace pseudocode {

      PythonSyntax::PythonSyntax() {
      }


      PythonSyntax::~PythonSyntax() {
      }


      /* Syntax dispatcher from an abstract node */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstAbstractNode* node) {
        switch (node->getKind()) {
          case ASSERT_NODE:               return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstAssertNode*>(node)); break;
          case BVADD_NODE:                return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvaddNode*>(node)); break;
          case BVAND_NODE:                return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvandNode*>(node)); break;
          case BVASHR_NODE:               return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvashrNode*>(node)); break;
          case BVDECL_NODE:               return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvdeclNode*>(node)); break;
          case BVLSHR_NODE:               return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvlshrNode*>(node)); break;
          case BVMUL_NODE:                return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvmulNode*>(node)); break;
          case BVNAND_NODE:               return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvnandNode*>(node)); break;
          case BVNEG_NODE:                return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvnegNode*>(node)); break;
          case BVNOR_NODE:                return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvnorNode*>(node)); break;
          case BVNOT_NODE:                return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvnotNode*>(node)); break;
          case BVOR_NODE:                 return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvorNode*>(node)); break;
          case BVROL_NODE:                return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvrolNode*>(node)); break;
          case BVROR_NODE:                return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvrorNode*>(node)); break;
          case BVSDIV_NODE:               return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvsdivNode*>(node)); break;
          case BVSGE_NODE:                return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvsgeNode*>(node)); break;
          case BVSGT_NODE:                return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvsgtNode*>(node)); break;
          case BVSHL_NODE:                return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvshlNode*>(node)); break;
          case BVSLE_NODE:                return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvsleNode*>(node)); break;
          case BVSLT_NODE:                return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvsltNode*>(node)); break;
          case BVSMOD_NODE:               return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvsmodNode*>(node)); break;
          case BVSREM_NODE:               return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvsremNode*>(node)); break;
          case BVSUB_NODE:                return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvsubNode*>(node)); break;
          case BVUDIV_NODE:               return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvudivNode*>(node)); break;
          case BVUGE_NODE:                return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvugeNode*>(node)); break;
          case BVUGT_NODE:                return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvugtNode*>(node)); break;
          case BVULE_NODE:                return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvuleNode*>(node)); break;
          case BVULT_NODE:                return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvultNode*>(node)); break;
          case BVUREM_NODE:               return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvuremNode*>(node)); break;
          case BVXNOR_NODE:               return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvxnorNode*>(node)); break;
          case BVXOR_NODE:                return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvxorNode*>(node)); break;
          case BV_NODE:                   return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstBvNode*>(node)); break;
          case COMPOUND_NODE:             return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstCompoundNode*>(node)); break;
          case CONCAT_NODE:               return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstConcatNode*>(node)); break;
          case DECIMAL_NODE:              return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstDecimalNode*>(node)); break;
          case DECLARE_FUNCTION_NODE:     return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstDeclareFunctionNode*>(node)); break;
          case DISTINCT_NODE:             return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstDistinctNode*>(node)); break;
          case EQUAL_NODE:                return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstEqualNode*>(node)); break;
          case EXTRACT_NODE:              return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstExtractNode*>(node)); break;
          case ITE_NODE:                  return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstIteNode*>(node)); break;
          case LAND_NODE:                 return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstLandNode*>(node)); break;
          case LET_NODE:                  return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstLetNode*>(node)); break;
          case LNOT_NODE:                 return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstLnotNode*>(node)); break;
          case LOR_NODE:                  return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstLorNode*>(node)); break;
          case REFERENCE_NODE:            return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstReferenceNode*>(node)); break;
          case STRING_NODE:               return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstStringNode*>(node)); break;
          case SX_NODE:                   return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstSxNode*>(node)); break;
          case VARIABLE_NODE:             return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstVariableNode*>(node)); break;
          case ZX_NODE:                   return this->display(stream, reinterpret_cast<triton::smt2lib::smtAstZxNode*>(node)); break;
          default:
            throw std::invalid_argument("triton::smt2lib::PythonSyntax::display(smtAstAbstractNode) - Invalid kind node");
        }
        return stream;
      }


      /* assert syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstAssertNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvadd syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvaddNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvand syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvandNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvashr syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvashrNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvdecl syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvdeclNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvlshr syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvlshrNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvmul syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvmulNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvnand syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvnandNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvneg syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvnegNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvnor syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvnorNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvnot syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvnotNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvor syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvorNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvrol syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvrolNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvror syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvrorNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvsdiv syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvsdivNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvsge syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvsgeNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvsgt syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvsgtNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvshl syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvshlNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvsle syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvsleNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvslt syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvsltNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvsmod syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvsmodNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvsrem syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvsremNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvsub syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvsubNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvudiv syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvudivNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvuge syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvugeNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvugt syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvugtNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvule syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvuleNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvult syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvultNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvurem syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvuremNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvxnor syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvxnorNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bvxor syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvxorNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* bv syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* compound syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstCompoundNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* concat syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstConcatNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* decimal syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstDecimalNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* declare syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstDeclareFunctionNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* distinct syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstDistinctNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* equal syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstEqualNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* extract syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstExtractNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* ite syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstIteNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* land syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstLandNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* let syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstLetNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* lnot syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstLnotNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* lor syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstLorNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* reference syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstReferenceNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* string syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstStringNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* sx syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstSxNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* variable syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstVariableNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }


      /* zx syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstZxNode* node) {
        throw std::invalid_argument("Not implemented yet.");
        return stream;
      }

    };
  };
};


