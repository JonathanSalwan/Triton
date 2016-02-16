//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>
#include <astSmtRepresentation.hpp>



namespace triton {
  namespace ast {
    namespace representation {

      AstSmtRepresentation::AstSmtRepresentation() {
      }


      AstSmtRepresentation::~AstSmtRepresentation() {
      }


      /* Representation dispatcher from an abstract node */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstAbstractNode* node) {
        switch (node->getKind()) {
          case ASSERT_NODE:               return this->print(stream, reinterpret_cast<triton::ast::smtAstAssertNode*>(node)); break;
          case BVADD_NODE:                return this->print(stream, reinterpret_cast<triton::ast::smtAstBvaddNode*>(node)); break;
          case BVAND_NODE:                return this->print(stream, reinterpret_cast<triton::ast::smtAstBvandNode*>(node)); break;
          case BVASHR_NODE:               return this->print(stream, reinterpret_cast<triton::ast::smtAstBvashrNode*>(node)); break;
          case BVDECL_NODE:               return this->print(stream, reinterpret_cast<triton::ast::smtAstBvdeclNode*>(node)); break;
          case BVLSHR_NODE:               return this->print(stream, reinterpret_cast<triton::ast::smtAstBvlshrNode*>(node)); break;
          case BVMUL_NODE:                return this->print(stream, reinterpret_cast<triton::ast::smtAstBvmulNode*>(node)); break;
          case BVNAND_NODE:               return this->print(stream, reinterpret_cast<triton::ast::smtAstBvnandNode*>(node)); break;
          case BVNEG_NODE:                return this->print(stream, reinterpret_cast<triton::ast::smtAstBvnegNode*>(node)); break;
          case BVNOR_NODE:                return this->print(stream, reinterpret_cast<triton::ast::smtAstBvnorNode*>(node)); break;
          case BVNOT_NODE:                return this->print(stream, reinterpret_cast<triton::ast::smtAstBvnotNode*>(node)); break;
          case BVOR_NODE:                 return this->print(stream, reinterpret_cast<triton::ast::smtAstBvorNode*>(node)); break;
          case BVROL_NODE:                return this->print(stream, reinterpret_cast<triton::ast::smtAstBvrolNode*>(node)); break;
          case BVROR_NODE:                return this->print(stream, reinterpret_cast<triton::ast::smtAstBvrorNode*>(node)); break;
          case BVSDIV_NODE:               return this->print(stream, reinterpret_cast<triton::ast::smtAstBvsdivNode*>(node)); break;
          case BVSGE_NODE:                return this->print(stream, reinterpret_cast<triton::ast::smtAstBvsgeNode*>(node)); break;
          case BVSGT_NODE:                return this->print(stream, reinterpret_cast<triton::ast::smtAstBvsgtNode*>(node)); break;
          case BVSHL_NODE:                return this->print(stream, reinterpret_cast<triton::ast::smtAstBvshlNode*>(node)); break;
          case BVSLE_NODE:                return this->print(stream, reinterpret_cast<triton::ast::smtAstBvsleNode*>(node)); break;
          case BVSLT_NODE:                return this->print(stream, reinterpret_cast<triton::ast::smtAstBvsltNode*>(node)); break;
          case BVSMOD_NODE:               return this->print(stream, reinterpret_cast<triton::ast::smtAstBvsmodNode*>(node)); break;
          case BVSREM_NODE:               return this->print(stream, reinterpret_cast<triton::ast::smtAstBvsremNode*>(node)); break;
          case BVSUB_NODE:                return this->print(stream, reinterpret_cast<triton::ast::smtAstBvsubNode*>(node)); break;
          case BVUDIV_NODE:               return this->print(stream, reinterpret_cast<triton::ast::smtAstBvudivNode*>(node)); break;
          case BVUGE_NODE:                return this->print(stream, reinterpret_cast<triton::ast::smtAstBvugeNode*>(node)); break;
          case BVUGT_NODE:                return this->print(stream, reinterpret_cast<triton::ast::smtAstBvugtNode*>(node)); break;
          case BVULE_NODE:                return this->print(stream, reinterpret_cast<triton::ast::smtAstBvuleNode*>(node)); break;
          case BVULT_NODE:                return this->print(stream, reinterpret_cast<triton::ast::smtAstBvultNode*>(node)); break;
          case BVUREM_NODE:               return this->print(stream, reinterpret_cast<triton::ast::smtAstBvuremNode*>(node)); break;
          case BVXNOR_NODE:               return this->print(stream, reinterpret_cast<triton::ast::smtAstBvxnorNode*>(node)); break;
          case BVXOR_NODE:                return this->print(stream, reinterpret_cast<triton::ast::smtAstBvxorNode*>(node)); break;
          case BV_NODE:                   return this->print(stream, reinterpret_cast<triton::ast::smtAstBvNode*>(node)); break;
          case COMPOUND_NODE:             return this->print(stream, reinterpret_cast<triton::ast::smtAstCompoundNode*>(node)); break;
          case CONCAT_NODE:               return this->print(stream, reinterpret_cast<triton::ast::smtAstConcatNode*>(node)); break;
          case DECIMAL_NODE:              return this->print(stream, reinterpret_cast<triton::ast::smtAstDecimalNode*>(node)); break;
          case DECLARE_FUNCTION_NODE:     return this->print(stream, reinterpret_cast<triton::ast::smtAstDeclareFunctionNode*>(node)); break;
          case DISTINCT_NODE:             return this->print(stream, reinterpret_cast<triton::ast::smtAstDistinctNode*>(node)); break;
          case EQUAL_NODE:                return this->print(stream, reinterpret_cast<triton::ast::smtAstEqualNode*>(node)); break;
          case EXTRACT_NODE:              return this->print(stream, reinterpret_cast<triton::ast::smtAstExtractNode*>(node)); break;
          case ITE_NODE:                  return this->print(stream, reinterpret_cast<triton::ast::smtAstIteNode*>(node)); break;
          case LAND_NODE:                 return this->print(stream, reinterpret_cast<triton::ast::smtAstLandNode*>(node)); break;
          case LET_NODE:                  return this->print(stream, reinterpret_cast<triton::ast::smtAstLetNode*>(node)); break;
          case LNOT_NODE:                 return this->print(stream, reinterpret_cast<triton::ast::smtAstLnotNode*>(node)); break;
          case LOR_NODE:                  return this->print(stream, reinterpret_cast<triton::ast::smtAstLorNode*>(node)); break;
          case REFERENCE_NODE:            return this->print(stream, reinterpret_cast<triton::ast::smtAstReferenceNode*>(node)); break;
          case STRING_NODE:               return this->print(stream, reinterpret_cast<triton::ast::smtAstStringNode*>(node)); break;
          case SX_NODE:                   return this->print(stream, reinterpret_cast<triton::ast::smtAstSxNode*>(node)); break;
          case VARIABLE_NODE:             return this->print(stream, reinterpret_cast<triton::ast::smtAstVariableNode*>(node)); break;
          case ZX_NODE:                   return this->print(stream, reinterpret_cast<triton::ast::smtAstZxNode*>(node)); break;
          default:
            throw std::invalid_argument("triton::ast::AstSmtRepresentation::print(smtAstAbstractNode) - Invalid kind node");
        }
        return stream;
      }


      /* assert representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstAssertNode* node) {
        stream << "(assert " << node->getChilds()[0] << ")";
        return stream;
      }


      /* bvadd representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvaddNode* node) {
        stream << "(bvadd " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvand representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvandNode* node) {
        stream << "(bvand " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvashr representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvashrNode* node) {
        stream << "(bvashr " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvdecl representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvdeclNode* node) {
        stream << "(_ BitVec " << node->getChilds()[0] << ")";
        return stream;
      }


      /* bvlshr representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvlshrNode* node) {
        stream << "(bvlshr " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvmul representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvmulNode* node) {
        stream << "(bvmul " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvnand representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvnandNode* node) {
        stream << "(bvnand " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvneg representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvnegNode* node) {
        stream << "(bvneg " << node->getChilds()[0] << ")";
        return stream;
      }


      /* bvnor representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvnorNode* node) {
        stream << "(bvnor " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvnot representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvnotNode* node) {
        stream << "(bvnot " << node->getChilds()[0] << ")";
        return stream;
      }


      /* bvor representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvorNode* node) {
        stream << "(bvor " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvrol representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvrolNode* node) {
        stream << "((_ rotate_left " << node->getChilds()[0] << ") " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvror representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvrorNode* node) {
        stream << "((_ rotate_right " << node->getChilds()[0] << ") " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsdiv representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvsdivNode* node) {
        stream << "(bvsdiv " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsge representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvsgeNode* node) {
        stream << "(bvsge " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsgt representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvsgtNode* node) {
        stream << "(bvsgt " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvshl representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvshlNode* node) {
        stream << "(bvshl " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsle representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvsleNode* node) {
        stream << "(bvsle " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvslt representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvsltNode* node) {
        stream << "(bvslt " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsmod representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvsmodNode* node) {
        stream << "(bvsmod " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsrem representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvsremNode* node) {
         stream << "(bvsrem " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsub representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvsubNode* node) {
        stream << "(bvsub " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvudiv representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvudivNode* node) {
        stream << "(bvudiv " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvuge representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvugeNode* node) {
        stream << "(bvuge " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvugt representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvugtNode* node) {
        stream << "(bvugt " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvule representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvuleNode* node) {
        stream << "(bvule " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvult representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvultNode* node) {
        stream << "(bvult " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvurem representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvuremNode* node) {
        stream << "(bvurem " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvxnor representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvxnorNode* node) {
        stream << "(bvxnor " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvxor representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvxorNode* node) {
        stream << "(bvxor " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bv representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstBvNode* node) {
        stream << "(_ bv" << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* compound representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstCompoundNode* node) {
        for (triton::uint32 index = 0; index < node->getChilds().size(); index++)
          stream << node->getChilds()[index];
        return stream;
      }


      /* concat representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstConcatNode* node) {
        std::vector<triton::ast::smtAstAbstractNode*> childs = node->getChilds();
        triton::uint32 size = childs.size();

        if (size < 2)
          throw std::length_error("smtAstConcatNode - exprs must contain at least two expressions");

        stream << "(concat";
        for (triton::uint32 index = 0; index < size; index++)
          stream << " " << childs[index];
        stream << ")";

        return stream;
      }


      /* decimal representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstDecimalNode* node) {
        stream << node->getValue();
        return stream;
      }


      /* declare representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstDeclareFunctionNode* node) {
        stream << "(declare-fun " << node->getChilds()[0] << " () " << node->getChilds()[1] << ")";
        return stream;
      }


      /* distinct representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstDistinctNode* node) {
        stream << "(distinct " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* equal representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstEqualNode* node) {
        stream << "(= " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* extract representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstExtractNode* node) {
        stream << "((_ extract " << node->getChilds()[0] << " " << node->getChilds()[1] << ") " << node->getChilds()[2] << ")";
        return stream;
      }


      /* ite representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstIteNode* node) {
        stream << "(ite " << node->getChilds()[0] << " " << node->getChilds()[1] << " " << node->getChilds()[2] << ")";
        return stream;
      }


      /* land representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstLandNode* node) {
        stream << "(and " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* let representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstLetNode* node) {
        stream << "(let ((" << node->getChilds()[0] << " " << node->getChilds()[1] << ")) " << node->getChilds()[2] << ")";
        return stream;
      }


      /* lnot representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstLnotNode* node) {
        stream << "(not " << node->getChilds()[0] << ")";
        return stream;
      }


      /* lor representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstLorNode* node) {
        stream << "(or " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* reference representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstReferenceNode* node) {
        stream << "#" << node->getValue();
        return stream;
      }


      /* string representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstStringNode* node) {
        stream << node->getValue();
        return stream;
      }


      /* sx representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstSxNode* node) {
        stream << "((_ sign_extend " << node->getChilds()[0] << ") " << node->getChilds()[1] << ")";
        return stream;
      }


      /* variable representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstVariableNode* node) {
        stream << node->getValue();
        return stream;
      }


      /* zx representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::ast::smtAstZxNode* node) {
        stream << "((_ zero_extend " << node->getChilds()[0] << ") " << node->getChilds()[1] << ")";
        return stream;
      }

    };
  };
};

