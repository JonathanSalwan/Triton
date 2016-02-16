//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>
#include <astSmtRepresentation.hpp>



namespace triton {
  namespace smt2lib {
    namespace representation {

      AstSmtRepresentation::AstSmtRepresentation() {
      }


      AstSmtRepresentation::~AstSmtRepresentation() {
      }


      /* Representation dispatcher from an abstract node */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstAbstractNode* node) {
        switch (node->getKind()) {
          case ASSERT_NODE:               return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstAssertNode*>(node)); break;
          case BVADD_NODE:                return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvaddNode*>(node)); break;
          case BVAND_NODE:                return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvandNode*>(node)); break;
          case BVASHR_NODE:               return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvashrNode*>(node)); break;
          case BVDECL_NODE:               return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvdeclNode*>(node)); break;
          case BVLSHR_NODE:               return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvlshrNode*>(node)); break;
          case BVMUL_NODE:                return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvmulNode*>(node)); break;
          case BVNAND_NODE:               return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvnandNode*>(node)); break;
          case BVNEG_NODE:                return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvnegNode*>(node)); break;
          case BVNOR_NODE:                return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvnorNode*>(node)); break;
          case BVNOT_NODE:                return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvnotNode*>(node)); break;
          case BVOR_NODE:                 return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvorNode*>(node)); break;
          case BVROL_NODE:                return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvrolNode*>(node)); break;
          case BVROR_NODE:                return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvrorNode*>(node)); break;
          case BVSDIV_NODE:               return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvsdivNode*>(node)); break;
          case BVSGE_NODE:                return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvsgeNode*>(node)); break;
          case BVSGT_NODE:                return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvsgtNode*>(node)); break;
          case BVSHL_NODE:                return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvshlNode*>(node)); break;
          case BVSLE_NODE:                return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvsleNode*>(node)); break;
          case BVSLT_NODE:                return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvsltNode*>(node)); break;
          case BVSMOD_NODE:               return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvsmodNode*>(node)); break;
          case BVSREM_NODE:               return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvsremNode*>(node)); break;
          case BVSUB_NODE:                return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvsubNode*>(node)); break;
          case BVUDIV_NODE:               return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvudivNode*>(node)); break;
          case BVUGE_NODE:                return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvugeNode*>(node)); break;
          case BVUGT_NODE:                return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvugtNode*>(node)); break;
          case BVULE_NODE:                return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvuleNode*>(node)); break;
          case BVULT_NODE:                return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvultNode*>(node)); break;
          case BVUREM_NODE:               return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvuremNode*>(node)); break;
          case BVXNOR_NODE:               return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvxnorNode*>(node)); break;
          case BVXOR_NODE:                return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvxorNode*>(node)); break;
          case BV_NODE:                   return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstBvNode*>(node)); break;
          case COMPOUND_NODE:             return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstCompoundNode*>(node)); break;
          case CONCAT_NODE:               return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstConcatNode*>(node)); break;
          case DECIMAL_NODE:              return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstDecimalNode*>(node)); break;
          case DECLARE_FUNCTION_NODE:     return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstDeclareFunctionNode*>(node)); break;
          case DISTINCT_NODE:             return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstDistinctNode*>(node)); break;
          case EQUAL_NODE:                return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstEqualNode*>(node)); break;
          case EXTRACT_NODE:              return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstExtractNode*>(node)); break;
          case ITE_NODE:                  return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstIteNode*>(node)); break;
          case LAND_NODE:                 return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstLandNode*>(node)); break;
          case LET_NODE:                  return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstLetNode*>(node)); break;
          case LNOT_NODE:                 return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstLnotNode*>(node)); break;
          case LOR_NODE:                  return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstLorNode*>(node)); break;
          case REFERENCE_NODE:            return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstReferenceNode*>(node)); break;
          case STRING_NODE:               return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstStringNode*>(node)); break;
          case SX_NODE:                   return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstSxNode*>(node)); break;
          case VARIABLE_NODE:             return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstVariableNode*>(node)); break;
          case ZX_NODE:                   return this->print(stream, reinterpret_cast<triton::smt2lib::smtAstZxNode*>(node)); break;
          default:
            throw std::invalid_argument("triton::smt2lib::AstSmtRepresentation::print(smtAstAbstractNode) - Invalid kind node");
        }
        return stream;
      }


      /* assert representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstAssertNode* node) {
        stream << "(assert " << node->getChilds()[0] << ")";
        return stream;
      }


      /* bvadd representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvaddNode* node) {
        stream << "(bvadd " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvand representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvandNode* node) {
        stream << "(bvand " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvashr representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvashrNode* node) {
        stream << "(bvashr " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvdecl representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvdeclNode* node) {
        stream << "(_ BitVec " << node->getChilds()[0] << ")";
        return stream;
      }


      /* bvlshr representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvlshrNode* node) {
        stream << "(bvlshr " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvmul representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvmulNode* node) {
        stream << "(bvmul " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvnand representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvnandNode* node) {
        stream << "(bvnand " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvneg representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvnegNode* node) {
        stream << "(bvneg " << node->getChilds()[0] << ")";
        return stream;
      }


      /* bvnor representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvnorNode* node) {
        stream << "(bvnor " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvnot representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvnotNode* node) {
        stream << "(bvnot " << node->getChilds()[0] << ")";
        return stream;
      }


      /* bvor representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvorNode* node) {
        stream << "(bvor " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvrol representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvrolNode* node) {
        stream << "((_ rotate_left " << node->getChilds()[0] << ") " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvror representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvrorNode* node) {
        stream << "((_ rotate_right " << node->getChilds()[0] << ") " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsdiv representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvsdivNode* node) {
        stream << "(bvsdiv " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsge representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvsgeNode* node) {
        stream << "(bvsge " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsgt representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvsgtNode* node) {
        stream << "(bvsgt " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvshl representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvshlNode* node) {
        stream << "(bvshl " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsle representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvsleNode* node) {
        stream << "(bvsle " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvslt representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvsltNode* node) {
        stream << "(bvslt " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsmod representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvsmodNode* node) {
        stream << "(bvsmod " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsrem representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvsremNode* node) {
         stream << "(bvsrem " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsub representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvsubNode* node) {
        stream << "(bvsub " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvudiv representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvudivNode* node) {
        stream << "(bvudiv " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvuge representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvugeNode* node) {
        stream << "(bvuge " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvugt representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvugtNode* node) {
        stream << "(bvugt " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvule representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvuleNode* node) {
        stream << "(bvule " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvult representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvultNode* node) {
        stream << "(bvult " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvurem representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvuremNode* node) {
        stream << "(bvurem " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvxnor representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvxnorNode* node) {
        stream << "(bvxnor " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvxor representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvxorNode* node) {
        stream << "(bvxor " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bv representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstBvNode* node) {
        stream << "(_ bv" << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* compound representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstCompoundNode* node) {
        for (triton::uint32 index = 0; index < node->getChilds().size(); index++)
          stream << node->getChilds()[index];
        return stream;
      }


      /* concat representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstConcatNode* node) {
        std::vector<triton::smt2lib::smtAstAbstractNode*> childs = node->getChilds();
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
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstDecimalNode* node) {
        stream << node->getValue();
        return stream;
      }


      /* declare representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstDeclareFunctionNode* node) {
        stream << "(declare-fun " << node->getChilds()[0] << " () " << node->getChilds()[1] << ")";
        return stream;
      }


      /* distinct representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstDistinctNode* node) {
        stream << "(distinct " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* equal representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstEqualNode* node) {
        stream << "(= " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* extract representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstExtractNode* node) {
        stream << "((_ extract " << node->getChilds()[0] << " " << node->getChilds()[1] << ") " << node->getChilds()[2] << ")";
        return stream;
      }


      /* ite representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstIteNode* node) {
        stream << "(ite " << node->getChilds()[0] << " " << node->getChilds()[1] << " " << node->getChilds()[2] << ")";
        return stream;
      }


      /* land representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstLandNode* node) {
        stream << "(and " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* let representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstLetNode* node) {
        stream << "(let ((" << node->getChilds()[0] << " " << node->getChilds()[1] << ")) " << node->getChilds()[2] << ")";
        return stream;
      }


      /* lnot representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstLnotNode* node) {
        stream << "(not " << node->getChilds()[0] << ")";
        return stream;
      }


      /* lor representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstLorNode* node) {
        stream << "(or " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
        return stream;
      }


      /* reference representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstReferenceNode* node) {
        stream << "#" << node->getValue();
        return stream;
      }


      /* string representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstStringNode* node) {
        stream << node->getValue();
        return stream;
      }


      /* sx representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstSxNode* node) {
        stream << "((_ sign_extend " << node->getChilds()[0] << ") " << node->getChilds()[1] << ")";
        return stream;
      }


      /* variable representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstVariableNode* node) {
        stream << node->getValue();
        return stream;
      }


      /* zx representation */
      std::ostream& AstSmtRepresentation::print(std::ostream& stream, triton::smt2lib::smtAstZxNode* node) {
        stream << "((_ zero_extend " << node->getChilds()[0] << ") " << node->getChilds()[1] << ")";
        return stream;
      }

    };
  };
};

