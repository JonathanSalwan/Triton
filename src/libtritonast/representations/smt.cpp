//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <tritonast/nodes.hpp>
#include <tritonast/exceptions.hpp>
#include <tritonast/representations/smt.hpp>



namespace triton {
  namespace ast {
    namespace representations {

      Smt::Smt() {
      }


      /* Representation dispatcher from an abstract node */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::AbstractNode* node) {
        switch (node->getKind()) {
          case BVADD_NODE:                return this->print(stream, reinterpret_cast<triton::ast::BvaddNode*>(node)); break;
          case BVAND_NODE:                return this->print(stream, reinterpret_cast<triton::ast::BvandNode*>(node)); break;
          case BVASHR_NODE:               return this->print(stream, reinterpret_cast<triton::ast::BvashrNode*>(node)); break;
          case BVLSHR_NODE:               return this->print(stream, reinterpret_cast<triton::ast::BvlshrNode*>(node)); break;
          case BVMUL_NODE:                return this->print(stream, reinterpret_cast<triton::ast::BvmulNode*>(node)); break;
          case BVNAND_NODE:               return this->print(stream, reinterpret_cast<triton::ast::BvnandNode*>(node)); break;
          case BVNEG_NODE:                return this->print(stream, reinterpret_cast<triton::ast::BvnegNode*>(node)); break;
          case BVNOR_NODE:                return this->print(stream, reinterpret_cast<triton::ast::BvnorNode*>(node)); break;
          case BVNOT_NODE:                return this->print(stream, reinterpret_cast<triton::ast::BvnotNode*>(node)); break;
          case BVOR_NODE:                 return this->print(stream, reinterpret_cast<triton::ast::BvorNode*>(node)); break;
          case BVROL_NODE:                return this->print(stream, reinterpret_cast<triton::ast::BvrolNode*>(node)); break;
          case BVROR_NODE:                return this->print(stream, reinterpret_cast<triton::ast::BvrorNode*>(node)); break;
          case BVSDIV_NODE:               return this->print(stream, reinterpret_cast<triton::ast::BvsdivNode*>(node)); break;
          case BVSGE_NODE:                return this->print(stream, reinterpret_cast<triton::ast::BvsgeNode*>(node)); break;
          case BVSGT_NODE:                return this->print(stream, reinterpret_cast<triton::ast::BvsgtNode*>(node)); break;
          case BVSHL_NODE:                return this->print(stream, reinterpret_cast<triton::ast::BvshlNode*>(node)); break;
          case BVSLE_NODE:                return this->print(stream, reinterpret_cast<triton::ast::BvsleNode*>(node)); break;
          case BVSLT_NODE:                return this->print(stream, reinterpret_cast<triton::ast::BvsltNode*>(node)); break;
          case BVSMOD_NODE:               return this->print(stream, reinterpret_cast<triton::ast::BvsmodNode*>(node)); break;
          case BVSREM_NODE:               return this->print(stream, reinterpret_cast<triton::ast::BvsremNode*>(node)); break;
          case BVSUB_NODE:                return this->print(stream, reinterpret_cast<triton::ast::BvsubNode*>(node)); break;
          case BVUDIV_NODE:               return this->print(stream, reinterpret_cast<triton::ast::BvudivNode*>(node)); break;
          case BVUGE_NODE:                return this->print(stream, reinterpret_cast<triton::ast::BvugeNode*>(node)); break;
          case BVUGT_NODE:                return this->print(stream, reinterpret_cast<triton::ast::BvugtNode*>(node)); break;
          case BVULE_NODE:                return this->print(stream, reinterpret_cast<triton::ast::BvuleNode*>(node)); break;
          case BVULT_NODE:                return this->print(stream, reinterpret_cast<triton::ast::BvultNode*>(node)); break;
          case BVUREM_NODE:               return this->print(stream, reinterpret_cast<triton::ast::BvuremNode*>(node)); break;
          case BVXNOR_NODE:               return this->print(stream, reinterpret_cast<triton::ast::BvxnorNode*>(node)); break;
          case BVXOR_NODE:                return this->print(stream, reinterpret_cast<triton::ast::BvxorNode*>(node)); break;
          case BV_NODE:                   return this->print(stream, reinterpret_cast<triton::ast::BvNode*>(node)); break;
          case CONCAT_NODE:               return this->print(stream, reinterpret_cast<triton::ast::ConcatNode*>(node)); break;
          case DECIMAL_NODE:              return this->print(stream, reinterpret_cast<triton::ast::DecimalNode*>(node)); break;
          case DISTINCT_NODE:             return this->print(stream, reinterpret_cast<triton::ast::DistinctNode*>(node)); break;
          case EQUAL_NODE:                return this->print(stream, reinterpret_cast<triton::ast::EqualNode*>(node)); break;
          case EXTRACT_NODE:              return this->print(stream, reinterpret_cast<triton::ast::ExtractNode*>(node)); break;
          case ITE_NODE:                  return this->print(stream, reinterpret_cast<triton::ast::IteNode*>(node)); break;
          case LAND_NODE:                 return this->print(stream, reinterpret_cast<triton::ast::LandNode*>(node)); break;
          case LET_NODE:                  return this->print(stream, reinterpret_cast<triton::ast::LetNode*>(node)); break;
          case LNOT_NODE:                 return this->print(stream, reinterpret_cast<triton::ast::LnotNode*>(node)); break;
          case LOR_NODE:                  return this->print(stream, reinterpret_cast<triton::ast::LorNode*>(node)); break;
          case REFERENCE_NODE:            return this->print(stream, reinterpret_cast<triton::ast::ReferenceNode*>(node)); break;
          case STRING_NODE:               return this->print(stream, reinterpret_cast<triton::ast::StringNode*>(node)); break;
          case SX_NODE:                   return this->print(stream, reinterpret_cast<triton::ast::SxNode*>(node)); break;
          case VARIABLE_NODE:             return this->print(stream, reinterpret_cast<triton::ast::VariableNode*>(node)); break;
          case ZX_NODE:                   return this->print(stream, reinterpret_cast<triton::ast::ZxNode*>(node)); break;
          default:
            throw triton::ast::exceptions::Representation("Smt::print(AbstractNode): Invalid kind node.");
        }
        return stream;
      }


      /* bvadd representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvaddNode* node) {
        stream << "(bvadd " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvand representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvandNode* node) {
        stream << "(bvand " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvashr representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvashrNode* node) {
        stream << "(bvashr " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvlshr representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvlshrNode* node) {
        stream << "(bvlshr " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvmul representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvmulNode* node) {
        stream << "(bvmul " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvnand representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvnandNode* node) {
        stream << "(bvnand " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvneg representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvnegNode* node) {
        stream << "(bvneg " << node->getChildren()[0].get() << ")";
        return stream;
      }


      /* bvnor representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvnorNode* node) {
        stream << "(bvnor " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvnot representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvnotNode* node) {
        stream << "(bvnot " << node->getChildren()[0].get() << ")";
        return stream;
      }


      /* bvor representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvorNode* node) {
        stream << "(bvor " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvrol representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvrolNode* node) {
        stream << "((_ rotate_left " << node->getChildren()[0].get() << ") " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvror representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvrorNode* node) {
        stream << "((_ rotate_right " << node->getChildren()[0].get() << ") " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvsdiv representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvsdivNode* node) {
        stream << "(bvsdiv " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvsge representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvsgeNode* node) {
        stream << "(bvsge " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvsgt representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvsgtNode* node) {
        stream << "(bvsgt " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvshl representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvshlNode* node) {
        stream << "(bvshl " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvsle representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvsleNode* node) {
        stream << "(bvsle " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvslt representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvsltNode* node) {
        stream << "(bvslt " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvsmod representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvsmodNode* node) {
        stream << "(bvsmod " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvsrem representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvsremNode* node) {
         stream << "(bvsrem " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvsub representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvsubNode* node) {
        stream << "(bvsub " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvudiv representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvudivNode* node) {
        stream << "(bvudiv " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvuge representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvugeNode* node) {
        stream << "(bvuge " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvugt representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvugtNode* node) {
        stream << "(bvugt " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvule representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvuleNode* node) {
        stream << "(bvule " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvult representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvultNode* node) {
        stream << "(bvult " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvurem representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvuremNode* node) {
        stream << "(bvurem " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvxnor representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvxnorNode* node) {
        stream << "(bvxnor " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bvxor representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvxorNode* node) {
        stream << "(bvxor " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* bv representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::BvNode* node) {
        stream << "(_ bv" << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* concat representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::ConcatNode* node) {
        std::vector<triton::ast::SharedAbstractNode> children = node->getChildren();
        size_t size = children.size();

        if (size < 2)
          throw triton::ast::exceptions::Representation("Smt::print(ConcatNode): Exprs must contain at least two expressions.");

        stream << "(concat";
        for (size_t index = 0; index < size; index++)
          stream << " " << children[index].get();
        stream << ")";

        return stream;
      }


      /* decimal representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::DecimalNode* node) {
        stream << node->getValue();
        return stream;
      }


      /* distinct representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::DistinctNode* node) {
        stream << "(distinct " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* equal representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::EqualNode* node) {
        stream << "(= " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* extract representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::ExtractNode* node) {
        stream << "((_ extract " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ") " << node->getChildren()[2].get() << ")";
        return stream;
      }


      /* ite representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::IteNode* node) {
        stream << "(ite " << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << " " << node->getChildren()[2].get() << ")";
        return stream;
      }


      /* land representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::LandNode* node) {
        size_t size = node->getChildren().size();

        stream << "(and";
        for (size_t index = 0; index < size; index++)
          stream << " " << node->getChildren()[index];
        stream << ")";

        return stream;
      }


      /* let representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::LetNode* node) {
        stream << "(let ((" << node->getChildren()[0].get() << " " << node->getChildren()[1].get() << ")) " << node->getChildren()[2].get() << ")";
        return stream;
      }


      /* lnot representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::LnotNode* node) {
        stream << "(not " << node->getChildren()[0].get() << ")";
        return stream;
      }


      /* lor representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::LorNode* node) {
        size_t size = node->getChildren().size();

        stream << "(or";
        for (size_t index = 0; index < size; index++)
          stream << " " << node->getChildren()[index];
        stream << ")";

        return stream;
      }


      /* reference representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::ReferenceNode* node) {
        stream << "ref!" << node->getId();
        return stream;
      }


      /* string representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::StringNode* node) {
        stream << node->getValue();
        return stream;
      }


      /* sx representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::SxNode* node) {
        stream << "((_ sign_extend " << node->getChildren()[0].get() << ") " << node->getChildren()[1].get() << ")";
        return stream;
      }


      /* variable representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::VariableNode* node) {
        stream << node->getVarName();
        return stream;
      }


      /* zx representation */
      std::ostream& Smt::print(std::ostream& stream, triton::ast::ZxNode* node) {
        stream << "((_ zero_extend " << node->getChildren()[0].get() << ") " << node->getChildren()[1].get() << ")";
        return stream;
      }

    };
  };
};

