//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/astPythonRepresentation.hpp>
#include <triton/exceptions.hpp>
#include <triton/symbolicExpression.hpp>
#include <triton/symbolicVariable.hpp>



namespace triton {
  namespace ast {
    namespace representations {

      AstPythonRepresentation::AstPythonRepresentation() {
      }


      /* Representation dispatcher from an abstract node */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::AbstractNode* node) {
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
            throw triton::exceptions::AstRepresentation("AstPythonRepresentation::print(AbstractNode): Invalid kind node.");
        }
        return stream;
      }


      /* bvadd representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvaddNode* node) {
        stream << "((" << node->getChildren()[0] << " + " << node->getChildren()[1] << ") & 0x" << std::hex << node->getBitvectorMask() << std::dec << ")";
        return stream;
      }


      /* bvand representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvandNode* node) {
        stream << "(" << node->getChildren()[0] << " & " << node->getChildren()[1] << ")";
        return stream;
      }


      /* bvashr representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvashrNode* node) {
        stream << "(" << node->getChildren()[0] << " >> " << node->getChildren()[1] << ")";
        return stream;
      }


      /* bvlshr representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvlshrNode* node) {
        stream << "(" << node->getChildren()[0] << " >> " << node->getChildren()[1] << ")";
        return stream;
      }


      /* bvmul representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvmulNode* node) {
        stream << "((" << node->getChildren()[0] << " * " << node->getChildren()[1] << ") & 0x" << std::hex << node->getBitvectorMask() << std::dec << ")";
        return stream;
      }


      /* bvnand representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvnandNode* node) {
        stream << "(~(" << node->getChildren()[0] << " & " << node->getChildren()[1] << ") & 0x" << std::hex << node->getBitvectorMask() << std::dec << ")";
        return stream;
      }


      /* bvneg representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvnegNode* node) {
        stream << "-" << node->getChildren()[0];
        return stream;
      }


      /* bvnor representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvnorNode* node) {
        stream << "(~(" << node->getChildren()[0] << " | " << node->getChildren()[1] << ") & 0x" << std::hex << node->getBitvectorMask() << std::dec << ")";
        return stream;
      }


      /* bvnot representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvnotNode* node) {
        stream << "(~(" << node->getChildren()[0] << ") & 0x" << std::hex << node->getBitvectorMask() << std::dec << ")";
        return stream;
      }


      /* bvor representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvorNode* node) {
        stream << "(" << node->getChildren()[0] << " | " << node->getChildren()[1] << ")";
        return stream;
      }


      /* bvrol representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvrolNode* node) {
        stream << "rol(" << node->getChildren()[0] << ", " << node->getChildren()[1] << ")";
        return stream;
      }


      /* bvror representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvrorNode* node) {
        stream << "ror(" << node->getChildren()[0] << ", " << node->getChildren()[1] << ")";
        return stream;
      }


      /* bvsdiv representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvsdivNode* node) {
        stream << "(" << node->getChildren()[0] << " / " << node->getChildren()[1] << ")";
        return stream;
      }


      /* bvsge representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvsgeNode* node) {
        stream << "(" << node->getChildren()[0] << " >= " << node->getChildren()[1] << ")";
        return stream;
      }


      /* bvsgt representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvsgtNode* node) {
        stream << "(" << node->getChildren()[0] << " > " << node->getChildren()[1] << ")";
        return stream;
      }


      /* bvshl representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvshlNode* node) {
        stream << "((" << node->getChildren()[0] << " << " << node->getChildren()[1] << ") & 0x" << std::hex << node->getBitvectorMask() << std::dec << ")";
        return stream;
      }


      /* bvsle representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvsleNode* node) {
        stream << "(" << node->getChildren()[0] << " <= " << node->getChildren()[1] << ")";
        return stream;
      }


      /* bvslt representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvsltNode* node) {
        stream << "(" << node->getChildren()[0] << " < " << node->getChildren()[1] << ")";
        return stream;
      }


      /* bvsmod representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvsmodNode* node) {
        stream << "(" << node->getChildren()[0] << " % " << node->getChildren()[1] << ")";
        return stream;
      }


      /* bvsrem representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvsremNode* node) {
        stream << "(" << node->getChildren()[0] << " % " << node->getChildren()[1] << ")";
        return stream;
      }


      /* bvsub representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvsubNode* node) {
        stream << "((" << node->getChildren()[0] << " - " << node->getChildren()[1] << ") & 0x" << std::hex << node->getBitvectorMask() << std::dec << ")";
        return stream;
      }


      /* bvudiv representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvudivNode* node) {
        stream << "(" << node->getChildren()[0] << " / " << node->getChildren()[1] << ")";
        return stream;
      }


      /* bvuge representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvugeNode* node) {
        stream << "(" << node->getChildren()[0] << " >= " << node->getChildren()[1] << ")";
        return stream;
      }


      /* bvugt representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvugtNode* node) {
        stream << "(" << node->getChildren()[0] << " > " << node->getChildren()[1] << ")";
        return stream;
      }


      /* bvule representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvuleNode* node) {
        stream << "(" << node->getChildren()[0] << " <= " << node->getChildren()[1] << ")";
        return stream;
      }


      /* bvult representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvultNode* node) {
        stream << "(" << node->getChildren()[0] << " < " << node->getChildren()[1] << ")";
        return stream;
      }


      /* bvurem representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvuremNode* node) {
        stream << "(" << node->getChildren()[0] << " % " << node->getChildren()[1] << ")";
        return stream;
      }


      /* bvxnor representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvxnorNode* node) {
        stream << "(~(" << node->getChildren()[0] << " ^ " << node->getChildren()[1] << ") & 0x" << std::hex << node->getBitvectorMask() << std::dec << ")";
        return stream;
      }


      /* bvxor representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvxorNode* node) {
        stream << "(" << node->getChildren()[0] << " ^ " << node->getChildren()[1] << ")";
        return stream;
      }


      /* bv representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvNode* node) {
        stream << node->getChildren()[0];
        return stream;
      }


      /* concat representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::ConcatNode* node) {
        triton::usize size = node->getChildren().size();

        for (triton::usize index = 0; index < size; index++)
          stream << "(";

        for (triton::usize index = 0; index < size-1; index++)
          stream << node->getChildren()[index] << ") << " << node->getChildren()[index+1]->getBitvectorSize() << " | ";

        stream << node->getChildren()[size-1] << ")";
        return stream;
      }


      /* decimal representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::DecimalNode* node) {
        stream << std::hex << "0x" << node->getValue() << std::dec;
        return stream;
      }


      /* distinct representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::DistinctNode* node) {
        stream << "(" << node->getChildren()[0] << " != " << node->getChildren()[1] << ")";
        return stream;
      }


      /* equal representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::EqualNode* node) {
        stream << "(" << node->getChildren()[0] << " == " << node->getChildren()[1] << ")";
        return stream;
      }


      /* extract representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::ExtractNode* node) {
        triton::uint32 low = reinterpret_cast<triton::ast::DecimalNode*>(node->getChildren()[1])->getValue().convert_to<triton::uint32>();

        if (low == 0)
          stream << "(" << node->getChildren()[2] << " & " << std::hex << "0x" << node->getBitvectorMask() << std::dec << ")";
        else
          stream << "((" << node->getChildren()[2] << " >> " << low << ")" << " & " << std::hex << "0x" << node->getBitvectorMask() << std::dec << ")";

        return stream;
      }


      /* ite representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::IteNode* node) {
        stream << "(" << node->getChildren()[1] << " if " << node->getChildren()[0] << " else " << node->getChildren()[2] << ")";
        return stream;
      }


      /* land representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::LandNode* node) {
        triton::usize size = node->getChildren().size();

        stream << "(" << node->getChildren()[0];
        for (triton::usize index = 1; index < size; index++)
          stream << " and " << node->getChildren()[index];
        stream << ")";

        return stream;
      }


      /* let representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::LetNode* node) {
        stream << node->getChildren()[2];
        return stream;
      }


      /* lnot representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::LnotNode* node) {
        stream << "not " << node->getChildren()[0];
        return stream;
      }


      /* lor representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::LorNode* node) {
        triton::usize size = node->getChildren().size();

        stream << "(" << node->getChildren()[0];
        for (triton::usize index = 1; index < size; index++)
          stream << " or " << node->getChildren()[index];
        stream << ")";

        return stream;
      }


      /* reference representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::ReferenceNode* node) {
        stream << "ref_" << node->getSymbolicExpression().getId();
        return stream;
      }


      /* string representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::StringNode* node) {
        stream << node->getValue();
        return stream;
      }


      /* sx representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::SxNode* node) {
        triton::uint512 extend = reinterpret_cast<triton::ast::DecimalNode*>(node->getChildren()[0])->getValue();

        if (extend)
          stream << "sx(" << node->getChildren()[0] << ", " << node->getChildren()[1] << ")";
        else
          stream << node->getChildren()[1];

        return stream;
      }


      /* variable representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::VariableNode* node) {
        stream << node->getVar().getName();
        return stream;
      }


      /* zx representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::ZxNode* node) {
        stream << node->getChildren()[1];
        return stream;
      }

    };
  };
};


