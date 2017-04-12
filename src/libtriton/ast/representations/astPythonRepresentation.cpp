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


      AstPythonRepresentation::~AstPythonRepresentation() {
      }


      /* Representation dispatcher from an abstract node */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::AbstractNode* node) {
        switch (node->getKind()) {
          case ASSERT_NODE:               return this->print(stream, reinterpret_cast<triton::ast::AssertNode*>(node)); break;
          case BVADD_NODE:                return this->print(stream, reinterpret_cast<triton::ast::BvaddNode*>(node)); break;
          case BVAND_NODE:                return this->print(stream, reinterpret_cast<triton::ast::BvandNode*>(node)); break;
          case BVASHR_NODE:               return this->print(stream, reinterpret_cast<triton::ast::BvashrNode*>(node)); break;
          case BVDECL_NODE:               return this->print(stream, reinterpret_cast<triton::ast::BvdeclNode*>(node)); break;
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
          case COMPOUND_NODE:             return this->print(stream, reinterpret_cast<triton::ast::CompoundNode*>(node)); break;
          case CONCAT_NODE:               return this->print(stream, reinterpret_cast<triton::ast::ConcatNode*>(node)); break;
          case DECIMAL_NODE:              return this->print(stream, reinterpret_cast<triton::ast::DecimalNode*>(node)); break;
          case DECLARE_FUNCTION_NODE:     return this->print(stream, reinterpret_cast<triton::ast::DeclareFunctionNode*>(node)); break;
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


      /* assert representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::AssertNode* node) {
        stream << "assert(" << node->getChilds()[0] << ")";
        return stream;
      }


      /* bvadd representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvaddNode* node) {
        stream << "((" << node->getChilds()[0] << " + " << node->getChilds()[1] << ") & 0x" << std::hex << node->getBitvectorMask() << std::dec << ")";
        return stream;
      }


      /* bvand representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvandNode* node) {
        stream << "(" << node->getChilds()[0] << " & " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvashr representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvashrNode* node) {
        stream << "(" << node->getChilds()[0] << " >> " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvdecl representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvdeclNode* node) {
        stream << "bvdecl(" << node->getChilds()[0] << ")";
        return stream;
      }


      /* bvlshr representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvlshrNode* node) {
        stream << "(" << node->getChilds()[0] << " >> " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvmul representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvmulNode* node) {
        stream << "((" << node->getChilds()[0] << " * " << node->getChilds()[1] << ") & 0x" << std::hex << node->getBitvectorMask() << std::dec << ")";
        return stream;
      }


      /* bvnand representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvnandNode* node) {
        stream << "(~(" << node->getChilds()[0] << " & " << node->getChilds()[1] << ") & 0x" << std::hex << node->getBitvectorMask() << std::dec << ")";
        return stream;
      }


      /* bvneg representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvnegNode* node) {
        stream << "-" << node->getChilds()[0];
        return stream;
      }


      /* bvnor representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvnorNode* node) {
        stream << "(~(" << node->getChilds()[0] << " | " << node->getChilds()[1] << ") & 0x" << std::hex << node->getBitvectorMask() << std::dec << ")";
        return stream;
      }


      /* bvnot representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvnotNode* node) {
        stream << "(~(" << node->getChilds()[0] << ") & 0x" << std::hex << node->getBitvectorMask() << std::dec << ")";
        return stream;
      }


      /* bvor representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvorNode* node) {
        stream << "(" << node->getChilds()[0] << " | " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvrol representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvrolNode* node) {
        stream << "rol(" << node->getChilds()[0] << ", " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvror representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvrorNode* node) {
        stream << "ror(" << node->getChilds()[0] << ", " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsdiv representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvsdivNode* node) {
        stream << "(" << node->getChilds()[0] << " / " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsge representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvsgeNode* node) {
        stream << "(" << node->getChilds()[0] << " >= " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsgt representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvsgtNode* node) {
        stream << "(" << node->getChilds()[0] << " > " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvshl representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvshlNode* node) {
        stream << "((" << node->getChilds()[0] << " << " << node->getChilds()[1] << ") & 0x" << std::hex << node->getBitvectorMask() << std::dec << ")";
        return stream;
      }


      /* bvsle representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvsleNode* node) {
        stream << "(" << node->getChilds()[0] << " <= " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvslt representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvsltNode* node) {
        stream << "(" << node->getChilds()[0] << " < " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsmod representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvsmodNode* node) {
        stream << "(" << node->getChilds()[0] << " % " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsrem representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvsremNode* node) {
        stream << "(" << node->getChilds()[0] << " % " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsub representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvsubNode* node) {
        stream << "((" << node->getChilds()[0] << " - " << node->getChilds()[1] << ") & 0x" << std::hex << node->getBitvectorMask() << std::dec << ")";
        return stream;
      }


      /* bvudiv representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvudivNode* node) {
        stream << "(" << node->getChilds()[0] << " / " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvuge representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvugeNode* node) {
        stream << "(" << node->getChilds()[0] << " >= " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvugt representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvugtNode* node) {
        stream << "(" << node->getChilds()[0] << " > " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvule representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvuleNode* node) {
        stream << "(" << node->getChilds()[0] << " <= " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvult representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvultNode* node) {
        stream << "(" << node->getChilds()[0] << " < " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvurem representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvuremNode* node) {
        stream << "(" << node->getChilds()[0] << " % " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvxnor representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvxnorNode* node) {
        stream << "(~(" << node->getChilds()[0] << " ^ " << node->getChilds()[1] << ") & 0x" << std::hex << node->getBitvectorMask() << std::dec << ")";
        return stream;
      }


      /* bvxor representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvxorNode* node) {
        stream << "(" << node->getChilds()[0] << " ^ " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bv representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::BvNode* node) {
        stream << node->getChilds()[0];
        return stream;
      }


      /* compound representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::CompoundNode* node) {
        for (triton::usize index = 0; index < node->getChilds().size(); index++)
          stream << node->getChilds()[index] << std::endl;
        return stream;
      }


      /* concat representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::ConcatNode* node) {
        triton::usize size = node->getChilds().size();

        for (triton::usize index = 0; index < size; index++)
          stream << "(";

        for (triton::usize index = 0; index < size-1; index++)
          stream << node->getChilds()[index] << ") << " << node->getChilds()[index+1]->getBitvectorSize() << " | ";

        stream << node->getChilds()[size-1] << ")";
        return stream;
      }


      /* decimal representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::DecimalNode* node) {
        stream << std::hex << "0x" << node->getValue() << std::dec;
        return stream;
      }


      /* declare representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::DeclareFunctionNode* node) {
        stream << node->getChilds()[0];
        return stream;
      }


      /* distinct representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::DistinctNode* node) {
        stream << "(" << node->getChilds()[0] << " != " << node->getChilds()[1] << ")";
        return stream;
      }


      /* equal representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::EqualNode* node) {
        stream << "(" << node->getChilds()[0] << " == " << node->getChilds()[1] << ")";
        return stream;
      }


      /* extract representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::ExtractNode* node) {
        triton::uint32 low = reinterpret_cast<triton::ast::DecimalNode*>(node->getChilds()[1])->getValue().convert_to<triton::uint32>();

        if (low == 0)
          stream << "(" << node->getChilds()[2] << " & " << std::hex << "0x" << node->getBitvectorMask() << std::dec << ")";
        else
          stream << "((" << node->getChilds()[2] << " >> " << low << ")" << " & " << std::hex << "0x" << node->getBitvectorMask() << std::dec << ")";

        return stream;
      }


      /* ite representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::IteNode* node) {
        stream << "(" << node->getChilds()[1] << " if " << node->getChilds()[0] << " else " << node->getChilds()[2] << ")";
        return stream;
      }


      /* land representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::LandNode* node) {
        stream << "(" << node->getChilds()[0] << " and " << node->getChilds()[1] << ")";
        return stream;
      }


      /* let representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::LetNode* node) {
        stream << node->getChilds()[2];
        return stream;
      }


      /* lnot representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::LnotNode* node) {
        stream << "not " << node->getChilds()[0];
        return stream;
      }


      /* lor representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::LorNode* node) {
        stream << "(" << node->getChilds()[0] << " or " << node->getChilds()[1] << ")";
        return stream;
      }


      /* reference representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::ReferenceNode* node) {
        stream << "ref_" << node->getExpr().getId();
        return stream;
      }


      /* string representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::StringNode* node) {
        stream << node->getValue();
        return stream;
      }


      /* sx representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::SxNode* node) {
        triton::uint512 extend = reinterpret_cast<triton::ast::DecimalNode*>(node->getChilds()[0])->getValue();

        if (extend)
          stream << "sx(" << node->getChilds()[0] << ", " << node->getChilds()[1] << ")";
        else
          stream << node->getChilds()[1];

        return stream;
      }


      /* variable representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::VariableNode* node) {
        stream << node->getVar().getName();
        return stream;
      }


      /* zx representation */
      std::ostream& AstPythonRepresentation::print(std::ostream& stream, triton::ast::ZxNode* node) {
        stream << node->getChilds()[1];
        return stream;
      }

    };
  };
};


