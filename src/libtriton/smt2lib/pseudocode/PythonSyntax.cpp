//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>

#include <api.hpp>
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
        stream << "assert(" << node->getChilds()[0] << ")";
        return stream;
      }


      /* bvadd syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvaddNode* node) {
        triton::uint512 mask = -1;
        mask = mask >> (512 - node->getBitvectorSize());
        stream << "((" << node->getChilds()[0] << " + " << node->getChilds()[1] << ") & 0x" << std::hex << mask << std::dec << ")";
        return stream;
      }


      /* bvand syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvandNode* node) {
        stream << "(" << node->getChilds()[0] << " & " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvashr syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvashrNode* node) {
        stream << "(" << node->getChilds()[0] << " >> " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvdecl syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvdeclNode* node) {
        stream << "bvdecl(" << node->getChilds()[0] << ")";
        return stream;
      }


      /* bvlshr syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvlshrNode* node) {
        stream << "(" << node->getChilds()[0] << " >> " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvmul syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvmulNode* node) {
        triton::uint512 mask = -1;
        mask = mask >> (512 - node->getBitvectorSize());
        stream << "((" << node->getChilds()[0] << " * " << node->getChilds()[1] << ") & 0x" << std::hex << mask << std::dec << ")";
        return stream;
      }


      /* bvnand syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvnandNode* node) {
        stream << "~(" << node->getChilds()[0] << " & " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvneg syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvnegNode* node) {
        stream << "-" << node->getChilds()[0];
        return stream;
      }


      /* bvnor syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvnorNode* node) {
        stream << "~(" << node->getChilds()[0] << " | " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvnot syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvnotNode* node) {
        stream << "~" << node->getChilds()[0];
        return stream;
      }


      /* bvor syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvorNode* node) {
        stream << "(" << node->getChilds()[0] << " | " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvrol syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvrolNode* node) {
        stream << "rol(" << node->getChilds()[0] << ", " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvror syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvrorNode* node) {
        stream << "ror(" << node->getChilds()[0] << ", " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsdiv syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvsdivNode* node) {
        stream << "(" << node->getChilds()[0] << " / " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsge syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvsgeNode* node) {
        stream << "(" << node->getChilds()[0] << " >= " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsgt syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvsgtNode* node) {
        stream << "(" << node->getChilds()[0] << " > " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvshl syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvshlNode* node) {
        triton::uint512 mask = -1;
        mask = mask >> (512 - node->getBitvectorSize());
        stream << "((" << node->getChilds()[0] << " << " << node->getChilds()[1] << ") & 0x" << std::hex << mask << std::dec << ")";
        return stream;
      }


      /* bvsle syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvsleNode* node) {
        stream << "(" << node->getChilds()[0] << " <= " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvslt syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvsltNode* node) {
        stream << "(" << node->getChilds()[0] << " < " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsmod syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvsmodNode* node) {
        stream << "(" << node->getChilds()[0] << " % " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsrem syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvsremNode* node) {
        stream << "(" << node->getChilds()[0] << " % " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvsub syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvsubNode* node) {
        triton::uint512 mask = -1;
        mask = mask >> (512 - node->getBitvectorSize());
        stream << "((" << node->getChilds()[0] << " - " << node->getChilds()[1] << ") & 0x" << std::hex << mask << std::dec << ")";
        return stream;
      }


      /* bvudiv syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvudivNode* node) {
        stream << "(" << node->getChilds()[0] << " / " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvuge syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvugeNode* node) {
        stream << "(" << node->getChilds()[0] << " >= " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvugt syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvugtNode* node) {
        stream << "(" << node->getChilds()[0] << " > " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvule syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvuleNode* node) {
        stream << "(" << node->getChilds()[0] << " <= " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvult syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvultNode* node) {
        stream << "(" << node->getChilds()[0] << " < " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvurem syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvuremNode* node) {
        stream << "(" << node->getChilds()[0] << " % " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvxnor syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvxnorNode* node) {
        stream << "xnor(" << node->getChilds()[0] << ", " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bvxor syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvxorNode* node) {
        stream << "(" << node->getChilds()[0] << " ^ " << node->getChilds()[1] << ")";
        return stream;
      }


      /* bv syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstBvNode* node) {
        stream << node->getChilds()[0];
        return stream;
      }


      /* compound syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstCompoundNode* node) {
        for (triton::uint32 index = 0; index < node->getChilds().size(); index++)
          stream << node->getChilds()[index] << std::endl;
        return stream;
      }


      /* concat syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstConcatNode* node) {
        stream << "(";
        for (triton::uint32 index = node->getChilds().size()-1; index > 0; index--)
          stream << "(" << node->getChilds()[index] << " << " << BYTE_SIZE_BIT * index << ") | ";
        stream << node->getChilds()[0] << ")";
        return stream;
      }


      /* decimal syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstDecimalNode* node) {
        stream << std::hex << "0x" << node->getValue() << std::dec;
        return stream;
      }


      /* declare syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstDeclareFunctionNode* node) {
        stream << node->getChilds()[0];
        return stream;
      }


      /* distinct syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstDistinctNode* node) {
        stream << "(" << node->getChilds()[0] << " != " << node->getChilds()[1] << ")";
        return stream;
      }


      /* equal syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstEqualNode* node) {
        stream << "(" << node->getChilds()[0] << " == " << node->getChilds()[1] << ")";
        return stream;
      }


      /* extract syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstExtractNode* node) {
        triton::uint512 mask = -1;
        triton::uint64  high = reinterpret_cast<triton::smt2lib::smtAstDecimalNode*>(node->getChilds()[0])->getValue().convert_to<triton::uint64>();
        triton::uint64  low  = reinterpret_cast<triton::smt2lib::smtAstDecimalNode*>(node->getChilds()[1])->getValue().convert_to<triton::uint64>();

        mask = mask >> (511 - (high - low));

        if (high - low == triton::api.cpuRegisterBitSize() - 1)
          stream << node->getChilds()[2];
        else if (low == 0)
          stream << "(" << node->getChilds()[2] << " & " << std::hex << "0x" << mask << std::dec << ")";
        else
          stream << "((" << node->getChilds()[2] << " >> " << low << ")" << " & " << std::hex << "0x" << mask << std::dec << ")";

        return stream;
      }


      /* ite syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstIteNode* node) {
        stream << "if " << node->getChilds()[0] << " then " << node->getChilds()[1] << " else " << node->getChilds()[2];
        return stream;
      }


      /* land syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstLandNode* node) {
        stream << "(" << node->getChilds()[0] << " && " << node->getChilds()[1] << ")";
        return stream;
      }


      /* let syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstLetNode* node) {
        stream << node->getChilds()[2];
        return stream;
      }


      /* lnot syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstLnotNode* node) {
        stream << "not " << node->getChilds()[0];
        return stream;
      }


      /* lor syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstLorNode* node) {
        stream << "(" << node->getChilds()[0] << " || " << node->getChilds()[1] << ")";
        return stream;
      }


      /* reference syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstReferenceNode* node) {
        stream << "#" << node->getValue();
        return stream;
      }


      /* string syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstStringNode* node) {
        stream << node->getValue();
        return stream;
      }


      /* sx syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstSxNode* node) {
        triton::uint128 extend = reinterpret_cast<triton::smt2lib::smtAstDecimalNode*>(node->getChilds()[0])->getValue();

        if (extend)
          stream << "sx(" << node->getChilds()[0] << ", " << node->getChilds()[1] << ")";
        else
          stream << node->getChilds()[1];

        return stream;
      }


      /* variable syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstVariableNode* node) {
        stream << node->getValue();
        return stream;
      }


      /* zx syntax */
      std::ostream& PythonSyntax::display(std::ostream& stream, triton::smt2lib::smtAstZxNode* node) {
        stream << node->getChilds()[1];
        return stream;
      }

    };
  };
};


