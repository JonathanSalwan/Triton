//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <vector>

#include <triton/cpuSize.hpp>
#include <triton/exceptions.hpp>
#include <triton/symbolicExpression.hpp>
#include <triton/symbolicVariable.hpp>
#include <triton/tritonToBitwuzla.hpp>



namespace triton {
  namespace ast {

    TritonToBitwuzla::TritonToBitwuzla(bool eval)
      : isEval(eval) {
    }


    TritonToBitwuzla::~TritonToBitwuzla() {
      this->translatedNodes.clear();
      this->variables.clear();
      this->symbols.clear();
    }


    const std::unordered_map<const BitwuzlaTerm*, triton::engines::symbolic::SharedSymbolicVariable>& TritonToBitwuzla::getVariables(void) const {
      return this->variables;
    }


    const std::map<size_t, const BitwuzlaSort*>& TritonToBitwuzla::getBitvectorSorts(void) const {
      return this->bvSorts;
    }


    const BitwuzlaTerm* TritonToBitwuzla::convert(const SharedAbstractNode& node, Bitwuzla* bzla) {
      auto nodes = childrenExtraction(node, true /* unroll*/, true /* revert */);
      for (auto&& n : nodes) {
        translatedNodes[n] = translate(n, bzla);
      }
      return translatedNodes.at(node);
    }


    const BitwuzlaTerm* TritonToBitwuzla::translate(const SharedAbstractNode& node, Bitwuzla* bzla) {
      if (node == nullptr)
        throw triton::exceptions::AstLifting("TritonToBitwuzla::translate(): node cannot be null.");

      std::vector<const BitwuzlaTerm*> children;
      for (auto&& n : node->getChildren()) {
        children.emplace_back(translatedNodes.at(n));
      }

      switch (node->getType()) {
        case BVADD_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_ADD, children[0], children[1]);

        case BVAND_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_AND, children[0], children[1]);

        case BVASHR_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_ASHR, children[0], children[1]);

        case BVLSHR_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_SHR, children[0], children[1]);

        case BVMUL_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_MUL, children[0], children[1]);

        case BVNAND_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_NAND, children[0], children[1]);

        case BVNEG_NODE:
          return bitwuzla_mk_term1(bzla, BITWUZLA_KIND_BV_NEG, children[0]);

        case BVNOR_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_NOR, children[0], children[1]);

        case BVNOT_NODE:
          return bitwuzla_mk_term1(bzla, BITWUZLA_KIND_BV_NOT, children[0]);

        case BVOR_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_OR, children[0], children[1]);

        case BVROL_NODE: {
          auto childNodes = node->getChildren();
          auto idx = reinterpret_cast<IntegerNode*>(childNodes[1].get())->getInteger().convert_to<size_t>();
          return bitwuzla_mk_term1_indexed1(bzla, BITWUZLA_KIND_BV_ROLI, children[0], idx);
        }

        case BVROR_NODE: {
          auto childNodes = node->getChildren();
          auto idx = reinterpret_cast<IntegerNode*>(childNodes[1].get())->getInteger().convert_to<size_t>();
          return bitwuzla_mk_term1_indexed1(bzla, BITWUZLA_KIND_BV_RORI, children[0], idx);
        }

        case BVSDIV_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_SDIV, children[0], children[1]);

        case BVSGE_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_SGE, children[0], children[1]);

        case BVSGT_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_SGT, children[0], children[1]);

        case BVSHL_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_SHL, children[0], children[1]);

        case BVSLE_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_SLE, children[0], children[1]);

        case BVSLT_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_SLT, children[0], children[1]);

        case BVSMOD_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_SMOD, children[0], children[1]);

        case BVSREM_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_SREM, children[0], children[1]);

        case BVSUB_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_SUB, children[0], children[1]);

        case BVUDIV_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_UDIV, children[0], children[1]);

        case BVUGE_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_UGE, children[0], children[1]);

        case BVUGT_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_UGT, children[0], children[1]);

        case BVULE_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_ULE, children[0], children[1]);

        case BVULT_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_ULT, children[0], children[1]);

        case BVUREM_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_UREM, children[0], children[1]);

        case BVXNOR_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_XNOR, children[0], children[1]);

        case BVXOR_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_XOR, children[0], children[1]);

        case BV_NODE: {
          auto childNodes = node->getChildren();
          auto bv_size = reinterpret_cast<IntegerNode*>(childNodes[1].get())->getInteger().convert_to<size_t>();
          auto sort = bvSorts.find(bv_size);
          if (sort == bvSorts.end()) {
            sort = bvSorts.insert({bv_size, bitwuzla_mk_bv_sort(bzla, bv_size)}).first;
          }

          // Handle bitvector value as integer if it small enough.
          if (bv_size <= sizeof(uint64_t) * 8) {
            auto bv_value = reinterpret_cast<IntegerNode*>(childNodes[0].get())->getInteger().convert_to<uint64_t>();
            return bitwuzla_mk_bv_value_uint64(bzla, sort->second, bv_value);
          }
          auto bv_value = reinterpret_cast<IntegerNode*>(childNodes[0].get())->getInteger().convert_to<std::string>();
          return bitwuzla_mk_bv_value(bzla, sort->second, bv_value.c_str(), BITWUZLA_BV_BASE_DEC);
        }

        case CONCAT_NODE:
          return bitwuzla_mk_term(bzla, BITWUZLA_KIND_BV_CONCAT, children.size(), children.data());

        case DISTINCT_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_DISTINCT, children[0], children[1]);

        case EQUAL_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_EQUAL, children[0], children[1]);

        case EXTRACT_NODE: {
          auto childNodes = node->getChildren();
          auto high = reinterpret_cast<IntegerNode*>(childNodes[0].get())->getInteger().convert_to<size_t>();
          auto low = reinterpret_cast<IntegerNode*>(childNodes[1].get())->getInteger().convert_to<size_t>();
          return bitwuzla_mk_term1_indexed2(bzla, BITWUZLA_KIND_BV_EXTRACT, children[2], high, low);
        }

        case FORALL_NODE:
          throw triton::exceptions::AstLifting("TritonToBitwuzla::translate(): FORALL node can't be converted due to a Bitwuzla issue (see #1062).");

        case IFF_NODE:
          return bitwuzla_mk_term2(bzla, BITWUZLA_KIND_IFF, children[0], children[1]);

        case INTEGER_NODE:
          return nullptr;

        case ITE_NODE:
          return bitwuzla_mk_term3(bzla, BITWUZLA_KIND_ITE, children[0], children[1], children[2]);

        case LAND_NODE:
          return bitwuzla_mk_term(bzla, BITWUZLA_KIND_AND, children.size(), children.data());

        case LET_NODE: {
          auto childNodes = node->getChildren();
          symbols[reinterpret_cast<triton::ast::StringNode*>(childNodes[0].get())->getString()] = childNodes[1];
          return children[2];
        }

        case LNOT_NODE:
          return bitwuzla_mk_term1(bzla, BITWUZLA_KIND_NOT, children[0]);

        case LOR_NODE:
          return bitwuzla_mk_term(bzla, BITWUZLA_KIND_OR, children.size(), children.data());

        case LXOR_NODE:
          return bitwuzla_mk_term(bzla, BITWUZLA_KIND_XOR, children.size(), children.data());

        case REFERENCE_NODE: {
          auto ref = reinterpret_cast<ReferenceNode*>(node.get())->getSymbolicExpression()->getAst();
          return translatedNodes.at(ref);
        }

        case STRING_NODE: {
          std::string value = reinterpret_cast<triton::ast::StringNode*>(node.get())->getString();

          auto it = symbols.find(value);
          if (it == symbols.end())
            throw triton::exceptions::AstLifting("TritonToBitwuzla::translate(): [STRING_NODE] Symbols not found.");

          return translatedNodes.at(it->second);
        }

        case SX_NODE: {
          auto childNodes = node->getChildren();
          auto ext = reinterpret_cast<IntegerNode*>(childNodes[0].get())->getInteger().convert_to<size_t>();
          return bitwuzla_mk_term1_indexed1(bzla, BITWUZLA_KIND_BV_SIGN_EXTEND, children[1], ext);
        }

        case VARIABLE_NODE: {
          const auto& symVar = reinterpret_cast<VariableNode*>(node.get())->getSymbolicVariable();
          auto size = symVar->getSize();
          auto sort = bvSorts.find(size);
          if (sort == bvSorts.end()) {
            sort = bvSorts.insert({size, bitwuzla_mk_bv_sort(bzla, size)}).first;
          }

          // If the conversion is used to evaluate a node, we concretize symbolic variables.
          if (this->isEval) {
            triton::uint512 value = reinterpret_cast<triton::ast::VariableNode*>(node.get())->evaluate();
            if (size <= sizeof(uint64_t) * 8) {
              return bitwuzla_mk_bv_value_uint64(bzla, sort->second, value.convert_to<uint64_t>());
            }
            return bitwuzla_mk_bv_value(bzla, sort->second, value.convert_to<std::string>().c_str(), BITWUZLA_BV_BASE_DEC);
          }

          auto n = bitwuzla_mk_const(bzla, sort->second, symVar->getName().c_str());
          variables[n] = symVar;
          return n;
        }

        case ZX_NODE: {
          auto childNodes = node->getChildren();
          auto ext = reinterpret_cast<IntegerNode*>(childNodes[0].get())->getInteger().convert_to<size_t>();
          return bitwuzla_mk_term1_indexed1(bzla, BITWUZLA_KIND_BV_ZERO_EXTEND,children[1], ext);
        }

        default:
          throw triton::exceptions::AstLifting("TritonToBitwuzla::translate(): Invalid kind of node.");
      }
    }

  }; /* ast namespace */
}; /* triton namespace */
