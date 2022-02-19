//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <algorithm>
#include <vector>

#include <triton/astEnums.hpp>
#include <triton/liftingToDot.hpp>
#include <triton/tritonTypes.hpp>



namespace triton {
  namespace engines {
    namespace lifters {

      LiftingToDot::LiftingToDot(const triton::ast::SharedAstContext& astCtxt, triton::engines::symbolic::SymbolicEngine* symbolic)
        : astCtxt(astCtxt), symbolic(symbolic) {
        this->uniqueid = 0;
      }


      std::ostream& LiftingToDot::liftToDot(std::ostream& stream, const triton::engines::symbolic::SharedSymbolicExpression& expr) {
        /* Slice expressions */
        this->expressions = this->symbolic->sliceExpressions(expr);

        /* Link abstract node to their symbolic expression to collect information later */
        for (const auto& se : this->expressions) {
          this->information[se.second->getAst().get()] = se.second.get();
        }

        return this->liftToDot(stream, expr->getAst());
      }


      void LiftingToDot::spreadInformation(std::ostream& stream) {
        for (const auto& i : this->information) {
          auto* node = i.first;
          auto* se = i.second;

          stream << "subgraph cluster_" << reinterpret_cast<size_t>(node) << " {" << std::endl;
          stream << "  rank=max;" << std::endl;
          stream << "  bgcolor=lightgrey;" << std::endl;
          stream << "  node [style=filled, color=black, fillcolor=white];" << std::endl;
          stream << "  label=\"" << se->getDisassembly() << "\";" << std::endl;
          stream << "  " << reinterpret_cast<size_t>(node) << ";" << std::endl;
          stream << "}" << std::endl;
        }
      }


      void LiftingToDot::defineLegend(std::ostream& stream) {
        /* Do not create legend if there is no extra information */
        if (this->expressions.empty())
          return;

        /* Get all id of symbolic expression */
        std::vector<triton::usize> ssa;
        for (const auto& se : this->expressions) {
          ssa.push_back(se.first);
        }

        /* Sort ssa form */
        std::sort(ssa.begin(), ssa.end());

        stream << "legend [fontname=mono style=filled fillcolor=lightyellow color=black shape=box label=\"Instructions involved in the expression" << std::endl << std::endl;
        for (const auto& id : ssa) {
          const auto& se = this->expressions[id];
          stream << se->getDisassembly() << "\\l";
        }
        stream << std::endl << "\"];" << std::endl;
      }


      std::ostream& LiftingToDot::liftToDot(std::ostream& stream, const triton::ast::SharedAbstractNode& root) {
        auto nodes = triton::ast::childrenExtraction(root, true /* unroll*/, false /* revert */);

        /* Prologue of Dot format */
        stream << "digraph triton {" << std::endl;
        stream << "ordering=\"out\";" << std::endl;
        stream << "fontname=mono;" << std::endl;

        /* Spread information */
        this->defineLegend(stream);
        this->spreadInformation(stream);

        for (auto const& node : nodes) {

          /* Print the current node on Dot format */
          switch (node->getType()) {
            case triton::ast::ASSERT_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"ASSERT\"];" << std::endl;
              break;
            }

            case triton::ast::BSWAP_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BSWAP\"];" << std::endl;
              break;
            }

            case triton::ast::BVADD_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVADD\"];" << std::endl;
              break;
            }

            case triton::ast::BVAND_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVAND\"];" << std::endl;
              break;
            }

            case triton::ast::BVASHR_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVASHR\"];" << std::endl;
              break;
            }

            case triton::ast::BVLSHR_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVLSHR\"];" << std::endl;
              break;
            }

            case triton::ast::BVMUL_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVMUL\"];" << std::endl;
              break;
            }

            case triton::ast::BVNAND_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVNAND\"];" << std::endl;
              break;
            }

            case triton::ast::BVNEG_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVNEG\"];" << std::endl;
              break;
            }

            case triton::ast::BVNOR_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVNOR\"];" << std::endl;
              break;
            }

            case triton::ast::BVNOT_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVNOT\"];" << std::endl;
              break;
            }

            case triton::ast::BVOR_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVOR\"];" << std::endl;
              break;
            }

            case triton::ast::BVROL_NODE: {
              auto RHS = node->getChildren()[1];
              auto rot = reinterpret_cast<triton::ast::IntegerNode*>(RHS.get())->getInteger();

              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVROL\"];" << std::endl;
              stream << reinterpret_cast<size_t>(RHS.get()) << " [label=\"" << rot << "-bit\"];" << std::endl;
              break;
            }

            case triton::ast::BVROR_NODE: {
              auto RHS = node->getChildren()[1];
              auto rot = reinterpret_cast<triton::ast::IntegerNode*>(RHS.get())->getInteger();

              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVROR\"];" << std::endl;
              stream << reinterpret_cast<size_t>(RHS.get()) << " [label=\"" << rot << "-bit\"];" << std::endl;
              break;
            }

            case triton::ast::BVSDIV_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVSDIV\"];" << std::endl;
              break;
            }

            case triton::ast::BVSGE_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVSGE\"];" << std::endl;
              break;
            }

            case triton::ast::BVSGT_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVSGT\"];" << std::endl;
              break;
            }

            case triton::ast::BVSHL_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVSHL\"];" << std::endl;
              break;
            }

            case triton::ast::BVSLE_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVSLE\"];" << std::endl;
              break;
            }

            case triton::ast::BVSLT_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVSLT\"];" << std::endl;
              break;
            }

            case triton::ast::BVSMOD_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVSMOD\"];" << std::endl;
              break;
            }

            case triton::ast::BVSREM_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVSREM\"];" << std::endl;
              break;
            }

            case triton::ast::BVSUB_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVSUB\"];" << std::endl;
              break;
            }

            case triton::ast::BVUDIV_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVUDIV\"];" << std::endl;
              break;
            }

            case triton::ast::BVUGE_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVUGE\"];" << std::endl;
              break;
            }

            case triton::ast::BVUGT_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVUGT\"];" << std::endl;
              break;
            }

            case triton::ast::BVULE_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVULE\"];" << std::endl;
              break;
            }

            case triton::ast::BVULT_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVULT\"];" << std::endl;
              break;
            }

            case triton::ast::BVUREM_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVUREM\"];" << std::endl;
              break;
            }

            case triton::ast::BVXNOR_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVXNOR\"];" << std::endl;
              break;
            }

            case triton::ast::BVXOR_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"BVXOR\"];" << std::endl;
              break;
            }

            case triton::ast::BV_NODE: {
              auto LHS   = node->getChildren()[0];
              auto RHS   = node->getChildren()[1];
              auto value = reinterpret_cast<triton::ast::IntegerNode*>(LHS.get())->getInteger();
              auto size  = reinterpret_cast<triton::ast::IntegerNode*>(RHS.get())->getInteger();

              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"0x" << std::hex << value << std::dec << " : " << size << "-bit\"];" << std::endl;
              break;
            }

            case triton::ast::COMPOUND_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"COMPOUND\"];" << std::endl;
              break;
            }

            case triton::ast::CONCAT_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"CONCAT\"];" << std::endl;
              break;
            }

            case triton::ast::DECLARE_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"DECLARE\"];" << std::endl;
              break;
            }

            case triton::ast::DISTINCT_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"!=\"];" << std::endl;
              break;
            }

            case triton::ast::EQUAL_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"==\"];" << std::endl;
              break;
            }

            case triton::ast::EXTRACT_NODE: {
              auto nhi = node->getChildren()[0];
              auto nlo = node->getChildren()[1];
              auto hi  = reinterpret_cast<triton::ast::IntegerNode*>(nhi.get())->getInteger();
              auto lo  = reinterpret_cast<triton::ast::IntegerNode*>(nlo.get())->getInteger();

              stream << reinterpret_cast<size_t>(nhi.get()) << " [label=\"hi:" << hi << "\"];" << std::endl;
              stream << reinterpret_cast<size_t>(nlo.get()) << " [label=\"lo:" << lo << "\"];" << std::endl;
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"EXTRACT\"];" << std::endl;
              break;
            }

            case triton::ast::FORALL_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"FORALL\"];" << std::endl;
              break;
            }

            case triton::ast::IFF_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"IFF\"];" << std::endl;
              break;
            }

            case triton::ast::ITE_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"ITE\"];" << std::endl;
              break;
            }

            case triton::ast::LAND_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"LAND\"];" << std::endl;
              break;
            }

            case triton::ast::LET_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"LET\"];" << std::endl;
              break;
            }

            case triton::ast::LNOT_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"LNOT\"];" << std::endl;
              break;
            }

            case triton::ast::LOR_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"LOR\"];" << std::endl;
              break;
            }

            case triton::ast::LXOR_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"LXOR\"];" << std::endl;
              break;
            }

            case triton::ast::STRING_NODE: {
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"" << node << "\"];" << std::endl;
              break;
            }

            case triton::ast::SX_NODE: {
              auto LHS = node->getChildren()[0];
              auto sx  = reinterpret_cast<triton::ast::IntegerNode*>(LHS.get())->getInteger();

              stream << reinterpret_cast<size_t>(LHS.get()) << " [label=\"" << sx << "-bit\"];" << std::endl;
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"SX\"];" << std::endl;
              break;
            }

            case triton::ast::ZX_NODE: {
              auto LHS = node->getChildren()[0];
              auto zx  = reinterpret_cast<triton::ast::IntegerNode*>(LHS.get())->getInteger();

              stream << reinterpret_cast<size_t>(LHS.get()) << " [label=\"" << zx << "-bit\"];" << std::endl;
              stream << reinterpret_cast<size_t>(node.get()) << " [label=\"ZX\"];" << std::endl;
              break;
            }

            default:
              break;
          };

          if (node->getType() == triton::ast::BV_NODE) {
            /* Skip bv node because we have a custom repr */
            continue;
          }

          /* Link the current node with its children */
          for (auto const& child : node->getChildren()) {
            /* Handle reference repr */
            if (child->getType() == triton::ast::REFERENCE_NODE) {
              this->handleReference(stream, node, child);
            }
            /* Handle variable repr */
            else if (child->getType() == triton::ast::VARIABLE_NODE) {
              this->handleVariable(stream, node, child);
            }
            /* Link by default */
            else {
              stream << reinterpret_cast<size_t>(node.get()) << "->" << reinterpret_cast<size_t>(child.get()) << ";" << std::endl;
            }
          }
        }

        /* Link the legend to the root node */
        if (this->expressions.empty() == false) {
          stream << "legend->" << reinterpret_cast<size_t>(root.get()) << " [style=dotted]" << std::endl;
        }

        /* Epilogue of Dot format */
        stream << "}" << std::endl;

        return stream;
      }


      void LiftingToDot::handleReference(std::ostream& stream, const triton::ast::SharedAbstractNode& parent, const triton::ast::SharedAbstractNode& child) {
        auto ref = reinterpret_cast<triton::ast::ReferenceNode*>(child.get())->getSymbolicExpression()->getAst();

        if (ref->getType() == triton::ast::VARIABLE_NODE) {
          this->handleVariable(stream, parent, ref);
        }
        else {
          stream << reinterpret_cast<size_t>(parent.get()) << "->" << reinterpret_cast<size_t>(ref.get()) << ";" << std::endl;
        }
      }


      void LiftingToDot::handleVariable(std::ostream& stream, const triton::ast::SharedAbstractNode& parent, const triton::ast::SharedAbstractNode& child) {
        /* Variables are displayed on several nodes for a better visibility */
        this->uniqueid++;

        stream << this->uniqueid << " [label=\"" << child << "\" rank=max style=filled, color=black, fillcolor=lightgreen];" << std::endl;
        stream << reinterpret_cast<size_t>(parent.get()) << "->" << this->uniqueid << ";" << std::endl;
      }

    }; /* lifters namespace */
  }; /* engines namespace */
}; /* triton namespace */
