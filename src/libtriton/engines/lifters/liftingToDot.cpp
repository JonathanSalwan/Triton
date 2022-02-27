//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <algorithm>
#include <vector>
#include <string>

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


      void LiftingToDot::iterateNodes(const triton::ast::SharedAbstractNode& root) {
        auto ttnodes = triton::ast::childrenExtraction(root, true /* unroll*/, false /* revert */);

        for (auto const& node : ttnodes) {
          switch (node->getType()) {

            case triton::ast::ARRAY_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"MEMORY\"];"});
              break;
            }

            case triton::ast::ASSERT_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"ASSERT\"];"});
              break;
            }

            case triton::ast::BSWAP_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BSWAP\"];"});
              break;
            }

            case triton::ast::BVADD_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVADD\"];"});
              break;
            }

            case triton::ast::BVAND_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVAND\"];"});
              break;
            }

            case triton::ast::BVASHR_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVASHR\"];"});
              break;
            }

            case triton::ast::BVLSHR_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVLSHR\"];"});
              break;
            }

            case triton::ast::BVMUL_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVMUL\"];"});
              break;
            }

            case triton::ast::BVNAND_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVNAND\"];"});
              break;
            }

            case triton::ast::BVNEG_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVNEG\"];"});
              break;
            }

            case triton::ast::BVNOR_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVNOR\"];"});
              break;
            }

            case triton::ast::BVNOT_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVNOT\"];"});
              break;
            }

            case triton::ast::BVOR_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVOR\"];"});
              break;
            }

            case triton::ast::BVROL_NODE: {
              auto RHS = node->getChildren()[1];
              auto rot = triton::ast::getInteger<std::string>(RHS);

              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVROL\"];"});
              this->nodes.insert({reinterpret_cast<size_t>(RHS.get()), "[label=\"" + rot + "-bit\"];"});
              break;
            }

            case triton::ast::BVROR_NODE: {
              auto RHS = node->getChildren()[1];
              auto rot = triton::ast::getInteger<std::string>(RHS);

              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVROR\"];"});
              this->nodes.insert({reinterpret_cast<size_t>(RHS.get()), "[label=\"" + rot + "-bit\"];"});
              break;
            }

            case triton::ast::BVSDIV_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVSDIV\"];"});
              break;
            }

            case triton::ast::BVSGE_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVSGE\"];"});
              break;
            }

            case triton::ast::BVSGT_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVSGT\"];"});
              break;
            }

            case triton::ast::BVSHL_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVSHL\"];"});
              break;
            }

            case triton::ast::BVSLE_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVSLE\"];"});
              break;
            }

            case triton::ast::BVSLT_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVSLT\"];"});
              break;
            }

            case triton::ast::BVSMOD_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVSMOD\"];"});
              break;
            }

            case triton::ast::BVSREM_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVSREM\"];"});
              break;
            }

            case triton::ast::BVSUB_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVSUB\"];"});
              break;
            }

            case triton::ast::BVUDIV_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVUDIV\"];"});
              break;
            }

            case triton::ast::BVUGE_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVUGE\"];"});
              break;
            }

            case triton::ast::BVUGT_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVUGT\"];"});
              break;
            }

            case triton::ast::BVULE_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVULE\"];"});
              break;
            }

            case triton::ast::BVULT_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVULT\"];"});
              break;
            }

            case triton::ast::BVUREM_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVUREM\"];"});
              break;
            }

            case triton::ast::BVXNOR_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVXNOR\"];"});
              break;
            }

            case triton::ast::BVXOR_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"BVXOR\"];"});
              break;
            }

            case triton::ast::BV_NODE: {
              auto LHS   = node->getChildren()[0];
              auto RHS   = node->getChildren()[1];
              auto value = triton::ast::getInteger<triton::uint512>(LHS);
              auto size  = triton::ast::getInteger<triton::uint512>(RHS);

              std::stringstream s;
              s << "[label=\"0x" << std::hex << value << std::dec << " : " << size << "-bit\" style=filled, color=black, fillcolor=lightblue];";

              this->nodes.insert({reinterpret_cast<size_t>(node.get()), s.str()});
              break;
            }

            case triton::ast::COMPOUND_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"COMPOUND\"];"});
              break;
            }

            case triton::ast::CONCAT_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"CONCAT\"];"});
              break;
            }

            case triton::ast::DECLARE_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"DECLARE\"];"});
              break;
            }

            case triton::ast::DISTINCT_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"!=\"];"});
              break;
            }

            case triton::ast::EQUAL_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"==\"];"});
              break;
            }

            case triton::ast::EXTRACT_NODE: {
              auto nhi = node->getChildren()[0];
              auto nlo = node->getChildren()[1];
              auto hi  = triton::ast::getInteger<std::string>(nhi);
              auto lo  = triton::ast::getInteger<std::string>(nlo);

              this->nodes.insert({reinterpret_cast<size_t>(nhi.get()), "[label=\"hi:" + hi + "\"];"});
              this->nodes.insert({reinterpret_cast<size_t>(nlo.get()), "[label=\"lo:" + lo + "\"];"});
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"EXTRACT\"];"});
              break;
            }

            case triton::ast::FORALL_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"FORALL\"];"});
              break;
            }

            case triton::ast::IFF_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"IFF\"];"});
              break;
            }

            case triton::ast::ITE_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"ITE\"];"});
              break;
            }

            case triton::ast::LAND_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"LAND\"];"});
              break;
            }

            case triton::ast::LET_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"LET\"];"});
              break;
            }

            case triton::ast::LNOT_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"LNOT\"];"});
              break;
            }

            case triton::ast::LOR_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"LOR\"];"});
              break;
            }

            case triton::ast::LXOR_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"LXOR\"];"});
              break;
            }

            case triton::ast::SELECT_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"SELECT\"];"});
              break;
            }

            case triton::ast::STORE_NODE: {
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"STORE\"];"});
              break;
            }

            case triton::ast::STRING_NODE: {
              std::stringstream s;
              s << "[label=\"" << node << "\"];";
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), s.str()});
              break;
            }

            case triton::ast::SX_NODE: {
              auto LHS = node->getChildren()[0];
              auto sx  = triton::ast::getInteger<std::string>(LHS);

              this->nodes.insert({reinterpret_cast<size_t>(LHS.get()), "[label=\"" + sx + "-bit\"];"});
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"SX\"];"});
              break;
            }

            case triton::ast::ZX_NODE: {
              auto LHS = node->getChildren()[0];
              auto zx  = triton::ast::getInteger<std::string>(LHS);

              this->nodes.insert({reinterpret_cast<size_t>(LHS.get()), "[label=\"" + zx + "-bit\"];"});
              this->nodes.insert({reinterpret_cast<size_t>(node.get()), "[label=\"ZX\"];"});
              break;
            }

            case triton::ast::REFERENCE_NODE: {
              const triton::ast::AbstractNode* ptr = node.get();
              while (ptr->getType() == triton::ast::REFERENCE_NODE) {
                const triton::ast::ReferenceNode* ref = reinterpret_cast<const triton::ast::ReferenceNode*>(ptr);
                const triton::ast::AbstractNode* next = ref->getSymbolicExpression()->getAst().get();
                triton::usize refId = ref->getSymbolicExpression()->getId();
                this->nodes.insert({reinterpret_cast<size_t>(ref), "[label=\"Ref #" + std::to_string(refId) + "\"];"});
                this->edges.insert({reinterpret_cast<size_t>(ptr), reinterpret_cast<size_t>(next)});
                ptr = next;
              }
              break;
            }

            default:
              break;
          };

          if (node->getType() == triton::ast::BV_NODE) {
            /* Skip bv node because we have a custom repr */
            continue;
          }

          if (node->getType() == triton::ast::ARRAY_NODE) {
            /* Skip array node because we have a custom repr */
            continue;
          }

          /* Link the current node with its children */
          for (auto const& child : node->getChildren()) {
            /* Handle variable repr */
            if (child->getType() == triton::ast::VARIABLE_NODE) {
              this->handleVariable(node, child);
            }
            /* Link by default */
            else {
              this->edges.insert({reinterpret_cast<size_t>(node.get()), reinterpret_cast<size_t>(child.get())});
            }
          }
        }
      }


      void LiftingToDot::handleVariable(const triton::ast::SharedAbstractNode& parent, const triton::ast::SharedAbstractNode& child) {
        /* Variables are displayed on several nodes for a better visibility */
        this->uniqueid++;

        std::stringstream s;
        s << "[label=\"" << child << "\" rank=max style=filled, color=black, fillcolor=lightgreen];";

        this->nodes.insert({this->uniqueid, s.str()});
        this->edges.insert({reinterpret_cast<size_t>(parent.get()), this->uniqueid});
      }


      std::ostream& LiftingToDot::liftToDot(std::ostream& stream, const triton::ast::SharedAbstractNode& root) {
        /* Prologue of Dot format */
        stream << "digraph triton {" << std::endl;
        stream << "ordering=\"out\";" << std::endl;
        stream << "fontname=mono;" << std::endl;

        /* Spread information */
        this->defineLegend(stream);
        this->spreadInformation(stream);

        /* Iterate over nodes */
        this->iterateNodes(root);

        /* Print nodes */
        for (const auto& node : this->nodes) {
          stream << node.first << " " << node.second << std::endl;
        }

        /* Print edges */
        for (const auto& edge : this->edges) {
          stream << edge.first << " -> " << edge.second << std::endl;
        }

        /* Link the legend to the root node */
        if (this->expressions.empty() == false) {
          stream << "legend -> " << reinterpret_cast<size_t>(root.get()) << " [style=dotted];" << std::endl;
        }

        /* Epilogue of Dot format */
        stream << "}" << std::endl;

        return stream;
      }

    }; /* lifters namespace */
  }; /* engines namespace */
}; /* triton namespace */
