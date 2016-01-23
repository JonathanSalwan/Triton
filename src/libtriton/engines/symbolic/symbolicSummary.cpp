//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <api.hpp>
#include <symbolicSummary.hpp>

/*
 *
 * /!\ Still experimental /!\
 *
 */



namespace triton {
  namespace engines {
    namespace symbolic {

      SymbolicSummary::SymbolicSummary() {
        this->node      = nullptr;
        this->reference = 0;
        this->result    = 0;
        this->size      = 0;
      }


      SymbolicSummary::SymbolicSummary(triton::smt2lib::smtAstAbstractNode* node) {
        this->node      = node;
        this->reference = 1;

        try {
          this->result = triton::api.evaluateAst(node);
        }
        catch (...) {
          this->result = 0;
        }

        try {
          this->size = node->getBitvectorSize();
        }
        catch (...) {
          this->size = 0;
        }

      }


      SymbolicSummary::SymbolicSummary(const SymbolicSummary& other) {
        this->node      = other.node;
        this->reference = other.reference;
        this->result    = other.result;
        this->size      = other.size;
      }


      void SymbolicSummary::operator=(const SymbolicSummary& other) {
        this->node      = other.node;
        this->reference = other.reference;
        this->result    = other.result;
        this->size      = other.size;
      }


      SymbolicSummary::~SymbolicSummary() {
      }


      triton::smt2lib::smtAstAbstractNode* SymbolicSummary::getNode(void) {
        return this->node;
      }


      triton::uint32 SymbolicSummary::getReference(void) {
        return this->reference;
      }


      triton::uint512 SymbolicSummary::getResult(void) {
        return this->result;
      }


      triton::uint32 SymbolicSummary::getSize(void) {
        return this->size;
      }


      void SymbolicSummary::incReference(void) {
        this->reference++;
      }


      bool operator==(SymbolicSummary& summary1, SymbolicSummary& summary2) {
        return ((summary1.getResult() == summary2.getResult()) && (summary1.getSize() == summary2.getSize()));
      }

      /* The map for AST summaries. */
      std::map<triton::uint512, std::list<triton::engines::symbolic::SymbolicSummary>> astSummaries;

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */

