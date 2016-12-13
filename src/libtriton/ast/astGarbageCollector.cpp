//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <astGarbageCollector.hpp>
#include <exceptions.hpp>



namespace triton {
  namespace ast {

    AstGarbageCollector::AstGarbageCollector(triton::engines::symbolic::SymbolicEngine* symbolicEngine) {
      if (symbolicEngine == nullptr)
        throw triton::exceptions::AstGarbageCollector("AstGarbageCollector::AstGarbageCollector(): The symbolicEngine API cannot be null.");
      this->symbolicEngine = symbolicEngine;
    }


    AstGarbageCollector::~AstGarbageCollector() {
      this->freeAllAstNodes();
    }


    void AstGarbageCollector::freeAllAstNodes(void) {
      std::set<triton::ast::AbstractNode*>::iterator it;

      for (it = this->allocatedNodes.begin(); it != this->allocatedNodes.end(); it++)
        delete *it;

      this->variableNodes.clear();
      this->allocatedNodes.clear();
    }


    void AstGarbageCollector::freeAstNodes(std::set<triton::ast::AbstractNode*>& nodes) {
      std::set<triton::ast::AbstractNode*>::iterator it;

      /* Do not delete AST nodes if the AST_DICTIONARIES optimization is enabled */
      if (this->symbolicEngine->isOptimizationEnabled(triton::engines::symbolic::AST_DICTIONARIES))
        return;

      for (it = nodes.begin(); it != nodes.end(); it++) {
        /* Remove the node from the global set */
        this->allocatedNodes.erase(*it);

        /* Remove the node from the global variables map */
        if ((*it)->getKind() == triton::ast::VARIABLE_NODE)
          this->variableNodes.erase(reinterpret_cast<triton::ast::VariableNode*>(*it)->getValue());

        /* Delete the node */
        delete *it;
      }

      nodes.clear();
    }


    void AstGarbageCollector::extractUniqueAstNodes(std::set<triton::ast::AbstractNode*>& uniqueNodes, triton::ast::AbstractNode* root) const {
      std::vector<triton::ast::AbstractNode*>::const_iterator it;
      uniqueNodes.insert(root);
      for (it = root->getChilds().begin(); it != root->getChilds().end(); it++)
        this->extractUniqueAstNodes(uniqueNodes, *it);
    }


    triton::ast::AbstractNode* AstGarbageCollector::recordAstNode(triton::ast::AbstractNode* node) {
      /* Check if the AST_DICTIONARIES is enabled. */
      if (this->symbolicEngine->isOptimizationEnabled(triton::engines::symbolic::AST_DICTIONARIES)) {
        triton::ast::AbstractNode* ret = this->symbolicEngine->browseAstDictionaries(node);
        if (ret != nullptr)
          return ret;
      }
      else {
        /* Record the node */
        this->allocatedNodes.insert(node);
      }
      return node;
    }


    void AstGarbageCollector::recordVariableAstNode(const std::string& name, triton::ast::AbstractNode* node) {
      this->variableNodes[name] = node;
    }


    const std::set<triton::ast::AbstractNode*>& AstGarbageCollector::getAllocatedAstNodes(void) const {
      return this->allocatedNodes;
    }


    const std::map<std::string, triton::ast::AbstractNode*>& AstGarbageCollector::getAstVariableNodes(void) const {
      return this->variableNodes;
    }


    triton::ast::AbstractNode* AstGarbageCollector::getAstVariableNode(const std::string& name) const {
      if (this->variableNodes.find(name) != this->variableNodes.end())
        return this->variableNodes.at(name);
      return nullptr;
    }


    void AstGarbageCollector::setAllocatedAstNodes(const std::set<triton::ast::AbstractNode*>& nodes) {
      /* Remove unused nodes before the assignation */
      for (std::set<triton::ast::AbstractNode*>::iterator it = this->allocatedNodes.begin(); it != this->allocatedNodes.end(); it++) {
        if (nodes.find(*it) == nodes.end())
          delete *it;
      }
      this->allocatedNodes = nodes;
    }


    void AstGarbageCollector::setAstVariableNodes(const std::map<std::string, triton::ast::AbstractNode*>& nodes) {
      this->variableNodes = nodes;
    }

  }; /* ast namespace */
}; /*triton namespace */

