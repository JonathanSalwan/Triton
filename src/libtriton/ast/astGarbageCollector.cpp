//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/astGarbageCollector.hpp>
#include <triton/exceptions.hpp>



namespace triton {
  namespace ast {

    AstGarbageCollector::AstGarbageCollector(triton::modes::Modes* modes, bool isBackup)
      : triton::ast::AstDictionaries(isBackup) {

      if (modes == nullptr)
        throw triton::exceptions::AstGarbageCollector("AstGarbageCollector::AstGarbageCollector(): The modes API cannot be null.");

      this->backupFlag = isBackup;
      this->modes      = modes;
    }


    AstGarbageCollector::AstGarbageCollector(const AstGarbageCollector& other)
      : triton::ast::AstDictionaries(other) {
      this->copy(other);
    }


    void AstGarbageCollector::operator=(const AstGarbageCollector& other) {
      triton::ast::AstDictionaries::operator=(other);
      this->copy(other);
    }


    void AstGarbageCollector::copy(const AstGarbageCollector& other) {
      /* Remove unused nodes before the assignation */
      for (auto it = this->allocatedNodes.begin(); it != this->allocatedNodes.end(); it++) {
        if (other.allocatedNodes.find(*it) == other.allocatedNodes.end())
          delete *it;
      }
      this->allocatedNodes  = other.allocatedNodes;
      this->backupFlag      = true;
      this->modes           = other.modes;
      this->variableNodes   = other.variableNodes;
    }


    AstGarbageCollector::~AstGarbageCollector() {
      if (this->backupFlag == false)
        this->freeAllAstNodes();
    }


    void AstGarbageCollector::freeAllAstNodes(void) {
      for (auto it = this->allocatedNodes.begin(); it != this->allocatedNodes.end(); it++)
        delete *it;

      this->variableNodes.clear();
      this->allocatedNodes.clear();
    }


    void AstGarbageCollector::freeAstNodes(std::set<triton::ast::AbstractNode*>& nodes) {
      std::set<triton::ast::AbstractNode*>::iterator it;

      /* Do not delete AST nodes if the AST_DICTIONARIES optimization is enabled */
      if (this->modes->isModeEnabled(triton::modes::AST_DICTIONARIES))
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
      if (this->modes->isModeEnabled(triton::modes::AST_DICTIONARIES)) {
        triton::ast::AbstractNode* ret = this->browseAstDictionaries(node);
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
      for (auto it = this->allocatedNodes.begin(); it != this->allocatedNodes.end(); it++) {
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

