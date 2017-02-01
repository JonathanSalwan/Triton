//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ASTGARBAGECOLLECTOR_H
#define TRITON_ASTGARBAGECOLLECTOR_H

#include <set>
#include <string>

#include "ast.hpp"
#include "astDictionaries.hpp"
#include "modes.hpp"
#include "tritonTypes.hpp"



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The AST namespace
  namespace ast {
  /*!
   *  \ingroup triton
   *  \addtogroup ast
   *  @{
   */

    //! \class AstGarbageCollector
    /*! \brief The AST garbage collector class */
    class AstGarbageCollector : public triton::ast::AstDictionaries {
      private:
        //! Modes API
        triton::modes::Modes* modes;

      protected:
        //! Defines if this instance is used as a backup.
        bool backupFlag;

        //! This container contains all allocated nodes.
        std::set<triton::ast::AbstractNode*> allocatedNodes;

        //! This map maintains a link between symbolic variables and their nodes.
        std::map<std::string, triton::ast::AbstractNode*> variableNodes;

      public:
        //! Constructor.
        AstGarbageCollector(triton::modes::Modes* modes, bool isBackup=false);

        //! Constructor by copy.
        AstGarbageCollector(const AstGarbageCollector& other);

        //! Destructor.
        virtual ~AstGarbageCollector();

        //! Copies an AstGarbageCollectors.
        void operator=(const AstGarbageCollector& other);

        //! Copies an AstGarbageCollectors..
        void copy(const AstGarbageCollector& other);

        //! Go through every allocated nodes and free them.
        void freeAllAstNodes(void);

        //! Frees a set of nodes and removes them from the global container.
        void freeAstNodes(std::set<triton::ast::AbstractNode*>& nodes);

        //! Extracts all unique nodes from a partial AST into the uniqueNodes set.
        void extractUniqueAstNodes(std::set<triton::ast::AbstractNode*>& uniqueNodes, triton::ast::AbstractNode* root) const;

        //! Records the allocated node or returns the same node if it already exists inside the dictionaries.
        triton::ast::AbstractNode* recordAstNode(triton::ast::AbstractNode* node);

        //! Records a variable AST node.
        void recordVariableAstNode(const std::string& name, triton::ast::AbstractNode* node);

        //! Returns all allocated nodes.
        const std::set<triton::ast::AbstractNode*>& getAllocatedAstNodes(void) const;

        //! Returns all variable nodes recorded.
        const std::map<std::string, triton::ast::AbstractNode*>& getAstVariableNodes(void) const;

        //! Returns the node of a recorded variable.
        triton::ast::AbstractNode* getAstVariableNode(const std::string& name) const;

        //! Sets all allocated nodes.
        void setAllocatedAstNodes(const std::set<triton::ast::AbstractNode*>& nodes);

        //! Sets all variable nodes recorded.
        void setAstVariableNodes(const std::map<std::string, triton::ast::AbstractNode*>& nodes);

        //! Returns true if this garbage collector is used as backup.
        bool isBackup(void) const;
    };

  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ASTGARBAGECOLLECTOR_H */

