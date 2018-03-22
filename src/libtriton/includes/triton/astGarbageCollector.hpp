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

#include <triton/ast.hpp>
#include <triton/dllexport.hpp>
#include <triton/modes.hpp>
#include <triton/tritonTypes.hpp>



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
    class AstGarbageCollector {
      private:
        //! Modes API
        const triton::modes::Modes& modes;

        //! Defines if this instance is used as a backup.
        bool backupFlag;

        //! Copies an AstGarbageCollectors..
        void copy(const AstGarbageCollector& other);

      protected:
        //! This container contains all allocated nodes.
        std::set<triton::ast::AbstractNode*> allocatedNodes;

        //! This map maintains a link between symbolic variables and their nodes.
        std::map<std::string, std::vector<triton::ast::AbstractNode*>> variableNodes;

      public:
        //! Constructor.
        TRITON_EXPORT AstGarbageCollector(const triton::modes::Modes& modes, bool isBackup=false);

        //! Constructor by copy.
        TRITON_EXPORT AstGarbageCollector(const AstGarbageCollector& other);

        //! Destructor.
        TRITON_EXPORT ~AstGarbageCollector();

        //! Copies an AstGarbageCollector.
        TRITON_EXPORT AstGarbageCollector& operator=(const AstGarbageCollector& other);

        //! Go through every allocated nodes and free them.
        TRITON_EXPORT void freeAllAstNodes(void);

        //! Frees a set of nodes and removes them from the global container.
        TRITON_EXPORT void freeAstNodes(std::set<triton::ast::AbstractNode*>& nodes);

        //! Extracts all unique nodes from a partial AST into the uniqueNodes set.
        TRITON_EXPORT void extractUniqueAstNodes(std::set<triton::ast::AbstractNode*>& uniqueNodes, triton::ast::AbstractNode* root) const;

        //! Records the allocated node or returns the same node if it already exists inside the dictionaries.
        TRITON_EXPORT triton::ast::AbstractNode* recordAstNode(triton::ast::AbstractNode* node);

        //! Records a variable AST node.
        TRITON_EXPORT void recordVariableAstNode(const std::string& name, triton::ast::AbstractNode* node);

        //! Returns all allocated nodes.
        TRITON_EXPORT const std::set<triton::ast::AbstractNode*>& getAllocatedAstNodes(void) const;

        //! Returns all variable nodes recorded.
        TRITON_EXPORT const std::map<std::string, std::vector<triton::ast::AbstractNode*>>& getAstVariableNodes(void) const;

        //! Returns the node of a recorded variable.
        TRITON_EXPORT std::vector<triton::ast::AbstractNode*> getAstVariableNode(const std::string& name) const;

        //! Sets all allocated nodes.
        TRITON_EXPORT void setAllocatedAstNodes(const std::set<triton::ast::AbstractNode*>& nodes);

        //! Sets all variable nodes recorded.
        TRITON_EXPORT void setAstVariableNodes(const std::map<std::string, std::vector<triton::ast::AbstractNode*>>& nodes);
    };

  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ASTGARBAGECOLLECTOR_H */

