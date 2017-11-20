//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/astContext.hpp>          // for Context
#include <triton/coreUtils.hpp>
#include <triton/exceptions.hpp>
#include <triton/symbolicEngine.hpp>

#include <cstring>
#include <new>




/*! \page engine_DSE_page Dynamic Symbolic Execution
    \brief [**internal**] All information about the dynamic symbolic execution engine.

\tableofcontents

\section engine_DSE_description Description
<hr>

Triton contains an internal Dynamic Symbolic Execution (DSE) engine. This engine maintains a
symbolic states of registers and part of memory at each program point.

The symbolic engine maintains:

- a table of symbolic registers states
- a map of symbolic memory states
- a global set of all symbolic references

During the execution, according to the instruction semantics, the table of symbolic registers states
is updated at each instruction executed. This table is modeled by a correspondence of \f$ \langle rid \rightarrow \varphi_x \rangle \f$ for
each register where \f$ rid \in N \f$ represents the unique register's reference and \f$ \varphi_{x \in N} \f$ represents the unique
symbolic expression's reference and the link to its SMT graph. In other words, at each program point,
all registers points on its symbolic expression which represents the last semantics of the assignment.

 Step | Register                | Instruction | Set of symbolic expressions
------|-------------------------|-------------|------------------------------------
 init | eax = None              | None        | \f$ \bot \f$
 1    | eax = \f$ \varphi_1 \f$ | mov eax, 0  | \f$ \{\varphi_1 = 0\} \f$
 2    | eax = \f$ \varphi_2 \f$ | inc eax     | \f$ \{\varphi_1 = 0, \varphi_2 = \varphi_1 + 1\} \f$
 3    | eax = \f$ \varphi_3 \f$ | add eax, 5  | \f$ \{\varphi_1 = 0, \varphi_2 = \varphi_1 + 1, \varphi_3 = \varphi_2 + 5\} \f$

Like with registers, Triton maintains a symbolic states of part of memory. This is modeled by a correspondence
of \f$ \langle addr \rightarrow \varphi_x \rangle \f$ for each address where \f$ addr \in N \f$ represents the address of the
memory and \f$ \varphi_{x \in N} \f$ represents the unique symbolic expression's reference.

 Step | Register                | Memory                  | Instruction | Set of Symbolic Expressions
------|-------------------------|-------------------------|-------------|----------------------------
 1    | eax = \f$ \varphi_1 \f$ | n/a                     | mov eax, 0  | \f$ \{\varphi_1 = 0\} \f$
 2    | n/a                     | sp = \f$ \varphi_2 \f$  | push eax    | \f$ \{\varphi_1 = 0, \varphi_2 = \varphi_1\} \f$
 ...  | ...                     | ...                     | ...         | ...
 10   | ebx = \f$ \varphi_3 \f$ | n/a                     | pop ebx     | \f$ \{\varphi_1 = 0, \varphi_2 = \varphi_1, \varphi_3 = \varphi_2\} \f$

Based on this process, we know that \f$ ebx = eax = 0 \f$.

There also exists an important point, if there is no previous symbolic reference of a register or part of memory when
the instruction is processed, Triton builds the expression with the concretization of the value and assigns the
expression to a new symbolic reference. This allows us to start the analysis everywhere.

*/




namespace triton {
  namespace engines {
    namespace symbolic {

      SymbolicEngine::SymbolicEngine(triton::arch::Architecture* architecture,
                                     const triton::modes::Modes& modes,
                                     triton::AstContext& astCtxt,
                                     triton::callbacks::Callbacks* callbacks,
                                     bool isBackup)
        : triton::engines::symbolic::SymbolicSimplification(callbacks),
          triton::engines::symbolic::PathManager(modes, astCtxt),
          astCtxt(astCtxt),
          modes(modes) {

        if (architecture == nullptr)
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::SymbolicEngine(): The architecture pointer must be valid.");

        this->architecture      = architecture;
        this->numberOfRegisters = this->architecture->numberOfRegisters();
        this->symbolicReg.resize(this->numberOfRegisters);
        this->callbacks       = callbacks;
        this->backupFlag      = isBackup;
        this->enableFlag      = true;
        this->uniqueSymExprId = 0;
        this->uniqueSymVarId  = 0;
      }


      void SymbolicEngine::copy(const SymbolicEngine& other) {
        this->numberOfRegisters = other.numberOfRegisters;
        this->symbolicReg = other.symbolicReg;

        /*
         * The backup flag cannot be spread. once a class is tagged as
         * backup, it always be a backup class.
         */
        this->alignedMemoryReference      = other.alignedMemoryReference;
        this->architecture                = other.architecture;
        this->backupFlag                  = true;
        this->callbacks                   = other.callbacks;
        this->enableFlag                  = other.enableFlag;
        this->memoryReference             = other.memoryReference;
        this->symbolicExpressions         = other.symbolicExpressions;
        this->symbolicVariables           = other.symbolicVariables;
        this->uniqueSymExprId             = other.uniqueSymExprId;
        this->uniqueSymVarId              = other.uniqueSymVarId;
      }


      SymbolicEngine::SymbolicEngine(const SymbolicEngine& copy)
        : triton::engines::symbolic::SymbolicSimplification(copy),
          triton::engines::symbolic::PathManager(copy),
          astCtxt(copy.astCtxt),
          modes(copy.modes) {
        this->copy(copy);
      }


      void SymbolicEngine::operator=(const SymbolicEngine& other) {
        triton::engines::symbolic::SymbolicSimplification::operator=(other);
        triton::engines::symbolic::PathManager::operator=(other);

        /* Delete unused variables */
        for (auto& sv: this->symbolicVariables) {
          if (other.symbolicVariables.find(sv.first) == other.symbolicVariables.end())
            delete this->symbolicVariables[sv.first];
        }

        // We assume astCtxt didn't change
        // We assume modes didn't change
        this->copy(other);
      }


      SymbolicEngine::~SymbolicEngine() {
        /*
         * Don't delete symbolic expressions and symbolic variables
         * if this class is used as backup engine. Otherwise that may
         * result in a double-free bug if the original symbolic engine
         * is deleted too (cf: #385).
         */
        if (this->backupFlag == false) {
          /* Delete all symbolic variables */
          for (auto sv: this->symbolicVariables)
            delete sv.second;
        }
      }


      /*
       * Concretize a register. If the register is setup as nullptr, the next assignment
       * will be over the concretization. This method must be called before symbolic
       * processing.
       */
      void SymbolicEngine::concretizeRegister(const triton::arch::Register& reg) {
        triton::arch::registers_e parentId = reg.getParent();

        if (!this->architecture->isRegisterValid(parentId))
          return;

        this->symbolicReg[parentId] = nullptr;
      }


      /* Same as concretizeRegister but with all registers */
      void SymbolicEngine::concretizeAllRegister(void) {
        for (triton::uint32 i = 0; i < this->numberOfRegisters; i++)
          this->symbolicReg[i] = nullptr;
      }


      /*
       * Concretize a memory. If the memory is not found into the map, the next
       * assignment will be over the concretization. This method must be called
       * before symbolic processing.
       */
      void SymbolicEngine::concretizeMemory(const triton::arch::MemoryAccess& mem) {
        triton::uint64 addr = mem.getAddress();
        triton::uint32 size = mem.getSize();

        for (triton::uint32 index = 0; index < size; index++)
          this->concretizeMemory(addr+index);
      }


      /*
       * Concretize a memory. If the memory is not found into the map, the next
       * assignment will be over the concretization. This method must be called
       * before symbolic processing.
       */
      void SymbolicEngine::concretizeMemory(triton::uint64 addr) {
        this->memoryReference.erase(addr);
        if (this->modes.isModeEnabled(triton::modes::ALIGNED_MEMORY))
          this->removeAlignedMemory(addr, BYTE_SIZE);
      }


      /* Same as concretizeMemory but with all address memory */
      void SymbolicEngine::concretizeAllMemory(void) {
        this->memoryReference.clear();
        this->alignedMemoryReference.clear();
      }


      /* Gets an aligned entry. */
      triton::SharedSymbolicExpression const& SymbolicEngine::getAlignedMemory(triton::uint64 address, triton::uint32 size) {
        if (this->isAlignedMemory(address, size))
          return this->alignedMemoryReference[std::make_pair(address, size)];
        throw triton::exceptions::SymbolicEngine("SymbolicEngine::getAlignedMemory(): memory not found");
      }


      /* Checks if the aligned memory is recored. */
      bool SymbolicEngine::isAlignedMemory(triton::uint64 address, triton::uint32 size) {
        if (this->alignedMemoryReference.find(std::make_pair(address, size)) != this->alignedMemoryReference.end())
          return true;
        return false;
      }


      /* Adds an aligned memory */
      void SymbolicEngine::addAlignedMemory(triton::uint64 address, triton::uint32 size, triton::SharedSymbolicExpression const& expr) {
        this->removeAlignedMemory(address, size);
        if (!(this->modes.isModeEnabled(triton::modes::ONLY_ON_SYMBOLIZED) && expr->getAst()->isSymbolized() == false))
          this->alignedMemoryReference[std::make_pair(address, size)] = expr;
      }


      /* Removes an aligned memory */
      void SymbolicEngine::removeAlignedMemory(triton::uint64 address, triton::uint32 size) {
        /* Remove overloaded positive ranges */
        for (triton::uint32 index = 0; index < size; index++) {
          this->alignedMemoryReference.erase(std::make_pair(address+index, BYTE_SIZE));
          this->alignedMemoryReference.erase(std::make_pair(address+index, WORD_SIZE));
          this->alignedMemoryReference.erase(std::make_pair(address+index, DWORD_SIZE));
          this->alignedMemoryReference.erase(std::make_pair(address+index, QWORD_SIZE));
          this->alignedMemoryReference.erase(std::make_pair(address+index, DQWORD_SIZE));
          this->alignedMemoryReference.erase(std::make_pair(address+index, QQWORD_SIZE));
          this->alignedMemoryReference.erase(std::make_pair(address+index, DQQWORD_SIZE));
        }

        /* Remove overloaded negative ranges */
        for (triton::uint32 index = 1; index < DQQWORD_SIZE; index++) {
          if (index < WORD_SIZE)
            this->alignedMemoryReference.erase(std::make_pair(address-index, WORD_SIZE));
          if (index < DWORD_SIZE)
            this->alignedMemoryReference.erase(std::make_pair(address-index, DWORD_SIZE));
          if (index < QWORD_SIZE)
            this->alignedMemoryReference.erase(std::make_pair(address-index, QWORD_SIZE));
          if (index < DQWORD_SIZE)
            this->alignedMemoryReference.erase(std::make_pair(address-index, DQWORD_SIZE));
          if (index < QQWORD_SIZE)
            this->alignedMemoryReference.erase(std::make_pair(address-index, QQWORD_SIZE));
          if (index < DQQWORD_SIZE)
            this->alignedMemoryReference.erase(std::make_pair(address-index, DQQWORD_SIZE));
        }
      }


      /* Returns the reference memory if it's referenced otherwise returns nullptr*/
      triton::SharedSymbolicExpression SymbolicEngine::getSymbolicMemory(triton::uint64 addr) const {
        auto it = this->memoryReference.find(addr);
        if (it != this->memoryReference.end())
          return it->second;

        return nullptr;
      }


      /* Returns the symbolic variable otherwise returns nullptr */
      SymbolicVariable* SymbolicEngine::getSymbolicVariableFromId(triton::usize symVarId) const {

        auto it = this->symbolicVariables.find(symVarId);
        if (it == this->symbolicVariables.end())
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::getSymbolicVariableFromId(): Unregistred variable.");
        return it->second;
      }


      /* Returns the symbolic variable otherwise returns nullptr */
      SymbolicVariable* SymbolicEngine::getSymbolicVariableFromName(const std::string& symVarName) const {

        // Assume variable was created by triton
        triton::usize id;
        if(sscanf(symVarName.c_str(), TRITON_SYMVAR_NAME "%zu", &id) == 1) {
          return getSymbolicVariableFromId(id);
        }

        for (auto& sv: this->symbolicVariables) {
          if (sv.second->getName() == symVarName)
            return sv.second;
        }

        return nullptr;
      }


      /* Returns all symbolic variables */
      const std::unordered_map<triton::usize, SymbolicVariable*>& SymbolicEngine::getSymbolicVariables(void) const {
        return this->symbolicVariables;
      }


      /* Returns the reg reference or nullptr*/
      triton::SharedSymbolicExpression const& SymbolicEngine::getSymbolicRegister(const triton::arch::Register& reg) const {
        triton::arch::registers_e parentId = reg.getParent();

        if (!this->architecture->isRegisterValid(parentId))
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::getSymbolicRegister(): Invalid Register");

        return this->symbolicReg.at(parentId);
      }


      /* Returns the symbolic address value */
      triton::uint8 SymbolicEngine::getSymbolicMemoryValue(triton::uint64 address) {
        triton::arch::MemoryAccess mem(address, BYTE_SIZE);
        return this->getSymbolicMemoryValue(mem).convert_to<triton::uint8>();
      }


      /* Returns the symbolic memory value */
      triton::uint512 SymbolicEngine::getSymbolicMemoryValue(const triton::arch::MemoryAccess& mem) {
        triton::ast::SharedAbstractNode node = this->getAstMemory(mem);
        return node->evaluate();
      }


      /* Returns the symbolic values of a memory area */
      std::vector<triton::uint8> SymbolicEngine::getSymbolicMemoryAreaValue(triton::uint64 baseAddr, triton::usize size) {
        std::vector<triton::uint8> area;

        for (triton::usize index = 0; index < size; index++)
          area.push_back(this->getSymbolicMemoryValue(baseAddr+index));

        return area;
      }


      /* Returns the symbolic register value */
      triton::uint512 SymbolicEngine::getSymbolicRegisterValue(const triton::arch::Register& reg) {
        return this->getAstRegister(reg)->evaluate();
      }


      /* Creates a new symbolic expression */
      /* Get an unique id.
       * Mainly used when a new symbolic expression is created */
      triton::usize SymbolicEngine::getUniqueSymExprId(void) {
        return this->uniqueSymExprId++;
      }


      /* Creates a new symbolic variable */
      /* Get an unique id.
       * Mainly used when a new symbolic variable is created */
      triton::usize SymbolicEngine::getUniqueSymVarId(void) {
        return this->uniqueSymVarId++;
      }


      /* Creates a new symbolic expression with comment */
      triton::SharedSymbolicExpression SymbolicEngine::newSymbolicExpression(triton::ast::SharedAbstractNode const& in_node, triton::engines::symbolic::symkind_e kind, const std::string& comment) {
        triton::usize id = this->getUniqueSymExprId();
        auto node = this->processSimplification(in_node);
        auto expr = triton::SharedSymbolicExpression(new(std::nothrow) SymbolicExpression(node, id, kind, comment));
        if (expr == nullptr)
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::newSymbolicExpression(): not enough memory");
        this->symbolicExpressions[id] = expr;
        return expr;//this->symbolicExpressions[id];
      }


      /* Removes the symbolic expression corresponding to the id */
      void SymbolicEngine::removeSymbolicExpression(triton::usize symExprId) {
        if (this->symbolicExpressions.find(symExprId) != this->symbolicExpressions.end()) {
          /* Delete and remove the pointer */
          this->symbolicExpressions.erase(symExprId);

          /* Concretize the register if it exists */
          for (triton::uint32 i = 0; i < this->numberOfRegisters; i++) {
            if (this->symbolicReg[i] != nullptr && this->symbolicReg[i]->getId() == symExprId) {
              this->symbolicReg[i] = nullptr;
              return;
            }
          }

          /* Concretize the memory if it exists */
          for (auto it = this->memoryReference.begin(); it != memoryReference.end(); it++) {
            if (it->second && it->second->getId() == symExprId) {
              this->concretizeMemory(it->first);
              return;
            }
          }

          // FIXME: Also try to remove it from alignedMemory
          // FIXME: Remove it from ast context too
        }

      }


      /* Gets the symbolic expression pointer from a symbolic id */
      triton::SharedSymbolicExpression SymbolicEngine::getSymbolicExpressionFromId(triton::usize symExprId) const {
        auto it = this->symbolicExpressions.find(symExprId);
        if (it == this->symbolicExpressions.end())
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::getSymbolicExpressionFromId(): symbolic expression id not found");

        if(auto sp = it->second.lock())
          return sp;

        this->symbolicExpressions.erase(symExprId);
        throw triton::exceptions::SymbolicEngine("SymbolicEngine::getSymbolicExpressionFromId(): symbolic expression is not available anymore");
      }


      /* Returns all symbolic expressions */
      std::unordered_map<triton::usize, triton::SharedSymbolicExpression> SymbolicEngine::getSymbolicExpressions(void) const {
        // Copy and clean up dead weak ref
        std::unordered_map<triton::usize, triton::SharedSymbolicExpression> ret;
        std::vector<triton::usize> toRemove;

        for(auto& kv: this->symbolicExpressions) {
          if(auto sp = kv.second.lock()) {
            ret[kv.first] = sp;
          } else
            toRemove.push_back(kv.first);
        }

        for(auto id: toRemove)
          this->symbolicExpressions.erase(id);

        return ret;
      }


      /* Returns the full symbolic expression backtracked. */
      triton::ast::SharedAbstractNode SymbolicEngine::unrollAst(triton::ast::SharedAbstractNode node) {
        // FIXME: Is it normal that we modify input? sometimes...
        // As we may or not return input and return value is an owning ptr, input has to be owning too...

        if (node->getKind() == triton::ast::REFERENCE_NODE) {
          return reinterpret_cast<triton::ast::ReferenceNode*>(node.get())->getAst();
        }

        std::vector<triton::ast::SharedAbstractNode>& children = node->getChildren();
        for (triton::uint32 index = 0; index < children.size(); index++)
          children[index] = this->unrollAst(children[index]);

        return node;
      }


      /* [private method] Slices all expressions from a given node */
      void SymbolicEngine::sliceExpressions(triton::ast::AbstractNode* node, std::map<triton::usize, triton::SharedSymbolicExpression>& exprs) {
        std::vector<triton::ast::SharedAbstractNode>& children = node->getChildren();

        if (node->getKind() == triton::ast::REFERENCE_NODE) {
          triton::ast::ReferenceNode* ref_node = reinterpret_cast<triton::ast::ReferenceNode*>(node);

          triton::usize id = ref_node->getId();

          if (exprs.find(id) == exprs.end()) {
            // FIXME: WARNING: Here we need "ast have ownership of its reference"
            exprs[id] = this->getSymbolicExpressionFromId(id);
            this->sliceExpressions(ref_node->getAst().get(), exprs);
          }
        }

        for (triton::uint32 index = 0; index < children.size(); index++) {
          this->sliceExpressions(children[index].get(), exprs);
        }
      }


      /* Slices all expressions from a given one */
      std::map<triton::usize, triton::SharedSymbolicExpression> SymbolicEngine::sliceExpressions(triton::SharedSymbolicExpression const& expr) {
        std::map<triton::usize, triton::SharedSymbolicExpression> exprs;

        if (expr == nullptr)
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::sliceExpressions(): expr cannot be null.");

        exprs[expr->getId()] = expr;
        this->sliceExpressions(expr->getAst(), exprs);

        return exprs;
      }


      /* Returns a list which contains all tainted expressions */
      std::list<triton::SharedSymbolicExpression> SymbolicEngine::getTaintedSymbolicExpressions(void) const {
        std::list<triton::SharedSymbolicExpression> taintedExprs;
        std::vector<triton::usize> invalidSymExpr;

        for (auto it = this->symbolicExpressions.begin(); it != this->symbolicExpressions.end(); it++) {
          if (auto sp = it->second.lock()) {
            if(sp->isTainted)
              taintedExprs.push_back(sp);
          } else {
            invalidSymExpr.push_back(it->first);
          }
        }

        for(auto id: invalidSymExpr)
          this->symbolicExpressions.erase(id);

        return taintedExprs;
      }


      /* Returns the map of symbolic registers defined */
      std::map<triton::arch::registers_e, triton::SharedSymbolicExpression> SymbolicEngine::getSymbolicRegisters(void) const {
        std::map<triton::arch::registers_e, triton::SharedSymbolicExpression> ret;

        for (triton::uint32 it = 0; it < this->numberOfRegisters; it++) {
          if (this->symbolicReg[it] != nullptr) {
            ret[arch::registers_e(it)] = this->symbolicReg[it];
          }
        }

        return ret;
      }


      /* Returns the map of symbolic memory defined */
      std::map<triton::uint64, triton::SharedSymbolicExpression> const& SymbolicEngine::getSymbolicMemory(void) const {
        return this->memoryReference;
      }


      /*
       * Converts an expression id to a symbolic variable.
       * e.g:
       * #43 = (_ bv10 8)
       * convertExpressionToSymbolicVariable(43, 8)
       * #43 = SymVar_4
       */
      SymbolicVariable* SymbolicEngine::convertExpressionToSymbolicVariable(triton::usize exprId, triton::uint32 symVarSize, const std::string& symVarComment) {
        triton::SharedSymbolicExpression expression = this->getSymbolicExpressionFromId(exprId);
        SymbolicVariable* symVar = this->newSymbolicVariable(triton::engines::symbolic::UNDEF, 0, symVarSize, symVarComment);

        if (expression->getAst())
           this->setConcreteSymbolicVariableValue(*symVar, expression->getAst()->evaluate());

        expression->setAst(symVar->getShareAst());

        return symVar;
      }


      /* The memory size is used to define the symbolic variable's size. */
      SymbolicVariable* SymbolicEngine::convertMemoryToSymbolicVariable(const triton::arch::MemoryAccess& mem, const std::string& symVarComment) {
        SymbolicVariable* symVar        = nullptr;
        triton::uint64 memAddr          = mem.getAddress();
        triton::uint32 symVarSize       = mem.getSize();
        triton::uint512 cv              = this->architecture->getConcreteMemoryValue(mem);

        /* First we create a symbolic variable */
        symVar = this->newSymbolicVariable(triton::engines::symbolic::MEM, memAddr, symVarSize * BYTE_SIZE_BIT, symVarComment);

        /* Create the AST node */
        auto& symVarNode = symVar->getShareAst();

        /* Setup the concrete value to the symbolic variable */
        this->setConcreteSymbolicVariableValue(*symVar, cv);

        /* Record the aligned symbolic variable for a symbolic optimization */
        if (this->modes.isModeEnabled(triton::modes::ALIGNED_MEMORY)) {
          auto se = this->newSymbolicExpression(symVarNode, triton::engines::symbolic::MEM, "aligned Byte reference");
          this->addAlignedMemory(memAddr, symVarSize, se);
        }

        /*  Split expression in bytes */
        for (triton::sint32 index = symVarSize-1; index >= 0; index--) {

          /* Isolate the good part of the symbolic variable */
          auto tmp = this->astCtxt.extract(((BYTE_SIZE_BIT * (index+1)) - 1), ((BYTE_SIZE_BIT * (index+1)) - BYTE_SIZE_BIT), symVarNode);

          /* Check if the memory address is already defined */
          triton::SharedSymbolicExpression se = this->getSymbolicMemory(memAddr+index);
          if (se == nullptr) {
            se = this->newSymbolicExpression(tmp, triton::engines::symbolic::MEM, "Byte reference");
            /* Add the new memory reference */
            this->addMemoryReference(memAddr+index, se);
          } else {
            // FIXME: Here we update the ast but the memory Reference may be use in
            // another ast which then become invalid. Should we create a new SE everytime?
            se->setAst(tmp);
          }
          se->setOriginMemory(triton::arch::MemoryAccess(memAddr+index, BYTE_SIZE));
        }

        return symVar;
      }


      SymbolicVariable* SymbolicEngine::convertRegisterToSymbolicVariable(const triton::arch::Register& reg, const std::string& symVarComment) {
        const triton::arch::Register& parent  = this->architecture->getRegister(reg.getParent());
        triton::uint32 symVarSize             = reg.getBitSize();
        triton::uint512 cv                    = this->architecture->getConcreteRegisterValue(reg);

        if (!this->architecture->isRegisterValid(parent.getId()))
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::convertRegisterToSymbolicVariable(): Invalid register id");

        /* Get the symbolic expression */
        auto const& expression = this->getSymbolicRegister(reg);

        /* Create the symbolic variable */
        SymbolicVariable* symVar = this->newSymbolicVariable(triton::engines::symbolic::REG, parent.getId(), symVarSize, symVarComment);

        /* Create the AST node */
        auto tmp = this->astCtxt.zx(parent.getBitSize() - symVarSize, symVar->getShareAst());
        /* Setup the concrete value to the symbolic variable */
        this->setConcreteSymbolicVariableValue(*symVar, cv);

        if (expression == nullptr) {
          /* Create the symbolic expression */
          auto se = this->newSymbolicExpression(tmp, triton::engines::symbolic::REG);
          se->setOriginRegister(reg);
          this->symbolicReg[parent.getId()] = se;
        } else {
          /* Set the AST node */
          expression->setAst(tmp);
        }

        return symVar;
      }


      /* Adds a new symbolic variable */
      SymbolicVariable* SymbolicEngine::newSymbolicVariable(triton::engines::symbolic::symkind_e kind, triton::uint64 kindValue, triton::uint32 size, const std::string& comment) {
        triton::usize uniqueId = this->getUniqueSymVarId();
        SymbolicVariable* symVar = new(std::nothrow) SymbolicVariable(this->astCtxt, kind, kindValue, uniqueId, size, comment);

        if (symVar == nullptr)
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::newSymbolicVariable(): Cannot allocate a new symbolic variable");

        this->symbolicVariables[uniqueId] = symVar;
        return symVar;
      }


      /* Returns a symbolic operand based on the abstract wrapper. */
      triton::ast::SharedAbstractNode SymbolicEngine::getAstOperand(const triton::arch::OperandWrapper& op) {
        switch (op.getType()) {
          case triton::arch::OP_IMM: return this->getAstImmediate(op.getConstImmediate());
          case triton::arch::OP_MEM: return this->getAstMemory(op.getConstMemory());
          case triton::arch::OP_REG: return this->getAstRegister(op.getConstRegister());
          default:
            throw triton::exceptions::SymbolicEngine("SymbolicEngine::getAstOperand(): Invalid operand.");
        }
      }


      /* Returns a symbolic operand based on the abstract wrapper. */
      triton::ast::SharedAbstractNode const& SymbolicEngine::getAstOperand(triton::arch::Instruction& inst, const triton::arch::OperandWrapper& op) {
        switch (op.getType()) {
          case triton::arch::OP_IMM: return this->getAstImmediate(inst, op.getConstImmediate());
          case triton::arch::OP_MEM: return this->getAstMemory(inst, op.getConstMemory());
          case triton::arch::OP_REG: return this->getAstRegister(inst, op.getConstRegister());
          default:
            throw triton::exceptions::SymbolicEngine("SymbolicEngine::getAstOperand(): Invalid operand.");
        }
      }


      /* Returns a symbolic immediate */
      triton::ast::SharedAbstractNode SymbolicEngine::getAstImmediate(const triton::arch::Immediate& imm) {
        return this->astCtxt.bv(imm.getValue(), imm.getBitSize());
      }


      /* Returns a symbolic immediate and defines the immediate as input of the instruction */
      triton::ast::SharedAbstractNode const& SymbolicEngine::getAstImmediate(triton::arch::Instruction& inst, const triton::arch::Immediate& imm) {
        triton::ast::SharedAbstractNode node = this->getAstImmediate(imm);
        triton::SharedSymbolicExpression se = this->newSymbolicExpression(node, triton::engines::symbolic::IMM, "SymbolicImmediate");
        inst.setReadImmediate(imm, se);
        return se->getShareAst();
      }


      /* Returns a symbolic memory */
      triton::ast::SharedAbstractNode SymbolicEngine::getAstMemory(const triton::arch::MemoryAccess& mem) {
        std::list<triton::ast::SharedAbstractNode> opVec;

        triton::ast::SharedAbstractNode tmp = nullptr;
        triton::uint64 address                    = mem.getAddress();
        triton::uint32 size                       = mem.getSize();
        triton::uint8 concreteValue[DQQWORD_SIZE] = {0};
        triton::uint512 value                     = this->architecture->getConcreteMemoryValue(mem);

        triton::utils::fromUintToBuffer(value, concreteValue);

        /*
         * Symbolic optimization
         * If the memory access is aligned, don't split the memory.
         */
        if (this->modes.isModeEnabled(triton::modes::ALIGNED_MEMORY) && this->isAlignedMemory(address, size))
          return this->getAlignedMemory(address, size)->getShareAst();

        /* Iterate on every memory cells to use their symbolic or concrete values */
        while (size) {
          /* Check if the memory cell is already symbolic */
          if (auto se = this->getSymbolicMemory(address + size - 1)) {
            tmp = this->astCtxt.reference(se);
            opVec.push_back(this->astCtxt.extract((BYTE_SIZE_BIT - 1), 0, tmp));
          }
          /* Otherwise, use the concerte value */
          else {
            tmp = this->astCtxt.bv(concreteValue[size - 1], BYTE_SIZE_BIT);
            opVec.push_back(this->astCtxt.extract((BYTE_SIZE_BIT - 1), 0, tmp));
          }
          size--;
        }

        /* Concatenate all memory cell to create a bit vector with the appropriate memory access */
        switch (opVec.size()) {
          case DQQWORD_SIZE:
          case QQWORD_SIZE:
          case DQWORD_SIZE:
          case QWORD_SIZE:
          case DWORD_SIZE:
          case WORD_SIZE:
            tmp = this->astCtxt.concat(opVec);
            break;
          case BYTE_SIZE:
            tmp = opVec.front();
            break;
        }

        return tmp;
      }


      /* Returns a symbolic memory and defines the memory as input of the instruction */
      triton::ast::SharedAbstractNode const& SymbolicEngine::getAstMemory(triton::arch::Instruction& inst, const triton::arch::MemoryAccess& mem) {
        triton::ast::SharedAbstractNode tmp = this->getAstMemory(mem);
        triton::SharedSymbolicExpression se = this->newSymbolicExpression(tmp, triton::engines::symbolic::MEM, "SymbolicMemory");

        inst.setLoadAccess(mem, se);
        inst.addSymbolicExpression(se);

        /* Set implicit read of the base register (LEA) */
        if (this->architecture->isRegisterValid(mem.getConstBaseRegister()))
          this->getAstRegister(inst, mem.getConstBaseRegister());

        /* Set implicit read of the index register (LEA) */
        if (this->architecture->isRegisterValid(mem.getConstIndexRegister()))
          this->getAstRegister(inst, mem.getConstIndexRegister());

        return se->getShareAst();
      }


      /* Returns a symbolic register */
      triton::ast::SharedAbstractNode SymbolicEngine::getAstRegister(const triton::arch::Register& reg) {
        triton::ast::SharedAbstractNode op = nullptr;

        /* Check if the register is already symbolic */
        if (auto const& symReg = this->getSymbolicRegister(reg)) {
          triton::uint32 high  = reg.getHigh();
          triton::uint32 low   = reg.getLow();
          op = this->astCtxt.extract(high, low, this->astCtxt.reference(symReg));
        } else { /* Otherwise, use the concrete value */
          triton::uint32 bvSize = reg.getBitSize();
          op = this->astCtxt.bv(this->architecture->getConcreteRegisterValue(reg), bvSize);
        }

        return op;
      }


      /* Returns a symbolic register and defines the register as input of the instruction */
      triton::ast::SharedAbstractNode const& SymbolicEngine::getAstRegister(triton::arch::Instruction& inst, const triton::arch::Register& reg) {
        triton::ast::SharedAbstractNode op = this->getAstRegister(reg);
        triton::SharedSymbolicExpression expr = this->newSymbolicExpression(op, triton::engines::symbolic::REG, "Symbolic Register");
        inst.setReadRegister(reg, expr);

        return expr->getShareAst();
      }


      /* Returns the new symbolic abstract expression and links this expression to the instruction. */
      triton::SharedSymbolicExpression const& SymbolicEngine::createSymbolicExpression(triton::arch::Instruction& inst, triton::ast::SharedAbstractNode const& node, const triton::arch::OperandWrapper& dst, const std::string& comment) {
        switch (dst.getType()) {
          case triton::arch::OP_MEM: return this->createSymbolicMemoryExpression(inst, node, dst.getConstMemory(), comment);
          case triton::arch::OP_REG: return this->createSymbolicRegisterExpression(inst, node, dst.getConstRegister(), comment);
          default:
            throw triton::exceptions::SymbolicEngine("SymbolicEngine::createSymbolicExpression(): Invalid operand.");
        }
      }


      /* Returns the new symbolic memory expression */
      triton::SharedSymbolicExpression const& SymbolicEngine::createSymbolicMemoryExpression(triton::arch::Instruction& inst, triton::ast::SharedAbstractNode const& node, const triton::arch::MemoryAccess& mem, const std::string& comment) {
        std::list<triton::ast::SharedAbstractNode> ret;

        triton::uint64 address   = mem.getAddress();
        triton::uint32 writeSize = mem.getSize();

        /* Record the aligned memory for a symbolic optimization */

        if (this->modes.isModeEnabled(triton::modes::ALIGNED_MEMORY)) {
          // Add a full expression if it doesn't already exists to represent aligned memory
          triton::SharedSymbolicExpression aligned_se = nullptr;
          if(auto* RN = dynamic_cast<triton::ast::ReferenceNode*>(node.get()))
            // FIXME: WARNING Here ast need ownership of symExpr
            aligned_se = this->getSymbolicExpressionFromId(RN->getId());
          // FIXME: Should we add SymbolicExpression to inst?
          else {
            aligned_se = this->newSymbolicExpression(node, triton::engines::symbolic::MEM, "Aligned Byte reference - " + comment);
            inst.addSymbolicExpression(aligned_se);
          }
          this->addAlignedMemory(address, writeSize, aligned_se);
        }

        /*
         * As the x86's memory can be accessed without alignment, each byte of the
         * memory must be assigned to an unique reference.
         */
        while (writeSize) {
          /* Extract each byte of the memory */
          auto tmp = this->astCtxt.extract(((writeSize * BYTE_SIZE_BIT) - 1), ((writeSize * BYTE_SIZE_BIT) - BYTE_SIZE_BIT), node);
          auto se = this->newSymbolicExpression(tmp, triton::engines::symbolic::MEM, "Byte reference - " + comment);
          se->setOriginMemory(triton::arch::MemoryAccess(((address + writeSize) - 1), BYTE_SIZE));
          ret.push_back(tmp);
          inst.addSymbolicExpression(se);
          /* Assign memory with little endian */
          this->addMemoryReference((address + writeSize) - 1, se);
          /* continue */
          writeSize--;
          if(ret.size() == 1 && writeSize == 0) {
            /* If there is only one reference, we return the symbolic expression */
            /* Synchronize the concrete state */
            this->architecture->setConcreteMemoryValue(mem, ret.back()->evaluate());
            /* Define the memory store */
            auto const& se_ref = inst.setStoreAccess(mem, se);
            return se_ref;
          }
        }

        /* Otherwise, we return the concatenation of all symbolic expressions */
        auto tmp = this->astCtxt.concat(ret);

        /* Synchronize the concrete state */
        this->architecture->setConcreteMemoryValue(mem, tmp->evaluate());

        auto se  = this->newSymbolicExpression(tmp, triton::engines::symbolic::MEM, "Temporary concatenation reference - " + comment);
        se->setOriginMemory(triton::arch::MemoryAccess(address, mem.getSize()));

        /* Define the memory store */
        auto const& se_ref = inst.setStoreAccess(mem, se);
        inst.addSymbolicExpression(se_ref);
        // FIXME: SHould we return a ref from here?
        return se_ref;
      }


      /* Returns the new symbolic register expression */
      triton::SharedSymbolicExpression const& SymbolicEngine::createSymbolicRegisterExpression(triton::arch::Instruction& inst, triton::ast::SharedAbstractNode const& node, const triton::arch::Register& reg, const std::string& comment) {
        const triton::arch::Register& parentReg   = this->architecture->getParentRegister(reg);
        triton::ast::SharedAbstractNode finalExpr = nullptr;
        triton::ast::SharedAbstractNode origRegNode = nullptr;
        triton::uint32 regSize                    = reg.getSize();

        if (this->architecture->isFlag(reg))
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::createSymbolicRegisterExpression(): The register cannot be a flag.");

        if (regSize == BYTE_SIZE || regSize == WORD_SIZE)
          origRegNode = this->getAstRegister(parentReg);

        switch (regSize) {
          case BYTE_SIZE:
            if (reg.getLow() == 0) {
              finalExpr = this->astCtxt.concat(this->astCtxt.extract((this->architecture->registerBitSize() - 1), BYTE_SIZE_BIT, origRegNode), node);
            }
            else {
              finalExpr = this->astCtxt.concat(this->astCtxt.extract((this->architecture->registerBitSize() - 1), WORD_SIZE_BIT, origRegNode),
                            this->astCtxt.concat(node, this->astCtxt.extract((BYTE_SIZE_BIT - 1), 0, origRegNode))
                          );
            }
            break;

          case WORD_SIZE:
            finalExpr = this->astCtxt.concat(this->astCtxt.extract((this->architecture->registerBitSize() - 1), WORD_SIZE_BIT, origRegNode), node);
            break;

          case DWORD_SIZE:
          case QWORD_SIZE:
          case DQWORD_SIZE:
          case QQWORD_SIZE:
          case DQQWORD_SIZE:
            finalExpr = this->astCtxt.zx(parentReg.getBitSize() - node->getBitvectorSize(), node);
            break;
        }

        triton::SharedSymbolicExpression se = this->newSymbolicExpression(finalExpr, triton::engines::symbolic::REG, "Parent Reg - " + comment);
        auto const& se_ref = this->assignSymbolicExpressionToRegister(se, parentReg);
        inst.addSymbolicExpression(se_ref);

        triton::SharedSymbolicExpression reg_se = this->newSymbolicExpression(node, triton::engines::symbolic::REG, "Real Reg - " + comment);
        inst.setWrittenRegister(reg, reg_se);
        inst.addSymbolicExpression(reg_se);

        return se_ref;
      }


      /* Returns the new symbolic flag expression */
      triton::SharedSymbolicExpression const& SymbolicEngine::createSymbolicFlagExpression(triton::arch::Instruction& inst, triton::ast::SharedAbstractNode const& node, const triton::arch::Register& flag, const std::string& comment) {
        if (!this->architecture->isFlag(flag))
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::createSymbolicFlagExpression(): The register must be a flag.");

        triton::SharedSymbolicExpression se = this->newSymbolicExpression(node, triton::engines::symbolic::REG, comment);
        auto const& se_ref = this->assignSymbolicExpressionToRegister(se, flag);
        inst.addSymbolicExpression(se_ref);
        inst.setWrittenRegister(flag, se_ref);

        return se_ref;
      }


      /* Returns the new symbolic volatile expression */
      triton::SharedSymbolicExpression const& SymbolicEngine::createSymbolicVolatileExpression(triton::arch::Instruction& inst, triton::ast::SharedAbstractNode const& node, const std::string& comment) {
        triton::SharedSymbolicExpression se = this->newSymbolicExpression(node, triton::engines::symbolic::UNDEF, comment);
        auto const& se_ref = inst.addSymbolicExpression(se);
        return se_ref;
      }


      /* Adds and assign a new memory reference */
      void SymbolicEngine::addMemoryReference(triton::uint64 mem, triton::SharedSymbolicExpression const& expr) {
        this->memoryReference[mem] = expr;
      }


      /* Assigns a symbolic expression to a register */
      triton::SharedSymbolicExpression const& SymbolicEngine::assignSymbolicExpressionToRegister(triton::SharedSymbolicExpression const& se, const triton::arch::Register& reg) {
        triton::ast::AbstractNode* node = se->getAst();
        triton::uint32 id               = reg.getParent();

        /* We can assign an expression only on parent registers */
        if (reg.getId() != id)
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::assignSymbolicExpressionToRegister(): We can assign an expression only on parent registers.");

        /* Check if the size of the symbolic expression is equal to the target register */
        if (node->getBitvectorSize() != reg.getBitSize()) {
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::assignSymbolicExpressionToRegister(): The size of the symbolic expression is not equal to the target register.");
        }

        se->setKind(triton::engines::symbolic::REG);
        se->setOriginRegister(reg);
        auto const& se_ref = this->symbolicReg[id] = se;

        /* Synchronize the concrete state */
        this->architecture->setConcreteRegisterValue(reg, node->evaluate());
        return se_ref;
      }


      /* Assigns a symbolic expression to a memory */
      void SymbolicEngine::assignSymbolicExpressionToMemory(triton::SharedSymbolicExpression const& se, const triton::arch::MemoryAccess& mem) {
        auto& node                = se->getShareAst();
        triton::uint64 address   = mem.getAddress();
        triton::uint32 writeSize = mem.getSize();

        /* Check if the size of the symbolic expression is equal to the memory access */
        if (node->getBitvectorSize() != mem.getBitSize())
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::assignSymbolicExpressionToMemory(): The size of the symbolic expression is not equal to the memory access.");

        /* Record the aligned memory for a symbolic optimization */
        if (this->modes.isModeEnabled(triton::modes::ALIGNED_MEMORY))
          this->addAlignedMemory(address, writeSize, se);

        /*
         * As the x86's memory can be accessed without alignment, each byte of the
         * memory must be assigned to an unique reference.
         */
        while (writeSize) {
          /* Extract each byte of the memory */
          auto tmp = this->astCtxt.extract(((writeSize * BYTE_SIZE_BIT) - 1), ((writeSize * BYTE_SIZE_BIT) - BYTE_SIZE_BIT), node);
          triton::SharedSymbolicExpression byteRef = this->newSymbolicExpression(tmp, triton::engines::symbolic::MEM, "Byte reference");
          byteRef->setOriginMemory(triton::arch::MemoryAccess(((address + writeSize) - 1), BYTE_SIZE));
          /* Assign memory with little endian */
          this->addMemoryReference((address + writeSize) - 1, byteRef);
          writeSize--;
        }
      }


      /* Returns true if the symbolic engine is enable */
      bool SymbolicEngine::isEnabled(void) const {
        return this->enableFlag;
      }


      /* Returns true if the symbolic expression ID exists */
      bool SymbolicEngine::isSymbolicExpressionIdExists(triton::usize symExprId) const {
        auto it = this->symbolicExpressions.find(symExprId);
        if (it != this->symbolicExpressions.end())
          return it->second.use_count() > 0;
        return false;
      }


      /* Returns true if memory cell expressions contain symbolic variables. */
      bool SymbolicEngine::isMemorySymbolized(const triton::arch::MemoryAccess& mem) const {
        triton::uint64 addr = mem.getAddress();
        triton::uint32 size = mem.getSize();

        return this->isMemorySymbolized(addr, size);
      }


      /* Returns true if memory cell expressions contain symbolic variables. */
      bool SymbolicEngine::isMemorySymbolized(triton::uint64 addr, triton::uint32 size) const {
        for (triton::uint32 i = 0; i < size; i++) {
          auto symExp = this->getSymbolicMemory(addr + i);
          if(symExp == nullptr)
            continue;

          if (symExp->isSymbolized())
            return true;
        }

        return false;
      }


      /* Returns true if the register expression contains a symbolic variable. */
      bool SymbolicEngine::isRegisterSymbolized(const triton::arch::Register& reg) const {
        auto const& symExp = this->getSymbolicRegister(reg);
        if(symExp == nullptr)
          return false;
        return symExp->isSymbolized();
      }


      /* Enables or disables the symbolic engine */
      void SymbolicEngine::enable(bool flag) {
        this->enableFlag = flag;
      }


      /* Initializes the memory access AST (LOAD and STORE) */
      void SymbolicEngine::initLeaAst(triton::arch::MemoryAccess& mem, bool force) {
        if (mem.getBitSize() >= BYTE_SIZE_BIT) {
          const triton::arch::Register& base  = mem.getConstBaseRegister();
          const triton::arch::Register& index = mem.getConstIndexRegister();
          const triton::arch::Register& seg   = mem.getConstSegmentRegister();
          triton::uint64 segmentValue         = (this->architecture->isRegisterValid(seg) ? this->architecture->getConcreteRegisterValue(seg).convert_to<triton::uint64>() : 0);
          triton::uint64 scaleValue           = mem.getConstScale().getValue();
          triton::uint64 dispValue            = mem.getConstDisplacement().getValue();
          triton::uint32 bitSize              = (this->architecture->isRegisterValid(index) ? index.getBitSize() :
                                                  (this->architecture->isRegisterValid(base) ? base.getBitSize() :
                                                    (mem.getConstDisplacement().getBitSize() ? mem.getConstDisplacement().getBitSize() :
                                                      this->architecture->registerBitSize()
                                                    )
                                                  )
                                                );


          /* Initialize the AST of the memory access (LEA) -> ((pc + base) + (index * scale) + disp) */
          triton::ast::SharedAbstractNode pc_base_ast = nullptr;
          if(auto pc = mem.getPcRelative()) {
            pc_base_ast = this->astCtxt.bv(pc, bitSize);
          } else if(this->architecture->isRegisterValid(base)) {
            pc_base_ast = this->getAstRegister(base);
          } else {
            pc_base_ast = this->astCtxt.bv(0, bitSize);
          }

          triton::ast::SharedAbstractNode index_ast = nullptr;
          if(this->architecture->isRegisterValid(index)) {
            index_ast = this->getAstRegister(index);
          } else {
            index_ast = this->astCtxt.bv(0, bitSize);
          }

          auto leaAst = this->astCtxt.bvadd(pc_base_ast,
                          this->astCtxt.bvadd(
                            this->astCtxt.bvmul(
                              index_ast,
                              this->astCtxt.bv(scaleValue, bitSize)
                            ),
                            this->astCtxt.bv(dispValue, bitSize)
                          )
                        );

          /* Use segments as base address instead of selector into the GDT. */
          if (segmentValue) {
            leaAst = this->astCtxt.bvadd(
                       this->astCtxt.bv(segmentValue, seg.getBitSize()),
                       this->astCtxt.sx((seg.getBitSize() - bitSize), leaAst)
                     );
          }

          /* Set AST */
          mem.setLeaAst(leaAst);

          /* Initialize the address only if it is not already defined */
          if (!mem.getAddress() || force)
            mem.setAddress(leaAst->evaluate().convert_to<triton::uint64>());
        }
      }


      const triton::uint512& SymbolicEngine::getConcreteSymbolicVariableValue(const SymbolicVariable& symVar) const {
        return this->astCtxt.getValueForVariable(symVar.getName());
      }


      void SymbolicEngine::setConcreteSymbolicVariableValue(const SymbolicVariable& symVar, const triton::uint512& value) {
        this->astCtxt.updateVariable(symVar.getName(), value);
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */

