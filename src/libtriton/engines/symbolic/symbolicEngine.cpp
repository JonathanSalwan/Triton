//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstring>
#include <new>

#include <triton/exceptions.hpp>
#include <triton/coreUtils.hpp>
#include <triton/symbolicEngine.hpp>
#include <triton/astContext.hpp>



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
 init | eax = UNSET             | None        | \f$ \bot \f$
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
                                     triton::ast::AstContext& astCtxt,
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
        this->callbacks         = callbacks;
        this->backupFlag        = isBackup;
        this->enableFlag        = true;
        this->uniqueSymExprId   = 0;
        this->uniqueSymVarId    = 0;

        this->symbolicReg.resize(this->numberOfRegisters);
      }


      void SymbolicEngine::copy(const SymbolicEngine& other) {
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
        this->numberOfRegisters           = other.numberOfRegisters;
        this->symbolicExpressions         = other.symbolicExpressions;
        this->symbolicReg                 = other.symbolicReg;
        this->symbolicVariables           = other.symbolicVariables;
        this->uniqueSymExprId             = other.uniqueSymExprId;
        this->uniqueSymVarId              = other.uniqueSymVarId;
      }


      SymbolicEngine::SymbolicEngine(const SymbolicEngine& other)
        : triton::engines::symbolic::SymbolicSimplification(other),
          triton::engines::symbolic::PathManager(other),
          astCtxt(other.astCtxt),
          modes(other.modes) {
        this->copy(other);
      }


      SymbolicEngine& SymbolicEngine::operator=(const SymbolicEngine& other) {
        triton::engines::symbolic::SymbolicSimplification::operator=(other);
        triton::engines::symbolic::PathManager::operator=(other);

        /* Delete unused variables */
        for (auto& sv : this->symbolicVariables) {
          if (other.symbolicVariables.find(sv.first) == other.symbolicVariables.end())
            delete this->symbolicVariables[sv.first];
        }

        // We assume astCtxt didn't change
        // We assume modes didn't change
        this->copy(other);

        return *this;
      }


      SymbolicEngine::~SymbolicEngine() {
        /*
         * Don't delete symbolic variables if this class is used as
         * backup engine. Otherwise that may result in a double-free
         * bug if the original symbolic engine is deleted too (cf: #385).
         */
        if (this->backupFlag == false) {
          /* Delete all symbolic variables */
          for (auto sv : this->symbolicVariables)
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
      const SharedSymbolicExpression& SymbolicEngine::getAlignedMemory(triton::uint64 address, triton::uint32 size) {
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
      void SymbolicEngine::addAlignedMemory(triton::uint64 address, triton::uint32 size, const SharedSymbolicExpression& expr) {
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


      /* Returns the reference memory if it's referenced otherwise returns nullptr */
      SharedSymbolicExpression SymbolicEngine::getSymbolicMemory(triton::uint64 addr) const {
        auto it = this->memoryReference.find(addr);
        if (it != this->memoryReference.end())
          return it->second;
        return nullptr;
      }


      /* Returns the symbolic variable otherwise raises an exception */
      SymbolicVariable* SymbolicEngine::getSymbolicVariableFromId(triton::usize symVarId) const {
        auto it = this->symbolicVariables.find(symVarId);
        if (it == this->symbolicVariables.end())
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::getSymbolicVariableFromId(): Unregistred variable.");
        return it->second;
      }


      /* Returns the symbolic variable otherwise returns nullptr */
      SymbolicVariable* SymbolicEngine::getSymbolicVariableFromName(const std::string& symVarName) const {
        /*
         * FIXME: When there is a ton of symvar, this loop takes a while to go through.
         *        What about adding two maps {id:symvar} and {string:symvar}? See #648.
         */
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


      /* Returns the shared symbolic expression corresponding to the register */
      const SharedSymbolicExpression& SymbolicEngine::getSymbolicRegister(const triton::arch::Register& reg) const {
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
        const triton::ast::SharedAbstractNode& node = this->buildSymbolicMemory(mem);
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
        return this->getRegisterAst(reg)->evaluate();
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
      SharedSymbolicExpression SymbolicEngine::newSymbolicExpression(const triton::ast::SharedAbstractNode& node, triton::engines::symbolic::symkind_e kind, const std::string& comment) {
        /* Each symbolic expression must have an unique id */
        triton::usize id = this->getUniqueSymExprId();

        /* Performes transformation if there are rules recorded */
        const triton::ast::SharedAbstractNode& snode = this->processSimplification(node);

        /* Allocates the new shared symbolic expression */
        SharedSymbolicExpression expr = std::make_shared<SymbolicExpression>(snode, id, kind, comment);
        if (expr == nullptr)
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::newSymbolicExpression(): not enough memory");

        /* Save and returns the new shared symbolic expression */
        this->symbolicExpressions[id] = expr;
        return expr;
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


      /* Gets the shared symbolic expression from a symbolic id */
      SharedSymbolicExpression SymbolicEngine::getSymbolicExpressionFromId(triton::usize symExprId) const {
        auto it = this->symbolicExpressions.find(symExprId);
        if (it == this->symbolicExpressions.end())
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::getSymbolicExpressionFromId(): symbolic expression id not found");

        if (auto sp = it->second.lock())
          return sp;

        this->symbolicExpressions.erase(symExprId);
        throw triton::exceptions::SymbolicEngine("SymbolicEngine::getSymbolicExpressionFromId(): symbolic expression is not available anymore");
      }


      /* Returns all symbolic expressions */
      std::unordered_map<triton::usize, SharedSymbolicExpression> SymbolicEngine::getSymbolicExpressions(void) const {
        // Copy and clean up dead weak ref
        std::unordered_map<triton::usize, SharedSymbolicExpression> ret;
        std::vector<triton::usize> toRemove;

        for (auto& kv : this->symbolicExpressions) {
          if (auto sp = kv.second.lock()) {
            ret[kv.first] = sp;
          } else {
            toRemove.push_back(kv.first);
          }
        }

        for (auto id : toRemove)
          this->symbolicExpressions.erase(id);

        return ret;
      }


      /* Returns the full symbolic expression backtracked. */
      triton::ast::SharedAbstractNode SymbolicEngine::unrollAst(const triton::ast::SharedAbstractNode& node) {
        std::vector<triton::ast::SharedAbstractNode>& children = node->getChildren();

        if (node->getKind() == triton::ast::REFERENCE_NODE) {
          const SharedSymbolicExpression& expr = reinterpret_cast<triton::ast::ReferenceNode*>(node.get())->getSymbolicExpression();
          const triton::ast::SharedAbstractNode& ref = expr->getAst();
          return this->unrollAst(ref);
        }

        for (triton::uint32 index = 0; index < children.size(); index++)
          children[index] = this->unrollAst(children[index]);

        return node;
      }


      /* [private method] Slices all expressions from a given node */
      void SymbolicEngine::sliceExpressions(const triton::ast::SharedAbstractNode& node, std::map<triton::usize, SharedSymbolicExpression>& exprs) {
        std::vector<triton::ast::SharedAbstractNode>& children = node->getChildren();

        if (node->getKind() == triton::ast::REFERENCE_NODE) {
          const SharedSymbolicExpression& expr = reinterpret_cast<triton::ast::ReferenceNode*>(node.get())->getSymbolicExpression();
          triton::usize id = expr->getId();
          if (exprs.find(id) == exprs.end()) {
            exprs[id] = expr;
            this->sliceExpressions(expr->getAst(), exprs);
          }
        }

        for (triton::uint32 index = 0; index < children.size(); index++) {
          this->sliceExpressions(children[index], exprs);
        }
      }


      /* Slices all expressions from a given one */
      std::map<triton::usize, SharedSymbolicExpression> SymbolicEngine::sliceExpressions(const SharedSymbolicExpression& expr) {
        std::map<triton::usize, SharedSymbolicExpression> exprs;

        if (expr == nullptr)
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::sliceExpressions(): expr cannot be null.");

        exprs[expr->getId()] = expr;
        this->sliceExpressions(expr->getAst(), exprs);

        return exprs;
      }


      /* Returns a list which contains all tainted expressions */
      std::list<SharedSymbolicExpression> SymbolicEngine::getTaintedSymbolicExpressions(void) const {
        std::list<SharedSymbolicExpression> taintedExprs;
        std::vector<triton::usize> invalidSymExpr;

        for (auto it = this->symbolicExpressions.begin(); it != this->symbolicExpressions.end(); it++) {
          if (auto sp = it->second.lock()) {
            if (sp->isTainted) {
              taintedExprs.push_back(sp);
            }
          } else {
            invalidSymExpr.push_back(it->first);
          }
        }

        for (auto id : invalidSymExpr)
          this->symbolicExpressions.erase(id);

        return taintedExprs;
      }


      /* Returns the map of symbolic registers defined */
      std::map<triton::arch::registers_e, SharedSymbolicExpression> SymbolicEngine::getSymbolicRegisters(void) const {
        std::map<triton::arch::registers_e, SharedSymbolicExpression> ret;

        for (triton::uint32 it = 0; it < this->numberOfRegisters; it++) {
          if (this->symbolicReg[it] != nullptr) {
            ret[arch::registers_e(it)] = this->symbolicReg[it];
          }
        }

        return ret;
      }


      /* Returns the map of symbolic memory defined */
      const std::map<triton::uint64, SharedSymbolicExpression>& SymbolicEngine::getSymbolicMemory(void) const {
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
        const SharedSymbolicExpression& expression = this->getSymbolicExpressionFromId(exprId);
        SymbolicVariable* symVar                   = this->newSymbolicVariable(triton::engines::symbolic::UNDEF, 0, symVarSize, symVarComment);
        const triton::ast::SharedAbstractNode& tmp = this->astCtxt.variable(*symVar);

        if (expression->getAst())
           this->setConcreteSymbolicVariableValue(*symVar, expression->getAst()->evaluate());

        expression->setAst(tmp);

        return symVar;
      }


      /* The memory size is used to define the symbolic variable's size. */
      SymbolicVariable* SymbolicEngine::convertMemoryToSymbolicVariable(const triton::arch::MemoryAccess& mem, const std::string& symVarComment) {
        triton::uint64 memAddr          = mem.getAddress();
        triton::uint32 symVarSize       = mem.getSize();
        triton::uint512 cv              = this->architecture->getConcreteMemoryValue(mem);

        /* First we create a symbolic variable */
        SymbolicVariable* symVar = this->newSymbolicVariable(triton::engines::symbolic::MEM, memAddr, symVarSize * BYTE_SIZE_BIT, symVarComment);

        /* Create the AST node */
        const triton::ast::SharedAbstractNode& symVarNode = this->astCtxt.variable(*symVar);

        /* Setup the concrete value to the symbolic variable */
        this->setConcreteSymbolicVariableValue(*symVar, cv);

        /* Record the aligned symbolic variable for a symbolic optimization */
        if (this->modes.isModeEnabled(triton::modes::ALIGNED_MEMORY)) {
          const SharedSymbolicExpression& se = this->newSymbolicExpression(symVarNode, triton::engines::symbolic::MEM, "aligned Byte reference");
          this->addAlignedMemory(memAddr, symVarSize, se);
        }

        /*  Split expression in bytes */
        for (triton::sint32 index = symVarSize-1; index >= 0; index--) {
          /* Isolate the good part of the symbolic variable */
          const triton::ast::SharedAbstractNode& tmp = this->astCtxt.extract(((BYTE_SIZE_BIT * (index+1)) - 1), ((BYTE_SIZE_BIT * (index+1)) - BYTE_SIZE_BIT), symVarNode);

          /* Check if the memory address is already defined */
          SharedSymbolicExpression se = this->getSymbolicMemory(memAddr+index);
          if (se == nullptr) {
            se = this->newSymbolicExpression(tmp, triton::engines::symbolic::MEM, "Byte reference");
            /* Add the new memory reference */
            this->addMemoryReference(memAddr+index, se);
          }
          else {
            // FIXME: Here we update the ast but the memory Reference may
            // be use in another ast which then become invalid. Should we
            // create a new SE everytime?
            se->setAst(tmp);
          }
          /* Defines the origin of the expression */
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
        const SharedSymbolicExpression& expression = this->getSymbolicRegister(reg);

        /* Create the symbolic variable */
        SymbolicVariable* symVar = this->newSymbolicVariable(triton::engines::symbolic::REG, parent.getId(), symVarSize, symVarComment);

        /* Create the AST node */
        const triton::ast::SharedAbstractNode& tmp = this->astCtxt.zx(parent.getBitSize() - symVarSize, this->astCtxt.variable(*symVar));

        /* Setup the concrete value to the symbolic variable */
        this->setConcreteSymbolicVariableValue(*symVar, cv);

        if (expression == nullptr) {
          /* Create the symbolic expression */
          const SharedSymbolicExpression& se = this->newSymbolicExpression(tmp, triton::engines::symbolic::REG);
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
        SymbolicVariable* symVar = new(std::nothrow) SymbolicVariable(kind, kindValue, uniqueId, size, comment);

        if (symVar == nullptr)
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::newSymbolicVariable(): Cannot allocate a new symbolic variable");

        this->symbolicVariables[uniqueId] = symVar;
        return symVar;
      }


      /* Returns the AST corresponding to the operand. */
      triton::ast::SharedAbstractNode SymbolicEngine::getOperandAst(const triton::arch::OperandWrapper& op) {
        switch (op.getType()) {
          case triton::arch::OP_IMM: return this->getImmediateAst(op.getConstImmediate());
          case triton::arch::OP_MEM: return this->buildSymbolicMemory(op.getConstMemory());
          case triton::arch::OP_REG: return this->getRegisterAst(op.getConstRegister());
          default:
            throw triton::exceptions::SymbolicEngine("SymbolicEngine::getOperandAst(): Invalid operand.");
        }
      }


      /* Returns the AST corresponding to the operand. */
      triton::ast::SharedAbstractNode SymbolicEngine::getOperandAst(triton::arch::Instruction& inst, const triton::arch::OperandWrapper& op) {
        switch (op.getType()) {
          case triton::arch::OP_IMM: return this->getImmediateAst(inst, op.getConstImmediate());
          case triton::arch::OP_MEM: return this->buildSymbolicMemory(inst, op.getConstMemory());
          case triton::arch::OP_REG: return this->getRegisterAst(inst, op.getConstRegister());
          default:
            throw triton::exceptions::SymbolicEngine("SymbolicEngine::getOperandAst(): Invalid operand.");
        }
      }


      /* Returns the AST corresponding to the immediate */
      triton::ast::SharedAbstractNode SymbolicEngine::getImmediateAst(const triton::arch::Immediate& imm) {
        triton::ast::SharedAbstractNode node = this->astCtxt.bv(imm.getValue(), imm.getBitSize());
        return node;
      }


      /* Returns the AST corresponding to the immediate and defines the immediate as input of the instruction */
      triton::ast::SharedAbstractNode SymbolicEngine::getImmediateAst(triton::arch::Instruction& inst, const triton::arch::Immediate& imm) {
        triton::ast::SharedAbstractNode node = this->getImmediateAst(imm);
        inst.setReadImmediate(imm, node);
        return node;
      }


      /* Returns the AST corresponding to the memory */
      triton::ast::SharedAbstractNode SymbolicEngine::buildSymbolicMemory(const triton::arch::MemoryAccess& mem) {
        std::list<triton::ast::SharedAbstractNode> opVec;

        triton::ast::SharedAbstractNode tmp       = nullptr;
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
          return this->getAlignedMemory(address, size)->getAst();

        /* Iterate on every memory cells to use their symbolic or concrete values */
        while (size) {
          const SharedSymbolicExpression& symMem = this->getSymbolicMemory(address + size - 1);
          /* Check if the memory cell is already symbolic */
          if (symMem != nullptr) {
            tmp = this->astCtxt.reference(symMem);
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


      /* Returns the AST corresponding to the memory and defines the memory as input of the instruction */
      triton::ast::SharedAbstractNode SymbolicEngine::buildSymbolicMemory(triton::arch::Instruction& inst, const triton::arch::MemoryAccess& mem) {
        triton::ast::SharedAbstractNode node = this->buildSymbolicMemory(mem);

        /* Set load access */
        inst.setLoadAccess(mem, node);

        /* Set implicit read of the base register (LEA) */
        if (this->architecture->isRegisterValid(mem.getConstBaseRegister()))
          this->getRegisterAst(inst, mem.getConstBaseRegister());

        /* Set implicit read of the index register (LEA) */
        if (this->architecture->isRegisterValid(mem.getConstIndexRegister()))
          this->getRegisterAst(inst, mem.getConstIndexRegister());

        return node;
      }


      /* Returns the AST corresponding to the register */
      triton::ast::SharedAbstractNode SymbolicEngine::getRegisterAst(const triton::arch::Register& reg) {
        triton::ast::SharedAbstractNode op = nullptr;
        triton::uint32 bvSize              = reg.getBitSize();
        triton::uint32 high                = reg.getHigh();
        triton::uint32 low                 = reg.getLow();

        /* Check if the register is already symbolic */
        if (const SharedSymbolicExpression& symReg = this->getSymbolicRegister(reg)) {
          op = this->astCtxt.extract(high, low, this->astCtxt.reference(symReg));
        }
        /* Otherwise, use the concerte value */
        else {
          op = this->astCtxt.bv(this->architecture->getConcreteRegisterValue(reg), bvSize);
        }

        return op;
      }


      /* Returns the AST corresponding to the register and defines the register as input of the instruction */
      triton::ast::SharedAbstractNode SymbolicEngine::getRegisterAst(triton::arch::Instruction& inst, const triton::arch::Register& reg) {
        triton::ast::SharedAbstractNode node = this->getRegisterAst(reg);
        inst.setReadRegister(reg, node);
        return node;
      }


      /* Returns the new symbolic abstract expression and links this expression to the instruction. */
      const SharedSymbolicExpression& SymbolicEngine::createSymbolicExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const triton::arch::OperandWrapper& dst, const std::string& comment) {
        switch (dst.getType()) {
          case triton::arch::OP_MEM: return this->createSymbolicMemoryExpression(inst, node, dst.getConstMemory(), comment);
          case triton::arch::OP_REG: return this->createSymbolicRegisterExpression(inst, node, dst.getConstRegister(), comment);
          default:
            throw triton::exceptions::SymbolicEngine("SymbolicEngine::createSymbolicExpression(): Invalid operand.");
        }
      }


      /* Returns the new symbolic memory expression */
      const SharedSymbolicExpression& SymbolicEngine::createSymbolicMemoryExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const triton::arch::MemoryAccess& mem, const std::string& comment) {
        std::list<triton::ast::SharedAbstractNode> ret;
        triton::ast::SharedAbstractNode tmp = nullptr;
        SharedSymbolicExpression se         = nullptr;
        triton::uint64 address              = mem.getAddress();
        triton::uint32 writeSize            = mem.getSize();

        /* Record the aligned memory for a symbolic optimization */
        if (this->modes.isModeEnabled(triton::modes::ALIGNED_MEMORY)) {
          const SharedSymbolicExpression& aligned = this->newSymbolicExpression(node, triton::engines::symbolic::MEM, "Aligned Byte reference - " + comment);
          this->addAlignedMemory(address, writeSize, aligned);
        }

        /*
         * As the x86's memory can be accessed without alignment, each byte of the
         * memory must be assigned to an unique reference.
         */
        while (writeSize) {
          /* Extract each byte of the memory */
          tmp = this->astCtxt.extract(((writeSize * BYTE_SIZE_BIT) - 1), ((writeSize * BYTE_SIZE_BIT) - BYTE_SIZE_BIT), node);
          se = this->newSymbolicExpression(tmp, triton::engines::symbolic::MEM, "Byte reference - " + comment);
          se->setOriginMemory(triton::arch::MemoryAccess(((address + writeSize) - 1), BYTE_SIZE));
          ret.push_back(tmp);
          inst.addSymbolicExpression(se);
          /* Assign memory with little endian */
          this->addMemoryReference((address + writeSize) - 1, se);
          /* continue */
          writeSize--;
        }

        /* If there is only one reference, we return the symbolic expression */
        if (ret.size() == 1) {
          /* Synchronize the concrete state */
          this->architecture->setConcreteMemoryValue(mem, tmp->evaluate());
          /* Define the memory store */
          inst.setStoreAccess(mem, node);
          /* It will return se */
          return inst.symbolicExpressions.back();
        }

        /* Otherwise, we return the concatenation of all symbolic expressions */
        tmp = this->astCtxt.concat(ret);

        /* Synchronize the concrete state */
        this->architecture->setConcreteMemoryValue(mem, tmp->evaluate());

        se = this->newSymbolicExpression(tmp, triton::engines::symbolic::MEM, "Temporary concatenation reference - " + comment);
        se->setOriginMemory(triton::arch::MemoryAccess(address, mem.getSize()));

        /* Define the memory store */
        inst.setStoreAccess(mem, node);
        return inst.addSymbolicExpression(se);
      }


      /* Returns the new symbolic register expression */
      const SharedSymbolicExpression& SymbolicEngine::createSymbolicRegisterExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const triton::arch::Register& reg, const std::string& comment) {
        const triton::arch::Register& parentReg   = this->architecture->getParentRegister(reg);
        triton::ast::SharedAbstractNode finalExpr = nullptr;
        triton::ast::SharedAbstractNode origReg   = nullptr;
        triton::uint32 regSize                    = reg.getSize();

        if (this->architecture->isFlag(reg))
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::createSymbolicRegisterExpression(): The register cannot be a flag.");

        if (regSize == BYTE_SIZE || regSize == WORD_SIZE)
          origReg = this->getRegisterAst(parentReg);

        switch (regSize) {
          case BYTE_SIZE:
            if (reg.getLow() == 0) {
              finalExpr = this->astCtxt.concat(this->astCtxt.extract((this->architecture->registerBitSize() - 1), BYTE_SIZE_BIT, origReg), node);
            }
            else {
              finalExpr = this->astCtxt.concat(this->astCtxt.extract((this->architecture->registerBitSize() - 1), WORD_SIZE_BIT, origReg),
                            this->astCtxt.concat(node, this->astCtxt.extract((BYTE_SIZE_BIT - 1), 0, origReg))
                          );
            }
            break;

          case WORD_SIZE:
            finalExpr = this->astCtxt.concat(this->astCtxt.extract((this->architecture->registerBitSize() - 1), WORD_SIZE_BIT, origReg), node);
            break;

          case DWORD_SIZE:
          case QWORD_SIZE:
          case DQWORD_SIZE:
          case QQWORD_SIZE:
          case DQQWORD_SIZE:
            finalExpr = this->astCtxt.zx(parentReg.getBitSize() - node->getBitvectorSize(), node);
            break;
        }

        const SharedSymbolicExpression& se = this->newSymbolicExpression(finalExpr, triton::engines::symbolic::REG, comment);
        this->assignSymbolicExpressionToRegister(se, parentReg);
        inst.setWrittenRegister(reg, node);
        return inst.addSymbolicExpression(se);
      }


      /* Returns the new symbolic flag expression */
      const SharedSymbolicExpression& SymbolicEngine::createSymbolicFlagExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const triton::arch::Register& flag, const std::string& comment) {
        if (!this->architecture->isFlag(flag))
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::createSymbolicFlagExpression(): The register must be a flag.");

        const SharedSymbolicExpression& se = this->newSymbolicExpression(node, triton::engines::symbolic::REG, comment);
        this->assignSymbolicExpressionToRegister(se, flag);
        inst.setWrittenRegister(flag, node);
        return inst.addSymbolicExpression(se);
      }


      /* Returns the new symbolic volatile expression */
      const SharedSymbolicExpression& SymbolicEngine::createSymbolicVolatileExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const std::string& comment) {
        const SharedSymbolicExpression& se = this->newSymbolicExpression(node, triton::engines::symbolic::UNDEF, comment);
        return inst.addSymbolicExpression(se);
      }


      /* Adds and assign a new memory reference */
      void SymbolicEngine::addMemoryReference(triton::uint64 mem, const SharedSymbolicExpression& expr) {
        this->memoryReference[mem] = expr;
      }


      /* Assigns a symbolic expression to a register */
      void SymbolicEngine::assignSymbolicExpressionToRegister(const SharedSymbolicExpression& se, const triton::arch::Register& reg) {
        const triton::ast::SharedAbstractNode& node = se->getAst();
        triton::uint32 id                           = reg.getParent();

        /* We can assign an expression only on parent registers */
        if (reg.getId() != id)
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::assignSymbolicExpressionToRegister(): We can assign an expression only on parent registers.");

        /* Check if the size of the symbolic expression is equal to the target register */
        if (node->getBitvectorSize() != reg.getBitSize()) {
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::assignSymbolicExpressionToRegister(): The size of the symbolic expression is not equal to the target register.");
        }

        se->setKind(triton::engines::symbolic::REG);
        se->setOriginRegister(reg);
        this->symbolicReg[id] = se;

        /* Synchronize the concrete state */
        this->architecture->setConcreteRegisterValue(reg, node->evaluate());
      }


      /* Assigns a symbolic expression to a memory */
      void SymbolicEngine::assignSymbolicExpressionToMemory(const SharedSymbolicExpression& se, const triton::arch::MemoryAccess& mem) {
        const triton::ast::SharedAbstractNode& node = se->getAst();
        triton::uint64 address                      = mem.getAddress();
        triton::uint32 writeSize                    = mem.getSize();

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
          const triton::ast::SharedAbstractNode& tmp = this->astCtxt.extract(((writeSize * BYTE_SIZE_BIT) - 1), ((writeSize * BYTE_SIZE_BIT) - BYTE_SIZE_BIT), node);
          const SharedSymbolicExpression& byteRef = this->newSymbolicExpression(tmp, triton::engines::symbolic::MEM, "Byte reference");
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
          return (it->second.use_count() > 0);

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
          const SharedSymbolicExpression& expr = this->getSymbolicMemory(addr + i);

          if(expr == nullptr)
            continue;

          if (expr->isSymbolized())
            return true;
        }

        return false;
      }


      /* Returns true if the register expression contains a symbolic variable. */
      bool SymbolicEngine::isRegisterSymbolized(const triton::arch::Register& reg) const {
        const SharedSymbolicExpression& expr = this->getSymbolicRegister(reg);

        if (expr == nullptr)
          return false;

        return expr->isSymbolized();
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
          auto leaAst = this->astCtxt.bvadd(
                          (mem.getPcRelative() ? this->astCtxt.bv(mem.getPcRelative(), bitSize) :
                            (this->architecture->isRegisterValid(base) ? this->getRegisterAst(base) :
                              this->astCtxt.bv(0, bitSize)
                            )
                          ),
                          this->astCtxt.bvadd(
                            this->astCtxt.bvmul(
                              (this->architecture->isRegisterValid(index) ? this->getRegisterAst(index) : this->astCtxt.bv(0, bitSize)),
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
        return this->astCtxt.getVariableValue(symVar.getName());
      }


      void SymbolicEngine::setConcreteSymbolicVariableValue(const SymbolicVariable& symVar, const triton::uint512& value) {
        this->astCtxt.updateVariable(symVar.getName(), value);
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */

