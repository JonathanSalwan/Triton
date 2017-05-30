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
                                     triton::modes::Modes* modes,
                                     triton::callbacks::Callbacks* callbacks,
                                     bool isBackup)

        : triton::engines::symbolic::SymbolicSimplification(callbacks),
          triton::engines::symbolic::PathManager(modes) {

        if (architecture == nullptr)
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::SymbolicEngine(): The architecture pointer must be valid.");

        if (modes == nullptr)
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::SymbolicEngine(): The modes API cannot be null.");

        this->architecture      = architecture;
        this->numberOfRegisters = this->architecture->numberOfRegisters();
        this->symbolicReg       = new triton::usize[this->numberOfRegisters]();

        /* Init all symbolic registers/flags to UNSET (init state) */
        for (triton::uint32 i = 0; i < this->numberOfRegisters; i++)
          this->symbolicReg[i] = triton::engines::symbolic::UNSET;

        this->callbacks       = callbacks;
        this->backupFlag      = isBackup;
        this->enableFlag      = true;
        this->modes           = modes;
        this->uniqueSymExprId = 0;
        this->uniqueSymVarId  = 0;
      }


      void SymbolicEngine::copy(const SymbolicEngine& other) {
        this->numberOfRegisters = other.numberOfRegisters;
        this->symbolicReg = new triton::usize[this->numberOfRegisters]();

        for (triton::uint32 i = 0; i < this->numberOfRegisters; i++)
          this->symbolicReg[i] = other.symbolicReg[i];

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
        this->modes                       = other.modes;
        this->symbolicExpressions         = other.symbolicExpressions;
        this->symbolicVariables           = other.symbolicVariables;
        this->uniqueSymExprId             = other.uniqueSymExprId;
        this->uniqueSymVarId              = other.uniqueSymVarId;
      }


      SymbolicEngine::SymbolicEngine(const SymbolicEngine& copy)
        : triton::engines::symbolic::SymbolicSimplification(copy),
          triton::engines::symbolic::PathManager(copy) {
        this->copy(copy);
      }


      void SymbolicEngine::operator=(const SymbolicEngine& other) {
        triton::engines::symbolic::SymbolicSimplification::operator=(other);
        triton::engines::symbolic::PathManager::operator=(other);

        /* Delete unused expressions */
        std::map<triton::usize, SymbolicExpression*>::iterator it1;
        for (it1 = this->symbolicExpressions.begin(); it1 != this->symbolicExpressions.end(); it1++) {
          if (other.symbolicExpressions.find(it1->first) == other.symbolicExpressions.end())
            delete this->symbolicExpressions[it1->first];
        }

        /* Delete unused variables */
        std::map<triton::usize, SymbolicVariable*>::iterator it2;
        for (it2 = this->symbolicVariables.begin(); it2 != this->symbolicVariables.end(); it2++) {
          if (other.symbolicVariables.find(it2->first) == other.symbolicVariables.end())
            delete this->symbolicVariables[it2->first];
        }

        delete[] this->symbolicReg;
        this->copy(other);
      }


      SymbolicEngine::~SymbolicEngine() {
        std::map<triton::usize, SymbolicExpression*>::iterator it1 = this->symbolicExpressions.begin();
        std::map<triton::usize, SymbolicVariable*>::iterator it2 = this->symbolicVariables.begin();

        /*
         * Don't delete symbolic expressions and symbolic variables
         * if this class is used as backup engine. Otherwise that may
         * result in a double-free bug if the original symbolic engine
         * is deleted too (cf: #385).
         */
        if (this->backupFlag == false) {
          /* Delete all symbolic expressions */
          for (; it1 != this->symbolicExpressions.end(); ++it1)
            delete it1->second;

          /* Delete all symbolic variables */
          for (; it2 != this->symbolicVariables.end(); ++it2)
            delete it2->second;
        }

        /* Delete all symbolic register */
        delete[] this->symbolicReg;
      }


      /*
       * Concretize a register. If the register is setup as UNSET, the next assignment
       * will be over the concretization. This method must be called before symbolic
       * processing.
       */
      void SymbolicEngine::concretizeRegister(const triton::arch::Register& reg) {
        triton::uint32 parentId = reg.getParent().getId();

        if (!this->architecture->isRegisterValid(parentId))
          return;

        this->symbolicReg[parentId] = triton::engines::symbolic::UNSET;
      }


      /* Same as concretizeRegister but with all registers */
      void SymbolicEngine::concretizeAllRegister(void) {
        for (triton::uint32 i = 0; i < this->numberOfRegisters; i++)
          this->symbolicReg[i] = triton::engines::symbolic::UNSET;
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
        if (this->modes->isModeEnabled(triton::modes::ALIGNED_MEMORY))
          this->removeAlignedMemory(addr, BYTE_SIZE);
      }


      /* Same as concretizeMemory but with all address memory */
      void SymbolicEngine::concretizeAllMemory(void) {
        this->memoryReference.clear();
        this->alignedMemoryReference.clear();
      }


      /* Gets an aligned entry. */
      triton::ast::AbstractNode* SymbolicEngine::getAlignedMemory(triton::uint64 address, triton::uint32 size) {
        if (this->isAlignedMemory(address, size))
          return this->alignedMemoryReference[std::make_pair(address, size)];
        return nullptr;
      }


      /* Checks if the aligned memory is recored. */
      bool SymbolicEngine::isAlignedMemory(triton::uint64 address, triton::uint32 size) {
        if (this->alignedMemoryReference.find(std::make_pair(address, size)) != this->alignedMemoryReference.end())
          return true;
        return false;
      }


      /* Adds an aligned memory */
      void SymbolicEngine::addAlignedMemory(triton::uint64 address, triton::uint32 size, triton::ast::AbstractNode* node) {
        this->removeAlignedMemory(address, size);
        this->alignedMemoryReference[std::make_pair(address, size)] = node;
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


      /* Returns the reference memory if it's referenced otherwise returns UNSET */
      triton::usize SymbolicEngine::getSymbolicMemoryId(triton::uint64 addr) const {
        std::map<triton::uint64, triton::usize>::const_iterator it;

        if ((it = this->memoryReference.find(addr)) != this->memoryReference.end())
          return it->second;

        return triton::engines::symbolic::UNSET;
      }


      /* Returns the symbolic variable otherwise returns nullptr */
      SymbolicVariable* SymbolicEngine::getSymbolicVariableFromId(triton::usize symVarId) const {
        if (this->symbolicVariables.find(symVarId) == this->symbolicVariables.end())
          return nullptr;
        return this->symbolicVariables.at(symVarId);
      }


      /* Returns the symbolic variable otherwise returns nullptr */
      SymbolicVariable* SymbolicEngine::getSymbolicVariableFromName(const std::string& symVarName) const {
        std::map<triton::usize, SymbolicVariable*>::const_iterator it;

        for (it = this->symbolicVariables.begin(); it != this->symbolicVariables.end(); it++) {
          if (it->second->getName() == symVarName)
            return it->second;
        }

        return nullptr;
      }


      /* Returns all symbolic variables */
      const std::map<triton::usize, SymbolicVariable*>& SymbolicEngine::getSymbolicVariables(void) const {
        return this->symbolicVariables;
      }


      /* Returns the reg reference or UNSET */
      triton::usize SymbolicEngine::getSymbolicRegisterId(const triton::arch::Register& reg) const {
        triton::uint32 parentId = reg.getParent().getId();

        if (!this->architecture->isRegisterValid(parentId))
          return triton::engines::symbolic::UNSET;

        return this->symbolicReg[parentId];
      }


      /* Returns the symbolic address value */
      triton::uint8 SymbolicEngine::getSymbolicMemoryValue(triton::uint64 address) {
        triton::arch::MemoryAccess mem(address, BYTE_SIZE, 0);
        return this->getSymbolicMemoryValue(mem).convert_to<triton::uint8>();
      }


      /* Returns the symbolic memory value */
      triton::uint512 SymbolicEngine::getSymbolicMemoryValue(const triton::arch::MemoryAccess& mem) {
        triton::ast::AbstractNode* node = this->buildSymbolicMemory(mem);
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
        triton::ast::AbstractNode* node = this->buildSymbolicRegister(reg);
        return node->evaluate();
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
      SymbolicExpression* SymbolicEngine::newSymbolicExpression(triton::ast::AbstractNode* node, triton::engines::symbolic::symkind_e kind, const std::string& comment) {
        triton::usize id = this->getUniqueSymExprId();
        node = this->processSimplification(node);
        SymbolicExpression* expr = new(std::nothrow) SymbolicExpression(node, id, kind, comment);
        if (expr == nullptr)
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::newSymbolicExpression(): not enough memory");
        this->symbolicExpressions[id] = expr;
        return expr;
      }


      /* Removes the symbolic expression corresponding to the id */
      void SymbolicEngine::removeSymbolicExpression(triton::usize symExprId) {
        std::map<triton::uint64, triton::usize>::iterator it;

        if (this->symbolicExpressions.find(symExprId) != this->symbolicExpressions.end()) {
          /* Delete and remove the pointer */
          delete this->symbolicExpressions[symExprId];
          this->symbolicExpressions.erase(symExprId);

          /* Concretize the register if it exists */
          for (triton::uint32 i = 0; i < this->numberOfRegisters; i++) {
            if (this->symbolicReg[i] == symExprId) {
              this->symbolicReg[i] = triton::engines::symbolic::UNSET;
              return;
            }
          }

          /* Concretize the memory if it exists */
          for (it = this->memoryReference.begin(); it != memoryReference.end(); it++) {
            if (it->second == symExprId) {
              this->concretizeMemory(it->first);
              return;
            }
          }
        }

      }


      /* Gets the symbolic expression pointer from a symbolic id */
      SymbolicExpression* SymbolicEngine::getSymbolicExpressionFromId(triton::usize symExprId) const {
        if (this->symbolicExpressions.find(symExprId) == this->symbolicExpressions.end())
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::getSymbolicExpressionFromId(): symbolic expression id not found");
        return this->symbolicExpressions.at(symExprId);
      }


      /* Returns all symbolic expressions */
      const std::map<triton::usize, SymbolicExpression*>& SymbolicEngine::getSymbolicExpressions(void) const {
        return this->symbolicExpressions;
      }


      /* Returns the full symbolic expression backtracked. */
      triton::ast::AbstractNode* SymbolicEngine::getFullAst(triton::ast::AbstractNode* node, std::set<triton::usize>& processed) {
        std::vector<triton::ast::AbstractNode*>& childs = node->getChilds();

        for (triton::uint32 index = 0; index < childs.size(); index++) {
          if (childs[index]->getKind() == triton::ast::REFERENCE_NODE) {
            triton::usize id = reinterpret_cast<triton::ast::ReferenceNode*>(childs[index])->getValue();
            triton::ast::AbstractNode* ref = this->getSymbolicExpressionFromId(id)->getAst();
            childs[index] = ref;
            if (processed.find(id) != processed.end())
              continue;
            processed.insert(id);
          }
          this->getFullAst(childs[index], processed);
        }

        return node;
      }


      /* Returns the full symbolic expression backtracked. */
      triton::ast::AbstractNode* SymbolicEngine::getFullAst(triton::ast::AbstractNode* node) {
        std::set<triton::usize> processed;
        return this->getFullAst(node, processed);
      }


      /* [private method] Slices all expressions from a given node */
      void SymbolicEngine::sliceExpressions(triton::ast::AbstractNode* node, std::map<triton::usize, SymbolicExpression*>& exprs) {
        std::vector<triton::ast::AbstractNode*>& childs = node->getChilds();

        for (triton::uint32 index = 0; index < childs.size(); index++) {
          if (childs[index]->getKind() == triton::ast::REFERENCE_NODE) {
            triton::usize id = reinterpret_cast<triton::ast::ReferenceNode*>(childs[index])->getValue();
            if (exprs.find(id) == exprs.end()) {
              SymbolicExpression* expr = this->getSymbolicExpressionFromId(id);
              exprs[id] = expr;
              this->sliceExpressions(expr->getAst(), exprs);
            }
          }
          this->sliceExpressions(childs[index], exprs);
        }
      }


      /* Slices all expressions from a given one */
      std::map<triton::usize, SymbolicExpression*> SymbolicEngine::sliceExpressions(SymbolicExpression* expr) {
        std::map<triton::usize, SymbolicExpression*> exprs;

        if (expr == nullptr)
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::sliceExpressions(): expr cannot be null.");

        exprs[expr->getId()] = expr;
        this->sliceExpressions(expr->getAst(), exprs);

        return exprs;
      }


      /* Returns a list which contains all tainted expressions */
      std::list<SymbolicExpression*> SymbolicEngine::getTaintedSymbolicExpressions(void) const {
        std::map<triton::usize, SymbolicExpression*>::const_iterator it;
        std::list<SymbolicExpression*> taintedExprs;

        for (it = this->symbolicExpressions.begin(); it != this->symbolicExpressions.end(); it++) {
          if (it->second->isTainted == true)
            taintedExprs.push_back(it->second);
        }
        return taintedExprs;
      }


      /* Returns the list of the symbolic variables declared in the trace */
      std::string SymbolicEngine::getVariablesDeclaration(void) const {
        std::map<triton::usize, SymbolicVariable*>::const_iterator it;
        std::stringstream stream;

        for(it = this->symbolicVariables.begin(); it != this->symbolicVariables.end(); it++)
          stream << triton::ast::declareFunction(it->second->getName(), triton::ast::bvdecl(it->second->getSize()));

        return stream.str();
      }


      /* Returns the map of symbolic registers defined */
      std::map<triton::arch::Register, SymbolicExpression*> SymbolicEngine::getSymbolicRegisters(void) const {
        std::map<triton::arch::Register, SymbolicExpression*> ret;

        for (triton::uint32 it = 0; it < this->numberOfRegisters; it++) {
          if (this->symbolicReg[it] != triton::engines::symbolic::UNSET) {
            triton::arch::Register reg(it);
            ret[reg] = this->getSymbolicExpressionFromId(this->symbolicReg[it]);
          }
        }

        return ret;
      }


      /* Returns the map of symbolic memory defined */
      std::map<triton::uint64, SymbolicExpression*> SymbolicEngine::getSymbolicMemory(void) const {
        std::map<triton::uint64, SymbolicExpression*> ret;
        std::map<triton::uint64, triton::usize>::const_iterator it;

        for (it = this->memoryReference.begin(); it != this->memoryReference.end(); it++)
          ret[it->first] = this->getSymbolicExpressionFromId(it->second);

        return ret;
      }


      /*
       * Converts an expression id to a symbolic variable.
       * e.g:
       * #43 = (_ bv10 8)
       * convertExpressionToSymbolicVariable(43, 8)
       * #43 = SymVar_4
       */
      SymbolicVariable* SymbolicEngine::convertExpressionToSymbolicVariable(triton::usize exprId, triton::uint32 symVarSize, const std::string& symVarComment) {
        triton::ast::AbstractNode* tmp  = nullptr;
        SymbolicVariable* symVar = nullptr;
        SymbolicExpression* expression = this->getSymbolicExpressionFromId(exprId);

        symVar = this->newSymbolicVariable(triton::engines::symbolic::UNDEF, 0, symVarSize, symVarComment);
        if (expression->getAst())
            symVar->setConcreteValue(expression->getAst()->evaluate());

        tmp = triton::ast::variable(*symVar);
        tmp->setParent(expression->getAst()->getParents());
        expression->setAst(tmp);
        tmp->init();

        return symVar;
      }


      /* The memory size is used to define the symbolic variable's size. */
      SymbolicVariable* SymbolicEngine::convertMemoryToSymbolicVariable(const triton::arch::MemoryAccess& mem, const std::string& symVarComment) {
        triton::ast::AbstractNode* tmp  = nullptr;
        SymbolicExpression* se          = nullptr;
        SymbolicVariable* symVar        = nullptr;
        triton::usize memSymId          = triton::engines::symbolic::UNSET;
        triton::uint64 memAddr          = mem.getAddress();
        triton::uint32 symVarSize       = mem.getSize();
        triton::uint512 cv              = mem.hasConcreteValue() ? mem.getConcreteValue() : this->architecture->getConcreteMemoryValue(mem);

        memSymId = this->getSymbolicMemoryId(memAddr);

        /* First we create a symbolic variable */
        symVar = this->newSymbolicVariable(triton::engines::symbolic::MEM, memAddr, symVarSize * BYTE_SIZE_BIT, symVarComment);

        /* Setup the concrete value to the symbolic variable */
        symVar->setConcreteValue(cv);

        /* Create the AST node */
        triton::ast::AbstractNode* symVarNode = triton::ast::variable(*symVar);

        /* Record the aligned symbolic variable for a symbolic optimization */
        if (this->modes->isModeEnabled(triton::modes::ALIGNED_MEMORY))
          this->addAlignedMemory(memAddr, symVarSize, symVarNode);

        /*  Split expression in bytes */
        for (triton::sint32 index = symVarSize-1; index >= 0; index--) {

          /* Isolate the good part of the symbolic variable */
          tmp = triton::ast::extract(((BYTE_SIZE_BIT * (index+1)) - 1), ((BYTE_SIZE_BIT * (index+1)) - BYTE_SIZE_BIT), symVarNode);

          /* Check if the memory address is already defined */
          memSymId = this->getSymbolicMemoryId(memAddr+index);
          if (memSymId == triton::engines::symbolic::UNSET) {
            se = this->newSymbolicExpression(tmp, triton::engines::symbolic::MEM, "Byte reference");
            se->setOriginMemory(triton::arch::MemoryAccess(memAddr+index, BYTE_SIZE, tmp->evaluate()));
          }
          else {
            se = this->getSymbolicExpressionFromId(memSymId);
            tmp->setParent(se->getAst()->getParents());
            se->setAst(tmp);
            tmp->init();
            se->setOriginMemory(triton::arch::MemoryAccess(memAddr+index, BYTE_SIZE, tmp->evaluate()));
          }

          /* Add the new memory reference */
          this->addMemoryReference(memAddr+index, se->getId());
        }

        return symVar;
      }


      SymbolicVariable* SymbolicEngine::convertRegisterToSymbolicVariable(const triton::arch::Register& reg, const std::string& symVarComment) {
        SymbolicVariable* symVar        = nullptr;
        SymbolicExpression* expression  = nullptr;
        triton::usize regSymId          = triton::engines::symbolic::UNSET;
        triton::uint32 parentId         = reg.getParent().getId();
        triton::uint32 symVarSize       = reg.getBitSize();
        triton::uint512 cv              = !reg.isImmutable() && reg.hasConcreteValue() ? reg.getConcreteValue() : this->architecture->getConcreteRegisterValue(reg);

        if (!this->architecture->isRegisterValid(parentId))
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::convertRegisterToSymbolicVariable(): Invalid register id");

        regSymId = this->getSymbolicRegisterId(reg);
        if (regSymId == triton::engines::symbolic::UNSET) {
          /* Create the symbolic variable */
          symVar = this->newSymbolicVariable(triton::engines::symbolic::REG, parentId, symVarSize, symVarComment);
          /* Setup the concrete value to the symbolic variable */
          symVar->setConcreteValue(cv);
          /* Create the AST node */
          triton::ast::AbstractNode* tmp = triton::ast::variable(*symVar);
          /* Create the symbolic expression */
          SymbolicExpression* se = this->newSymbolicExpression(tmp, triton::engines::symbolic::REG);
          se->setOriginRegister(reg);
          this->symbolicReg[parentId] = se->getId();
        }

        else {
          /* Get the symbolic expression */
          expression = this->getSymbolicExpressionFromId(regSymId);
          /* Create the symbolic variable */
          symVar = this->newSymbolicVariable(triton::engines::symbolic::REG, parentId, symVarSize, symVarComment);
          /* Setup the concrete value to the symbolic variable */
          symVar->setConcreteValue(cv);
          /* Create the AST node */
          triton::ast::AbstractNode* tmp = triton::ast::variable(*symVar);
          /* Set the AST node */
          tmp->setParent(expression->getAst()->getParents());
          expression->setAst(tmp);
          tmp->init();
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


      /* Returns a symbolic operand based on the abstract wrapper. */
      triton::ast::AbstractNode* SymbolicEngine::buildSymbolicOperand(triton::arch::OperandWrapper& op) {
        switch (op.getType()) {
          case triton::arch::OP_IMM: return this->buildSymbolicImmediate(op.getImmediate());
          case triton::arch::OP_MEM: return this->buildSymbolicMemory(op.getMemory());
          case triton::arch::OP_REG: return this->buildSymbolicRegister(op.getRegister());
          default:
            throw triton::exceptions::SymbolicEngine("SymbolicEngine::buildSymbolicOperand(): Invalid operand.");
        }
      }


      /* Returns a symbolic operand based on the abstract wrapper. */
      triton::ast::AbstractNode* SymbolicEngine::buildSymbolicOperand(triton::arch::Instruction& inst, triton::arch::OperandWrapper& op) {
        switch (op.getType()) {
          case triton::arch::OP_IMM: return this->buildSymbolicImmediate(inst, op.getImmediate());
          case triton::arch::OP_MEM: return this->buildSymbolicMemory(inst, op.getMemory());
          case triton::arch::OP_REG: return this->buildSymbolicRegister(inst, op.getRegister());
          default:
            throw triton::exceptions::SymbolicEngine("SymbolicEngine::buildSymbolicOperand(): Invalid operand.");
        }
      }


      /* Returns a symbolic immediate */
      triton::ast::AbstractNode* SymbolicEngine::buildSymbolicImmediate(const triton::arch::Immediate& imm) {
        triton::ast::AbstractNode* node = triton::ast::bv(imm.getValue(), imm.getBitSize());
        return node;
      }


      /* Returns a symbolic immediate and defines the immediate as input of the instruction */
      triton::ast::AbstractNode* SymbolicEngine::buildSymbolicImmediate(triton::arch::Instruction& inst, triton::arch::Immediate& imm) {
        triton::ast::AbstractNode* node = this->buildSymbolicImmediate(imm);
        inst.setReadImmediate(imm, node);
        return node;
      }


      /* Returns a symbolic memory */
      triton::ast::AbstractNode* SymbolicEngine::buildSymbolicMemory(const triton::arch::MemoryAccess& mem) {
        std::list<triton::ast::AbstractNode*> opVec;

        triton::ast::AbstractNode* tmp            = nullptr;
        triton::uint64 address                    = mem.getAddress();
        triton::uint32 size                       = mem.getSize();
        triton::usize symMem                      = triton::engines::symbolic::UNSET;
        triton::uint8 concreteValue[DQQWORD_SIZE] = {0};
        triton::uint512 value                     = this->architecture->getConcreteMemoryValue(mem);

        triton::utils::fromUintToBuffer(value, concreteValue);

        /*
         * Symbolic optimization
         * If the memory access is aligned, don't split the memory.
         */
        if (this->modes->isModeEnabled(triton::modes::ALIGNED_MEMORY) && this->isAlignedMemory(address, size))
          return this->getAlignedMemory(address, size);

        /* Iterate on every memory cells to use their symbolic or concrete values */
        while (size) {
          symMem = this->getSymbolicMemoryId(address + size - 1);
          /* Check if the memory cell is already symbolic */
          if (symMem != triton::engines::symbolic::UNSET) {
            tmp = triton::ast::reference(symMem);
            opVec.push_back(triton::ast::extract((BYTE_SIZE_BIT - 1), 0, tmp));
          }
          /* Otherwise, use the concerte value */
          else {
            tmp = triton::ast::bv(concreteValue[size - 1], BYTE_SIZE_BIT);
            opVec.push_back(triton::ast::extract((BYTE_SIZE_BIT - 1), 0, tmp));
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
            tmp = triton::ast::concat(opVec);
            break;
          case BYTE_SIZE:
            tmp = opVec.front();
            break;
        }

        return tmp;
      }


      /* Returns a symbolic memory and defines the memory as input of the instruction */
      triton::ast::AbstractNode* SymbolicEngine::buildSymbolicMemory(triton::arch::Instruction& inst, triton::arch::MemoryAccess& mem) {
        triton::ast::AbstractNode* node = this->buildSymbolicMemory(mem);
        mem.setConcreteValue(node->evaluate());
        inst.setLoadAccess(mem, node);
        return node;
      }


      /* Returns a symbolic register */
      triton::ast::AbstractNode* SymbolicEngine::buildSymbolicRegister(const triton::arch::Register& reg) {
        triton::ast::AbstractNode* op = nullptr;
        triton::usize symReg          = this->getSymbolicRegisterId(reg);
        triton::uint32 bvSize         = reg.getBitSize();
        triton::uint32 high           = reg.getHigh();
        triton::uint32 low            = reg.getLow();

        /* Check if the register is already symbolic */
        if (symReg != triton::engines::symbolic::UNSET)
          op = triton::ast::extract(high, low, triton::ast::reference(symReg));

        /* Otherwise, use the concerte value */
        else
          op = triton::ast::bv(this->architecture->getConcreteRegisterValue(reg), bvSize);

        return op;
      }


      /* Returns a symbolic register and defines the register as input of the instruction */
      triton::ast::AbstractNode* SymbolicEngine::buildSymbolicRegister(triton::arch::Instruction& inst, triton::arch::Register& reg) {
        triton::ast::AbstractNode* node = this->buildSymbolicRegister(reg);
        reg.setConcreteValue(node->evaluate());
        inst.setReadRegister(reg, node);
        return node;
      }


      /* Returns the new symbolic abstract expression and links this expression to the instruction. */
      SymbolicExpression* SymbolicEngine::createSymbolicExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, triton::arch::OperandWrapper& dst, const std::string& comment) {
        switch (dst.getType()) {
          case triton::arch::OP_MEM: return this->createSymbolicMemoryExpression(inst, node, dst.getMemory(), comment);
          case triton::arch::OP_REG: return this->createSymbolicRegisterExpression(inst, node, dst.getRegister(), comment);
          default:
            throw triton::exceptions::SymbolicEngine("SymbolicEngine::createSymbolicExpression(): Invalid operand.");
        }
        return nullptr;
      }


      /* Returns the new symbolic memory expression */
      SymbolicExpression* SymbolicEngine::createSymbolicMemoryExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, triton::arch::MemoryAccess& mem, const std::string& comment) {
        triton::ast::AbstractNode* tmp = nullptr;
        std::list<triton::ast::AbstractNode*> ret;

        SymbolicExpression* se   = nullptr;
        triton::uint64 address   = mem.getAddress();
        triton::uint32 writeSize = mem.getSize();

        /* Record the aligned memory for a symbolic optimization */
        if (this->modes->isModeEnabled(triton::modes::ALIGNED_MEMORY))
          this->addAlignedMemory(address, writeSize, node);

        /*
         * As the x86's memory can be accessed without alignment, each byte of the
         * memory must be assigned to an unique reference.
         */
        while (writeSize) {
          /* Extract each byte of the memory */
          tmp = triton::ast::extract(((writeSize * BYTE_SIZE_BIT) - 1), ((writeSize * BYTE_SIZE_BIT) - BYTE_SIZE_BIT), node);
          se = this->newSymbolicExpression(tmp, triton::engines::symbolic::MEM, "Byte reference - " + comment);
          se->setOriginMemory(triton::arch::MemoryAccess(((address + writeSize) - 1), BYTE_SIZE, tmp->evaluate()));
          ret.push_back(tmp);
          inst.addSymbolicExpression(se);
          /* Assign memory with little endian */
          this->addMemoryReference((address + writeSize) - 1, se->getId());
          /* continue */
          writeSize--;
        }

        /* If there is only one reference, we return the symbolic expression */
        if (ret.size() == 1) {
          /* Synchronize the memory operand */
          mem.setConcreteValue(tmp->evaluate());
          /* Synchronize the concrete state */
          this->architecture->setConcreteMemoryValue(mem);
          /* Define the memory store */
          inst.setStoreAccess(mem, tmp);
          return se;
        }

        /* Otherwise, we return the concatenation of all symbolic expressions */
        tmp = triton::ast::concat(ret);

        /* Synchronize the memory operand */
        mem.setConcreteValue(tmp->evaluate());

        /* Synchronize the concrete state */
        this->architecture->setConcreteMemoryValue(mem);

        se  = this->newSymbolicExpression(tmp, triton::engines::symbolic::UNDEF, "Temporary concatenation reference - " + comment);
        se->setOriginMemory(triton::arch::MemoryAccess(address, mem.getSize(), tmp->evaluate()));

        /* Define the memory store */
        inst.setStoreAccess(mem, tmp);
        inst.addSymbolicExpression(se);
        return se;
      }


      /* Returns the new symbolic register expression */
      SymbolicExpression* SymbolicEngine::createSymbolicRegisterExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, triton::arch::Register& reg, const std::string& comment) {
        triton::ast::AbstractNode* finalExpr      = nullptr;
        triton::ast::AbstractNode* origReg        = nullptr;
        triton::uint32 regSize                    = reg.getSize();
        triton::arch::Register parentReg          = reg.getParent();

        if (this->architecture->isFlag(reg))
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::createSymbolicRegisterExpression(): The register cannot be a flag.");

        if (regSize == BYTE_SIZE || regSize == WORD_SIZE)
          origReg = this->buildSymbolicRegister(parentReg);

        switch (regSize) {
          case BYTE_SIZE:
            if (reg.getLow() == 0) {
              finalExpr = triton::ast::concat(triton::ast::extract((this->architecture->registerBitSize() - 1), BYTE_SIZE_BIT, origReg), node);
            }
            else {
              finalExpr = triton::ast::concat(
                            triton::ast::extract((this->architecture->registerBitSize() - 1), WORD_SIZE_BIT, origReg),
                            triton::ast::concat(node, triton::ast::extract((BYTE_SIZE_BIT - 1), 0, origReg))
                          );
            }
            break;

          case WORD_SIZE:
            finalExpr = triton::ast::concat(triton::ast::extract((this->architecture->registerBitSize() - 1), WORD_SIZE_BIT, origReg), node);
            break;

          case DWORD_SIZE:
            /* In AMD64, if a reg32 is written, it clears the 32-bit MSB of the corresponding register (Thx Wisk!) */
            if (this->architecture->getArchitecture() == triton::arch::ARCH_X86_64) {
              finalExpr = triton::ast::zx(DWORD_SIZE_BIT, node);
              break;
            }

          case QWORD_SIZE:
          case DQWORD_SIZE:
          case QQWORD_SIZE:
          case DQQWORD_SIZE:
            finalExpr = triton::ast::zx(parentReg.getBitSize() - node->getBitvectorSize(), node);
            break;
        }

        reg.setConcreteValue(node->evaluate());
        parentReg.setConcreteValue(finalExpr->evaluate());
        triton::engines::symbolic::SymbolicExpression* se = this->newSymbolicExpression(finalExpr, triton::engines::symbolic::REG, comment);
        this->assignSymbolicExpressionToRegister(se, parentReg);
        inst.addSymbolicExpression(se);
        inst.setWrittenRegister(reg, node);

        return se;
      }


      /* Returns the new symbolic flag expression */
      SymbolicExpression* SymbolicEngine::createSymbolicFlagExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, triton::arch::Register& flag, const std::string& comment) {
        if (!this->architecture->isFlag(flag))
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::createSymbolicFlagExpression(): The register must be a flag.");

        flag.setConcreteValue(node->evaluate());
        triton::engines::symbolic::SymbolicExpression *se = this->newSymbolicExpression(node, triton::engines::symbolic::REG, comment);
        this->assignSymbolicExpressionToRegister(se, flag);
        inst.addSymbolicExpression(se);
        inst.setWrittenRegister(flag, node);

        return se;
      }


      /* Returns the new symbolic volatile expression */
      SymbolicExpression* SymbolicEngine::createSymbolicVolatileExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, const std::string& comment) {
        triton::engines::symbolic::SymbolicExpression* se = this->newSymbolicExpression(node, triton::engines::symbolic::UNDEF, comment);
        inst.addSymbolicExpression(se);
        return se;
      }


      /* Adds and assign a new memory reference */
      void SymbolicEngine::addMemoryReference(triton::uint64 mem, triton::usize id) {
        this->memoryReference[mem] = id;
      }


      /* Assigns a symbolic expression to a register */
      void SymbolicEngine::assignSymbolicExpressionToRegister(SymbolicExpression *se, const triton::arch::Register& reg) {
        triton::ast::AbstractNode* node = se->getAst();
        triton::arch::Register parent   = reg.getParent();
        triton::uint32 id               = parent.getId();

        /* We can assign an expression only on parent registers */
        if (reg.getId() != parent.getId())
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::assignSymbolicExpressionToRegister(): We can assign an expression only on parent registers.");

        /* Check if the size of the symbolic expression is equal to the target register */
        if (node->getBitvectorSize() != reg.getBitSize())
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::assignSymbolicExpressionToRegister(): The size of the symbolic expression is not equal to the target register.");

        se->setKind(triton::engines::symbolic::REG);
        se->setOriginRegister(reg);
        this->symbolicReg[id] = se->getId();

        /* Synchronize the concrete state */
        this->architecture->setConcreteRegisterValue(reg);
      }


      /* Assigns a symbolic expression to a memory */
      void SymbolicEngine::assignSymbolicExpressionToMemory(SymbolicExpression *se, const triton::arch::MemoryAccess& mem) {
        triton::ast::AbstractNode* node = se->getAst();
        triton::uint64 address          = mem.getAddress();
        triton::uint32 writeSize        = mem.getSize();

        /* Check if the size of the symbolic expression is equal to the memory access */
        if (node->getBitvectorSize() != mem.getBitSize())
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::assignSymbolicExpressionToMemory(): The size of the symbolic expression is not equal to the memory access.");

        /* Record the aligned memory for a symbolic optimization */
        if (this->modes->isModeEnabled(triton::modes::ALIGNED_MEMORY))
          this->addAlignedMemory(address, writeSize, node);

        /*
         * As the x86's memory can be accessed without alignment, each byte of the
         * memory must be assigned to an unique reference.
         */
        while (writeSize) {
          /* Extract each byte of the memory */
          triton::ast::AbstractNode* tmp = triton::ast::extract(((writeSize * BYTE_SIZE_BIT) - 1), ((writeSize * BYTE_SIZE_BIT) - BYTE_SIZE_BIT), node);
          SymbolicExpression* byteRef = this->newSymbolicExpression(tmp, triton::engines::symbolic::MEM, "Byte reference");
          byteRef->setOriginMemory(triton::arch::MemoryAccess(((address + writeSize) - 1), BYTE_SIZE, tmp->evaluate()));
          /* Assign memory with little endian */
          this->addMemoryReference((address + writeSize) - 1, byteRef->getId());
          writeSize--;
        }
      }


      /* Returns true if the symbolic engine is enable */
      bool SymbolicEngine::isEnabled(void) const {
        return this->enableFlag;
      }


      /* Returns true if the symbolic expression ID exists */
      bool SymbolicEngine::isSymbolicExpressionIdExists(triton::usize symExprId) const {
        if (this->symbolicExpressions.find(symExprId) != this->symbolicExpressions.end())
          return true;
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
          triton::usize symId = this->getSymbolicMemoryId(addr+i);

          if (symId == triton::engines::symbolic::UNSET)
            continue;

          triton::engines::symbolic::SymbolicExpression* symExp = this->getSymbolicExpressionFromId(symId);
          if (symExp->isSymbolized())
            return true;
        }

        return false;
      }


      /* Returns true if the register expression contains a symbolic variable. */
      bool SymbolicEngine::isRegisterSymbolized(const triton::arch::Register& reg) const {
        triton::usize symId = this->getSymbolicRegisterId(reg);

        if (symId == triton::engines::symbolic::UNSET)
          return false;

        triton::engines::symbolic::SymbolicExpression* symExp = this->getSymbolicExpressionFromId(symId);
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
          auto leaAst = triton::ast::bvadd(
                          (mem.getPcRelative() ? triton::ast::bv(mem.getPcRelative(), bitSize) :
                            (this->architecture->isRegisterValid(base) ? this->buildSymbolicRegister(base) :
                              triton::ast::bv(0, bitSize)
                            )
                          ),
                          triton::ast::bvadd(
                            triton::ast::bvmul(
                              (this->architecture->isRegisterValid(index) ? this->buildSymbolicRegister(index) : triton::ast::bv(0, bitSize)),
                              triton::ast::bv(scaleValue, bitSize)
                            ),
                            triton::ast::bv(dispValue, bitSize)
                          )
                        );

          /* Use segments as base address instead of selector into the GDT. */
          if (segmentValue) {
            leaAst = triton::ast::bvadd(
                       triton::ast::bv(segmentValue, seg.getBitSize()),
                       triton::ast::sx((seg.getBitSize() - bitSize), leaAst)
                     );
          }

          /* Set AST */
          mem.setLeaAst(leaAst);

          /* Initialize the address only if it is not already defined */
          if (!mem.getAddress() || force)
            mem.setAddress(leaAst->evaluate().convert_to<triton::uint64>());
        }
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */

