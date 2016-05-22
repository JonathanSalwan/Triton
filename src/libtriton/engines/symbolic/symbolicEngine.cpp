//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <cstring>
#include <stdexcept>

#include <api.hpp>
#include <coreUtils.hpp>
#include <symbolicEngine.hpp>

#ifdef TRITON_PYTHON_BINDINGS
  #include <pythonBindings.hpp>
#endif



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

      SymbolicEngine::SymbolicEngine() {
        triton::api.checkArchitecture();

        this->numberOfRegisters = triton::api.cpuNumberOfRegisters();
        this->symbolicReg = new triton::__uint[this->numberOfRegisters]();

        /* Init all symbolic registers/flags to UNSET (init state) */
        for (triton::uint32 i = 0; i < this->numberOfRegisters; i++)
          this->symbolicReg[i] = triton::engines::symbolic::UNSET;

        this->emulationFlag   = false;
        this->enableFlag      = true;
        this->uniqueSymExprId = 0;
        this->uniqueSymVarId  = 0;
      }


      void SymbolicEngine::init(const SymbolicEngine& other) {
        triton::api.checkArchitecture();

        this->numberOfRegisters = other.numberOfRegisters;
        this->symbolicReg = new triton::__uint[this->numberOfRegisters]();

        for (triton::uint32 i = 0; i < this->numberOfRegisters; i++)
          this->symbolicReg[i] = other.symbolicReg[i];

        this->alignedMemoryReference      = other.alignedMemoryReference;
        this->emulationFlag               = other.emulationFlag;
        this->enableFlag                  = other.enableFlag;
        this->enabledOptimizations        = other.enabledOptimizations;
        this->memoryReference             = other.memoryReference;
        this->pathConstraints             = other.pathConstraints;
        this->simplificationCallbacks     = other.simplificationCallbacks;
        this->symbolicExpressions         = other.symbolicExpressions;
        this->symbolicVariables           = other.symbolicVariables;
        this->uniqueSymExprId             = other.uniqueSymExprId;
        this->uniqueSymVarId              = other.uniqueSymVarId;
        #ifdef TRITON_PYTHON_BINDINGS
        this->pySimplificationCallbacks   = other.pySimplificationCallbacks;
        #endif
      }


      SymbolicEngine::SymbolicEngine(const SymbolicEngine& copy) {
        this->init(copy);
      }


      void SymbolicEngine::operator=(const SymbolicEngine& other) {
        delete[] this->symbolicReg;
        this->init(other);
      }


      SymbolicEngine::~SymbolicEngine() {
        std::map<triton::__uint, SymbolicExpression*>::iterator it1 = this->symbolicExpressions.begin();
        std::map<triton::__uint, SymbolicVariable*>::iterator it2 = this->symbolicVariables.begin();

        /* Delete all symbolic expressions */
        for (; it1 != this->symbolicExpressions.end(); ++it1)
          delete it1->second;

        /* Delete all symbolic variables */
        for (; it2 != this->symbolicVariables.end(); ++it2)
          delete it2->second;

        /* Delete all symbolic register */
        delete[] this->symbolicReg;
      }


      /*
       * Concretize a register. If the register is setup as UNSET, the next assignment
       * will be over the concretization. This method must be called before symbolic
       * processing.
       */
      void SymbolicEngine::concretizeRegister(const triton::arch::RegisterOperand& reg) {
        triton::uint32 parentId = reg.getParent().getId();
        if (!triton::api.isCpuRegisterValid(parentId))
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
      void SymbolicEngine::concretizeMemory(const triton::arch::MemoryOperand& mem) {
        triton::__uint addr = mem.getAddress();
        triton::uint32 size = mem.getSize();
        for (triton::uint32 index = 0; index < size; index++)
          this->concretizeMemory(addr+index);
      }


      /*
       * Concretize a memory. If the memory is not found into the map, the next
       * assignment will be over the concretization. This method must be called
       * before symbolic processing.
       */
      void SymbolicEngine::concretizeMemory(triton::__uint addr) {
        this->memoryReference.erase(addr);
        if (triton::api.isSymbolicOptimizationEnabled(triton::engines::symbolic::ALIGNED_MEMORY))
          this->removeAlignedMemory(addr);
      }


      /* Same as concretizeMemory but with all address memory */
      void SymbolicEngine::concretizeAllMemory(void) {
        this->memoryReference.clear();
        this->alignedMemoryReference.clear();
      }


      /* Remove aligned memory */
      void SymbolicEngine::removeAlignedMemory(triton::__uint addr) {
        /* Remove address with several sizes */
        this->alignedMemoryReference.erase(std::make_pair(addr,  BYTE_SIZE));
        this->alignedMemoryReference.erase(std::make_pair(addr,  WORD_SIZE));
        this->alignedMemoryReference.erase(std::make_pair(addr,  DWORD_SIZE));
        this->alignedMemoryReference.erase(std::make_pair(addr,  QWORD_SIZE));
        this->alignedMemoryReference.erase(std::make_pair(addr,  DQWORD_SIZE));
        this->alignedMemoryReference.erase(std::make_pair(addr,  QQWORD_SIZE));
        this->alignedMemoryReference.erase(std::make_pair(addr,  DQQWORD_SIZE));

        /* Remove overloaded range */
        this->alignedMemoryReference.erase(std::make_pair(addr-BYTE_SIZE,   WORD_SIZE));
        this->alignedMemoryReference.erase(std::make_pair(addr-BYTE_SIZE,   DWORD_SIZE));
        this->alignedMemoryReference.erase(std::make_pair(addr-BYTE_SIZE,   QWORD_SIZE));
        this->alignedMemoryReference.erase(std::make_pair(addr-BYTE_SIZE,   DQWORD_SIZE));
        this->alignedMemoryReference.erase(std::make_pair(addr-BYTE_SIZE,   QQWORD_SIZE));
        this->alignedMemoryReference.erase(std::make_pair(addr-BYTE_SIZE,   DQQWORD_SIZE));

        this->alignedMemoryReference.erase(std::make_pair(addr-WORD_SIZE,   DWORD_SIZE));
        this->alignedMemoryReference.erase(std::make_pair(addr-WORD_SIZE,   QWORD_SIZE));
        this->alignedMemoryReference.erase(std::make_pair(addr-WORD_SIZE,   DQWORD_SIZE));
        this->alignedMemoryReference.erase(std::make_pair(addr-WORD_SIZE,   QQWORD_SIZE));
        this->alignedMemoryReference.erase(std::make_pair(addr-WORD_SIZE,   DQQWORD_SIZE));

        this->alignedMemoryReference.erase(std::make_pair(addr-DWORD_SIZE,  QWORD_SIZE));
        this->alignedMemoryReference.erase(std::make_pair(addr-DWORD_SIZE,  DQWORD_SIZE));
        this->alignedMemoryReference.erase(std::make_pair(addr-DWORD_SIZE,  QQWORD_SIZE));
        this->alignedMemoryReference.erase(std::make_pair(addr-DWORD_SIZE,  DQQWORD_SIZE));

        this->alignedMemoryReference.erase(std::make_pair(addr-QWORD_SIZE,  DQWORD_SIZE));
        this->alignedMemoryReference.erase(std::make_pair(addr-QWORD_SIZE,  QQWORD_SIZE));
        this->alignedMemoryReference.erase(std::make_pair(addr-QWORD_SIZE,  DQQWORD_SIZE));

        this->alignedMemoryReference.erase(std::make_pair(addr-DQWORD_SIZE, QQWORD_SIZE));
        this->alignedMemoryReference.erase(std::make_pair(addr-DQWORD_SIZE, DQQWORD_SIZE));

        this->alignedMemoryReference.erase(std::make_pair(addr-QQWORD_SIZE, DQQWORD_SIZE));
      }


      /* Returns the reference memory if it's referenced otherwise returns UNSET */
      triton::__uint SymbolicEngine::getSymbolicMemoryId(triton::__uint addr) const {
        std::map<triton::__uint, triton::__uint>::const_iterator it;
        if ((it = this->memoryReference.find(addr)) != this->memoryReference.end())
          return it->second;
        return triton::engines::symbolic::UNSET;
      }


      /* Returns the symbolic variable otherwise returns nullptr */
      SymbolicVariable* SymbolicEngine::getSymbolicVariableFromId(triton::__uint symVarId) const {
        if (this->symbolicVariables.find(symVarId) == this->symbolicVariables.end())
          return nullptr;
        return this->symbolicVariables.at(symVarId);
      }


      /* Returns the symbolic variable otherwise returns nullptr */
      SymbolicVariable* SymbolicEngine::getSymbolicVariableFromName(const std::string& symVarName) const {
        std::map<triton::__uint, SymbolicVariable*>::const_iterator it;

        for (it = this->symbolicVariables.begin(); it != this->symbolicVariables.end(); it++) {
          if (it->second->getSymVarName() == symVarName)
            return it->second;
        }
        return nullptr;
      }


      /* Returns all symbolic variables */
      const std::map<triton::__uint, SymbolicVariable*>& SymbolicEngine::getSymbolicVariables(void) const {
        return this->symbolicVariables;
      }


      /* Returns the reg reference or UNSET */
      triton::__uint SymbolicEngine::getSymbolicRegisterId(const triton::arch::RegisterOperand& reg) const {
        triton::uint32 parentId = reg.getParent().getId();
        if (!triton::api.isCpuRegisterValid(parentId))
          return triton::engines::symbolic::UNSET;
        return this->symbolicReg[parentId];
      }


      /* Returns the symbolic address value */
      triton::uint8 SymbolicEngine::getSymbolicMemoryValue(triton::__uint address) {
        triton::arch::MemoryOperand mem(address, BYTE_SIZE, 0);
        return this->getSymbolicMemoryValue(mem).convert_to<triton::uint8>();
      }


      /* Returns the symbolic memory value */
      triton::uint512 SymbolicEngine::getSymbolicMemoryValue(const triton::arch::MemoryOperand& mem) {
        triton::ast::AbstractNode* node = this->buildSymbolicMemoryOperand(mem);
        return node->evaluate();
      }


      /* Returns the symbolic values of a memory area */
      std::vector<triton::uint8> SymbolicEngine::getSymbolicMemoryAreaValue(triton::__uint baseAddr, triton::uint32 size) {
        std::vector<triton::uint8> area;

        for (triton::uint32 index = 0; index < size; index++)
          area.push_back(this->getSymbolicMemoryValue(baseAddr+index));

        return area;
      }


      /* Returns the symbolic register value */
      triton::uint512 SymbolicEngine::getSymbolicRegisterValue(const triton::arch::RegisterOperand& reg) {
        triton::ast::AbstractNode* node = this->buildSymbolicRegisterOperand(reg);
        return node->evaluate();
      }


      /* Creates a new symbolic expression */
      /* Get an unique id.
       * Mainly used when a new symbolic expression is created */
      triton::__uint SymbolicEngine::getUniqueSymExprId(void) {
        return this->uniqueSymExprId++;
      }


      /* Creates a new symbolic variable */
      /* Get an unique id.
       * Mainly used when a new symbolic variable is created */
      triton::__uint SymbolicEngine::getUniqueSymVarId(void) {
        return this->uniqueSymVarId++;
      }


      /* Creates a new symbolic expression with comment */
      SymbolicExpression* SymbolicEngine::newSymbolicExpression(triton::ast::AbstractNode* node, triton::engines::symbolic::symkind_e kind, const std::string& comment) {
        triton::__uint id = this->getUniqueSymExprId();
        node = this->processSimplification(node);
        SymbolicExpression* expr = new SymbolicExpression(node, id, kind, comment);
        if (expr == nullptr)
          throw std::runtime_error("SymbolicEngine::newSymbolicExpression(): not enough memory");
        this->symbolicExpressions[id] = expr;
        return expr;
      }


      /* Removes the symbolic expression corresponding to the id */
      void SymbolicEngine::removeSymbolicExpression(triton::__uint symExprId) {
        std::map<triton::__uint, triton::__uint>::iterator it;

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
      SymbolicExpression* SymbolicEngine::getSymbolicExpressionFromId(triton::__uint symExprId) const {
        if (this->symbolicExpressions.find(symExprId) == this->symbolicExpressions.end())
          throw std::runtime_error("SymbolicEngine::getSymbolicExpressionFromId(): symbolic expression id not found");
        return this->symbolicExpressions.at(symExprId);
      }


      /* Returns all symbolic expressions */
      const std::map<triton::__uint, SymbolicExpression*>& SymbolicEngine::getSymbolicExpressions(void) const {
        return this->symbolicExpressions;
      }


      /* Returns the full symbolic expression backtracked. */
      triton::ast::AbstractNode* SymbolicEngine::getFullAst(triton::ast::AbstractNode* node) {
        std::vector<triton::ast::AbstractNode*>& childs = node->getChilds();

        for (triton::uint32 index = 0; index < childs.size(); index++) {
          if (childs[index]->getKind() == triton::ast::REFERENCE_NODE) {
            triton::__uint id = reinterpret_cast<triton::ast::ReferenceNode*>(childs[index])->getValue();
            triton::ast::AbstractNode* ref = this->getSymbolicExpressionFromId(id)->getAst();
            childs[index] = ref;
          }
          this->getFullAst(childs[index]);
        }

        return node;
      }


      /* Returns a list which contains all tainted expressions */
      std::list<SymbolicExpression*> SymbolicEngine::getTaintedSymbolicExpressions(void) const {
        std::map<triton::__uint, SymbolicExpression*>::const_iterator it;
        std::list<SymbolicExpression*> taintedExprs;

        for (it = this->symbolicExpressions.begin(); it != this->symbolicExpressions.end(); it++) {
          if (it->second->isTainted == true)
            taintedExprs.push_back(it->second);
        }
        return taintedExprs;
      }


      /* Returns the list of the symbolic variables declared in the trace */
      std::string SymbolicEngine::getVariablesDeclaration(void) const {
        std::map<triton::__uint, SymbolicVariable*>::const_iterator it;
        std::stringstream stream;

        for(it = this->symbolicVariables.begin(); it != this->symbolicVariables.end(); it++)
          stream << triton::ast::declareFunction(it->second->getSymVarName(), triton::ast::bvdecl(it->second->getSymVarSize()));

        return stream.str();
      }


      /* Returns the map of symbolic registers defined */
      std::map<triton::arch::RegisterOperand, SymbolicExpression*> SymbolicEngine::getSymbolicRegisters(void) const {
        std::map<triton::arch::RegisterOperand, SymbolicExpression*> ret;

        for (triton::uint32 it = 0; it < this->numberOfRegisters; it++) {
          if (this->symbolicReg[it] != triton::engines::symbolic::UNSET) {
            triton::arch::RegisterOperand reg(it);
            ret[reg] = this->getSymbolicExpressionFromId(this->symbolicReg[it]);
          }
        }

        return ret;
      }


      /* Returns the map of symbolic memory defined */
      std::map<triton::__uint, SymbolicExpression*> SymbolicEngine::getSymbolicMemory(void) const {
        std::map<triton::__uint, SymbolicExpression*> ret;
        std::map<triton::__uint, triton::__uint>::const_iterator it;

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
      SymbolicVariable* SymbolicEngine::convertExpressionToSymbolicVariable(triton::__uint exprId, triton::uint32 symVarSize, const std::string& symVarComment) {
        triton::ast::AbstractNode* tmp  = nullptr;
        SymbolicVariable* symVar = nullptr;
        SymbolicExpression* expression = this->getSymbolicExpressionFromId(exprId);

        symVar = this->newSymbolicVariable(triton::engines::symbolic::UNDEF, 0, symVarSize, symVarComment);
        if (expression->getAst())
            symVar->setSymVarConcreteValue(expression->getAst()->evaluate());

        tmp = triton::ast::variable(*symVar);
        tmp->setParent(expression->getAst()->getParents());
        expression->setAst(tmp);
        tmp->init();

        return symVar;
      }


      /* The memory size is used to define the symbolic variable's size. */
      SymbolicVariable* SymbolicEngine::convertMemoryToSymbolicVariable(const triton::arch::MemoryOperand& mem, const std::string& symVarComment) {
        triton::ast::AbstractNode* tmp  = nullptr;
        SymbolicExpression* se          = nullptr;
        SymbolicVariable* symVar        = nullptr;
        triton::__uint memSymId         = triton::engines::symbolic::UNSET;
        triton::__uint memAddr          = mem.getAddress();
        triton::uint32 symVarSize       = mem.getSize();
        triton::uint512 cv              = mem.getConcreteValue() ? mem.getConcreteValue() : triton::api.getLastMemoryValue(mem);

        memSymId = this->getSymbolicMemoryId(memAddr);

        /* First we create a symbolic variable */
        symVar = this->newSymbolicVariable(triton::engines::symbolic::MEM, memAddr, symVarSize * BYTE_SIZE_BIT, symVarComment);
        /* Setup the concrete value to the symbolic variable */
        symVar->setSymVarConcreteValue(cv);
        /* Create the AST node */
        triton::ast::AbstractNode* symVarNode = triton::ast::variable(*symVar);

        /*  Split expression in bytes */
        for (triton::sint32 index = symVarSize-1; index >= 0; index--) {

          /* Isolate the good part of the symbolic variable */
          tmp = triton::ast::extract(((BYTE_SIZE_BIT * (index+1)) - 1), ((BYTE_SIZE_BIT * (index+1)) - BYTE_SIZE_BIT), symVarNode);

          /* Check if the memory address is already defined */
          memSymId = this->getSymbolicMemoryId(memAddr+index);
          if (memSymId == triton::engines::symbolic::UNSET) {
            se = this->newSymbolicExpression(tmp, triton::engines::symbolic::MEM, "Byte reference");
            se->setOriginMemory(triton::arch::MemoryOperand(memAddr+index, BYTE_SIZE, tmp->evaluate()));
          }
          else {
            se = this->getSymbolicExpressionFromId(memSymId);
            tmp->setParent(se->getAst()->getParents());
            se->setAst(tmp);
            tmp->init();
            se->setOriginMemory(triton::arch::MemoryOperand(memAddr+index, BYTE_SIZE, tmp->evaluate()));
          }

          /* Add the new memory reference */
          this->addMemoryReference(memAddr+index, se->getId());
          if (triton::api.isSymbolicOptimizationEnabled(triton::engines::symbolic::ALIGNED_MEMORY))
            removeAlignedMemory(memAddr+index);
        }

        return symVar;
      }


      SymbolicVariable* SymbolicEngine::convertRegisterToSymbolicVariable(const triton::arch::RegisterOperand& reg, const std::string& symVarComment) {
        SymbolicVariable* symVar        = nullptr;
        SymbolicExpression* expression  = nullptr;
        triton::__uint regSymId         = triton::engines::symbolic::UNSET;
        triton::uint32 parentId         = reg.getParent().getId();
        triton::uint32 symVarSize       = reg.getBitSize();
        triton::uint512 cv              = reg.getConcreteValue() ? reg.getConcreteValue() : triton::api.getLastRegisterValue(reg);

        if (!triton::api.isCpuRegisterValid(parentId))
          throw std::runtime_error("SymbolicEngine::convertRegisterToSymbolicVariable(): Invalid register id");

        regSymId = this->getSymbolicRegisterId(reg);
        if (regSymId == triton::engines::symbolic::UNSET) {
          /* Create the symbolic variable */
          symVar = this->newSymbolicVariable(triton::engines::symbolic::REG, parentId, symVarSize, symVarComment);
          /* Setup the concrete value to the symbolic variable */
          symVar->setSymVarConcreteValue(cv);
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
          symVar->setSymVarConcreteValue(cv);
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
      SymbolicVariable* SymbolicEngine::newSymbolicVariable(triton::engines::symbolic::symkind_e kind, triton::__uint kindValue, triton::uint32 size, const std::string& comment) {
        triton::__uint uniqueId  = this->getUniqueSymVarId();
        SymbolicVariable* symVar = new SymbolicVariable(kind, kindValue, uniqueId, size, comment);

        if (symVar == nullptr)
          throw std::runtime_error("SymbolicEngine::newSymbolicVariable(): Cannot allocate a new symbolic variable");

        this->symbolicVariables[uniqueId] = symVar;
        return symVar;
      }


      /* Returns an immediate symbolic operand */
      triton::ast::AbstractNode* SymbolicEngine::buildSymbolicImmediateOperand(const triton::arch::ImmediateOperand& imm) {
        triton::ast::AbstractNode* node = triton::ast::bv(imm.getValue(), imm.getBitSize());
        return node;
      }


      /* Returns an immediate symbolic operand and defines the immediate as input of the instruction */
      triton::ast::AbstractNode* SymbolicEngine::buildSymbolicImmediateOperand(triton::arch::Instruction& inst, triton::arch::ImmediateOperand& imm) {
        triton::ast::AbstractNode* node = this->buildSymbolicImmediateOperand(imm);
        inst.setReadImmediate(imm, node);
        return node;
      }


      /* Returns a symbolic memory operand */
      triton::ast::AbstractNode* SymbolicEngine::buildSymbolicMemoryOperand(const triton::arch::MemoryOperand& mem) {
        std::list<triton::ast::AbstractNode*> opVec;

        triton::ast::AbstractNode* tmp            = nullptr;
        triton::__uint address                    = mem.getAddress();
        triton::uint32 size                       = mem.getSize();
        triton::__uint symMem                     = triton::engines::symbolic::UNSET;
        triton::uint8 concreteValue[DQQWORD_SIZE] = {0};
        triton::uint512 value                     = triton::api.getLastMemoryValue(mem);

        triton::utils::fromUintToBuffer(value, concreteValue);

        /*
         * Symbolic optimization
         * If the memory access is aligned, don't split the memory.
         */
        if (triton::api.isSymbolicOptimizationEnabled(triton::engines::symbolic::ALIGNED_MEMORY)) {
          if (this->alignedMemoryReference.find(std::make_pair(address, size)) != this->alignedMemoryReference.end()) {
            return this->alignedMemoryReference[std::make_pair(address, size)];
          }
        }

        while (size) {
          symMem = this->getSymbolicMemoryId(address + size - 1);
          if (symMem != triton::engines::symbolic::UNSET) {
            tmp = triton::ast::reference(symMem);
            opVec.push_back(triton::ast::extract((BYTE_SIZE_BIT - 1), 0, tmp));
          }
          else {
            tmp = triton::ast::bv(concreteValue[size - 1], BYTE_SIZE_BIT);
            opVec.push_back(triton::ast::extract((BYTE_SIZE_BIT - 1), 0, tmp));
          }
          size--;
        }

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


      /* Returns a symbolic memory operand and defines the memory as input of the instruction */
      triton::ast::AbstractNode* SymbolicEngine::buildSymbolicMemoryOperand(triton::arch::Instruction& inst, triton::arch::MemoryOperand& mem) {
        triton::ast::AbstractNode* node = this->buildSymbolicMemoryOperand(mem);
        mem.setConcreteValue(node->evaluate());
        inst.setLoadAccess(mem, node);
        return node;
      }


      /* Returns a symbolic register operand */
      triton::ast::AbstractNode* SymbolicEngine::buildSymbolicRegisterOperand(const triton::arch::RegisterOperand& reg) {
        triton::ast::AbstractNode* op = nullptr;
        triton::__uint symReg         = this->getSymbolicRegisterId(reg);
        triton::uint32 bvSize         = reg.getBitSize();
        triton::uint32 high           = reg.getHigh();
        triton::uint32 low            = reg.getLow();

        if (symReg != triton::engines::symbolic::UNSET)
          op = triton::ast::extract(high, low, triton::ast::reference(symReg));
        else
          op = triton::ast::bv(triton::api.getLastRegisterValue(reg), bvSize);

        return op;
      }


      /* Returns a symbolic register operand and defines the register as input of the instruction */
      triton::ast::AbstractNode* SymbolicEngine::buildSymbolicRegisterOperand(triton::arch::Instruction& inst, triton::arch::RegisterOperand& reg) {
        triton::ast::AbstractNode* node = this->buildSymbolicRegisterOperand(reg);
        reg.setConcreteValue(node->evaluate());
        inst.setReadRegister(reg, node);
        return node;
      }


      /* Returns the new symbolic memory expression */
      SymbolicExpression* SymbolicEngine::createSymbolicMemoryExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, triton::arch::MemoryOperand& mem, const std::string& comment) {
        triton::ast::AbstractNode* tmp = nullptr;
        std::list<triton::ast::AbstractNode*> ret;

        SymbolicExpression* se   = nullptr;
        triton::__uint address   = mem.getAddress();
        triton::uint32 writeSize = mem.getSize();

        /* Record the aligned memory for a symbolic optimization */
        if (triton::api.isSymbolicOptimizationEnabled(triton::engines::symbolic::ALIGNED_MEMORY)) {
          this->removeAlignedMemory(address);
          this->alignedMemoryReference[std::make_pair(address, writeSize)] = node;
        }

        /*
         * As the x86's memory can be accessed without alignment, each byte of the
         * memory must be assigned to an unique reference.
         */
        while (writeSize) {
          /* Extract each byte of the memory */
          tmp = triton::ast::extract(((writeSize * BYTE_SIZE_BIT) - 1), ((writeSize * BYTE_SIZE_BIT) - BYTE_SIZE_BIT), node);
          se = this->newSymbolicExpression(tmp, triton::engines::symbolic::MEM, "Byte reference - " + comment);
          se->setOriginMemory(triton::arch::MemoryOperand(((address + writeSize) - 1), BYTE_SIZE, tmp->evaluate()));
          ret.push_back(tmp);
          inst.addSymbolicExpression(se);
          /* Assign memory with little endian */
          this->addMemoryReference((address + writeSize) - 1, se->getId());
          writeSize--;
        }

        /* If there is only one reference, we return the symbolic expression */
        if (ret.size() == 1) {
          if (tmp != nullptr)
            mem.setConcreteValue(tmp->evaluate());
          inst.setStoreAccess(mem, tmp);
          return se;
        }

        /* Otherwise, we return the concatenation of all symbolic expressions */
        tmp = triton::ast::concat(ret);
        mem.setConcreteValue(tmp->evaluate());

        se  = this->newSymbolicExpression(tmp, triton::engines::symbolic::UNDEF, "Temporary concatenation reference - " + comment);
        se->setOriginMemory(triton::arch::MemoryOperand(address, mem.getSize(), tmp->evaluate()));

        inst.setStoreAccess(mem, tmp);
        inst.addSymbolicExpression(se);
        return se;
      }


      /* Returns the new symbolic register expression */
      SymbolicExpression* SymbolicEngine::createSymbolicRegisterExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, triton::arch::RegisterOperand& reg, const std::string& comment) {
        triton::ast::AbstractNode* finalExpr      = nullptr;
        triton::ast::AbstractNode* origReg        = nullptr;
        triton::uint32 regSize                    = reg.getSize();
        triton::arch::RegisterOperand parentReg   = reg.getParent();

        if (reg.isFlag())
          throw std::runtime_error("SymbolicEngine::createSymbolicRegisterExpression(): The register cannot be a flag.");

        if (regSize == BYTE_SIZE || regSize == WORD_SIZE)
          origReg = this->buildSymbolicRegisterOperand(parentReg);

        switch (regSize) {
          case BYTE_SIZE:
            if (reg.getLow() == 0) {
              finalExpr = triton::ast::concat(triton::ast::extract((triton::api.cpuRegisterBitSize() - 1), BYTE_SIZE_BIT, origReg), node);
            }
            else {
              finalExpr = triton::ast::concat(
                            triton::ast::extract((triton::api.cpuRegisterBitSize() - 1), WORD_SIZE_BIT, origReg),
                            triton::ast::concat(node, triton::ast::extract((BYTE_SIZE_BIT - 1), 0, origReg))
                          );
            }
            break;

          case WORD_SIZE:
            finalExpr = triton::ast::concat(triton::ast::extract((triton::api.cpuRegisterBitSize() - 1), WORD_SIZE_BIT, origReg), node);
            break;

          case DWORD_SIZE:
            /* In AMD64, if a reg32 is written, it clears the 32-bit MSB of the corresponding register (Thx Wisk!) */
            if (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) {
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
      SymbolicExpression* SymbolicEngine::createSymbolicFlagExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, triton::arch::RegisterOperand& flag, const std::string& comment) {
        if (!flag.isFlag())
          throw std::runtime_error("SymbolicEngine::createSymbolicFlagExpression(): The register must be a flag.");
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
      void SymbolicEngine::addMemoryReference(triton::__uint mem, triton::__uint id) {
        this->memoryReference[mem] = id;
      }


      /* Assigns a symbolic expression to a register */
      void SymbolicEngine::assignSymbolicExpressionToRegister(SymbolicExpression *se, const triton::arch::RegisterOperand& reg) {
        triton::ast::AbstractNode* node = se->getAst();
        triton::arch::RegisterOperand parent = reg.getParent();
        triton::uint32 id = parent.getId();

        /* We can assign an expression only on parent registers */
        if (reg.getId() != parent.getId())
          throw std::runtime_error("SymbolicEngine::assignSymbolicExpressionToRegister(): We can assign an expression only on parent registers.");

        /* Check if the size of the symbolic expression is equal to the target register */
        if (node->getBitvectorSize() != reg.getBitSize())
          throw std::runtime_error("SymbolicEngine::assignSymbolicExpressionToRegister(): The size of the symbolic expression is not equal to the target register.");

        se->setKind(triton::engines::symbolic::REG);
        se->setOriginRegister(reg);
        this->symbolicReg[id] = se->getId();
      }


      /* Assigns a symbolic expression to a memory */
      void SymbolicEngine::assignSymbolicExpressionToMemory(SymbolicExpression *se, const triton::arch::MemoryOperand& mem) {
        triton::ast::AbstractNode* node = se->getAst();
        triton::__uint address          = mem.getAddress();
        triton::uint32 writeSize        = mem.getSize();

        /* Check if the size of the symbolic expression is equal to the memory access */
        if (node->getBitvectorSize() != mem.getBitSize())
          throw std::runtime_error("SymbolicEngine::assignSymbolicExpressionToMemory(): The size of the symbolic expression is not equal to the memory access.");

        /*
         * As the x86's memory can be accessed without alignment, each byte of the
         * memory must be assigned to an unique reference.
         */
        while (writeSize) {
          /* Extract each byte of the memory */
          triton::ast::AbstractNode* tmp = triton::ast::extract(((writeSize * BYTE_SIZE_BIT) - 1), ((writeSize * BYTE_SIZE_BIT) - BYTE_SIZE_BIT), node);
          SymbolicExpression* byteRef = this->newSymbolicExpression(tmp, triton::engines::symbolic::MEM, "Byte reference");
          byteRef->setOriginMemory(triton::arch::MemoryOperand(((address + writeSize) - 1), BYTE_SIZE, tmp->evaluate()));
          /* Assign memory with little endian */
          this->addMemoryReference((address + writeSize) - 1, byteRef->getId());
          writeSize--;
        }
      }


      /* Returns true if the we perform a full symbolic emulation. */
      bool SymbolicEngine::isEmulationEnabled(void) const {
        return this->emulationFlag;
      }


      /* Returns true if the symbolic engine is enable. Otherwise returns false. */
      bool SymbolicEngine::isEnabled(void) const {
        return this->enableFlag;
      }


      /* Returns true if the symbolic expression ID exists. */
      bool SymbolicEngine::isSymbolicExpressionIdExists(triton::__uint symExprId) const {
        if (this->symbolicExpressions.find(symExprId) != this->symbolicExpressions.end())
          return true;
        return false;
      }


      /* Enables or disables the symbolic emulation. */
      void SymbolicEngine::emulation(bool flag) {
        this->emulationFlag = flag;
      }


      /* Enables or disables the symbolic engine */
      void SymbolicEngine::enable(bool flag) {
        this->enableFlag = flag;
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */

