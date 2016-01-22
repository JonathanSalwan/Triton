//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <cstring>
#include <stdexcept>

#include <api.hpp>
#include <symbolicEngine.hpp>
#include <utils.hpp>

#ifdef TRITON_PYTHON_BINDINGS
  #ifdef __unix__
    #include <python2.7/Python.h>
  #elif _WIN32
    #include <Python.h>
  #endif
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

        this->numberOfReg = triton::api.cpuNumberOfReg();
        this->symbolicReg = new triton::__uint[this->numberOfReg]();

        /* Init all symbolic registers/flags to UNSET (init state) */
        for (triton::uint32 i = 0; i < this->numberOfReg; i++)
          this->symbolicReg[i] = triton::engines::symbolic::UNSET;

        this->enableFlag      = true;
        this->uniqueSymExprId = 0;
        this->uniqueSymVarId  = 0;
      }


      void SymbolicEngine::init(const SymbolicEngine& other) {
        triton::api.checkArchitecture();

        this->numberOfReg = other.numberOfReg;
        this->symbolicReg = new triton::__uint[this->numberOfReg]();

        for (triton::uint32 i = 0; i < this->numberOfReg; i++)
          this->symbolicReg[i] = other.symbolicReg[i];

        this->enableFlag                  = other.enableFlag;
        this->memoryReference             = other.memoryReference;
        this->symbolicExpressions         = other.symbolicExpressions;
        this->symbolicVariables           = other.symbolicVariables;
        this->uniqueSymExprId             = other.uniqueSymExprId;
        this->uniqueSymVarId              = other.uniqueSymVarId;
        this->enabledOptimizations        = other.enabledOptimizations;
        this->simplificationCallbacks     = other.simplificationCallbacks;
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
      void SymbolicEngine::concretizeReg(triton::arch::RegisterOperand& reg) {
        triton::uint32 parentId = reg.getParent().getId();
        if (!triton::api.isCpuRegValid(parentId))
          return;
        this->symbolicReg[parentId] = triton::engines::symbolic::UNSET;
      }


      /* Same as concretizeReg but with all registers */
      void SymbolicEngine::concretizeAllReg(void) {
        for (triton::uint32 i = 0; i < this->numberOfReg; i++)
          this->symbolicReg[i] = triton::engines::symbolic::UNSET;
      }


      /*
       * Concretize a memory. If the memory is not found into the map, the next
       * assignment will be over the concretization. This method must be called
       * before symbolic processing.
       */
      void SymbolicEngine::concretizeMem(triton::arch::MemoryOperand& mem) {
        triton::__uint addr = mem.getAddress();
        triton::uint32 size = mem.getSize();
        for (triton::uint32 index = 0; index < size; index++)
          this->memoryReference.erase(addr+index);
      }


      /*
       * Concretize a memory. If the memory is not found into the map, the next
       * assignment will be over the concretization. This method must be called
       * before symbolic processing.
       */
      void SymbolicEngine::concretizeMem(triton::__uint addr) {
        this->memoryReference.erase(addr);
      }


      /* Same as concretizeMem but with all address memory */
      void SymbolicEngine::concretizeAllMem(void) {
        this->memoryReference.clear();
      }


      /* Returns the reference memory if it's referenced otherwise returns UNSET */
      triton::__uint SymbolicEngine::getSymbolicMemoryId(triton::__uint addr) {
        std::map<triton::__uint, triton::__uint>::iterator it;
        if ((it = this->memoryReference.find(addr)) != this->memoryReference.end())
          return it->second;
        return triton::engines::symbolic::UNSET;
      }


      /* Returns the symbolic variable otherwise returns nullptr */
      SymbolicVariable* SymbolicEngine::getSymbolicVariableFromId(triton::__uint symVarId) {
        if (this->symbolicVariables.find(symVarId) == this->symbolicVariables.end())
          return nullptr;
        return this->symbolicVariables[symVarId];
      }


      /* Returns the symbolic variable otherwise returns nullptr */
      SymbolicVariable* SymbolicEngine::getSymbolicVariableFromName(std::string& symVarName) {
        std::map<triton::__uint, SymbolicVariable*>::iterator it;

        for (it = this->symbolicVariables.begin(); it != this->symbolicVariables.end(); it++) {
          if (it->second->getSymVarName() == symVarName)
            return it->second;
        }
        return nullptr;
      }


      /* Returns all symbolic variables */
      std::map<triton::__uint, SymbolicVariable*>& SymbolicEngine::getSymbolicVariables(void) {
        return this->symbolicVariables;
      }


      /* Return the reg reference or UNSET */
      triton::__uint SymbolicEngine::getSymbolicRegisterId(triton::arch::RegisterOperand& reg) {
        triton::uint32 parentId = reg.getParent().getId();
        if (!triton::api.isCpuRegValid(parentId))
          return triton::engines::symbolic::UNSET;
        return this->symbolicReg[parentId];
      }


      /* Create a new symbolic expression */
      /* Get an unique id.
       * Mainly used when a new symbolic expression is created */
      triton::__uint SymbolicEngine::getUniqueSymExprId(void) {
        return this->uniqueSymExprId++;
      }


      /* Create a new symbolic variable */
      /* Get an unique id.
       * Mainly used when a new symbolic variable is created */
      triton::__uint SymbolicEngine::getUniqueSymVarId(void) {
        return this->uniqueSymVarId++;
      }


      /* Create a new symbolic expression with comment */
      SymbolicExpression* SymbolicEngine::newSymbolicExpression(smt2lib::smtAstAbstractNode* node, triton::engines::symbolic::symkind_e kind, std::string comment) {
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
          for (triton::uint32 i = 0; i < this->numberOfReg; i++) {
            if (this->symbolicReg[i] == symExprId) {
              this->symbolicReg[i] = triton::engines::symbolic::UNSET;
              return;
            }
          }

          /* Concretize the memory if it exists */
          for (it = this->memoryReference.begin(); it != memoryReference.end(); it++) {
            if (it->second == symExprId) {
              this->memoryReference.erase(it->first);
              return;
            }
          }
        }

      }


      /* Get the symbolic expression pointer from a symbolic id */
      SymbolicExpression* SymbolicEngine::getSymbolicExpressionFromId(triton::__uint symExprId) {
        if (this->symbolicExpressions.find(symExprId) == this->symbolicExpressions.end())
          throw std::runtime_error("SymbolicEngine::getSymbolicExpressionFromId(): symbolic expression id not found");
        return this->symbolicExpressions[symExprId];
      }


      /* Returns all symbolic expressions */
      std::map<triton::__uint, SymbolicExpression*>& SymbolicEngine::getSymbolicExpressions(void) {
        return this->symbolicExpressions;
      }


      /* Returns the full symbolic expression backtracked. */
      smt2lib::smtAstAbstractNode* SymbolicEngine::getFullAst(smt2lib::smtAstAbstractNode* node) {
        std::vector<smt2lib::smtAstAbstractNode*>& childs = node->getChilds();

        for (triton::uint32 index = 0; index < childs.size(); index++) {
          if (childs[index]->getKind() == smt2lib::REFERENCE_NODE) {
            triton::__uint id = reinterpret_cast<smt2lib::smtAstReferenceNode*>(childs[index])->getValue();
            smt2lib::smtAstAbstractNode* ref = this->getSymbolicExpressionFromId(id)->getAst();
            childs[index] = ref;
          }
          this->getFullAst(childs[index]);
        }

        return node;
      }


      /* Returns a list which contains all tainted expressions */
      std::list<SymbolicExpression*> SymbolicEngine::getTaintedSymbolicExpressions(void) {
        std::map<triton::__uint, SymbolicExpression*>::iterator it;
        std::list<SymbolicExpression*> taintedExprs;

        for (it = this->symbolicExpressions.begin(); it != this->symbolicExpressions.end(); it++) {
          if (it->second->isTainted == true)
            taintedExprs.push_back(it->second);
        }
        return taintedExprs;
      }


      /* Returns the list of the symbolic variables declared in the trace */
      std::string SymbolicEngine::getVariablesDeclaration(void) {
        std::map<triton::__uint, SymbolicVariable*>::iterator it;
        std::stringstream stream;

        for(it = this->symbolicVariables.begin(); it != this->symbolicVariables.end(); it++)
          stream << smt2lib::declare(it->second->getSymVarName(), it->second->getSymVarSize());

        return stream.str();
      }


      /*
       * Converts an expression id to a symbolic variable.
       * e.g:
       * #43 = (_ bv10 8)
       * convertExprToSymVar(43, 8)
       * #43 = SymVar_4
       */
      SymbolicVariable* SymbolicEngine::convertExprToSymVar(triton::__uint exprId, triton::uint32 symVarSize, std::string symVarComment) {
        SymbolicVariable* symVar = nullptr;
        SymbolicExpression* expression = this->getSymbolicExpressionFromId(exprId);

        symVar = this->addSymbolicVariable(triton::engines::symbolic::UNDEF, 0, symVarSize, symVarComment);
        expression->setAst(smt2lib::variable(symVar->getSymVarName()));

        return symVar;
      }


      /* The memory size is used to define the symbolic variable's size. */
      SymbolicVariable* SymbolicEngine::convertMemToSymVar(triton::arch::MemoryOperand& mem, std::string symVarComment)
      {
        SymbolicVariable* symVar         = nullptr;
        SymbolicExpression* expression   = nullptr;
        smt2lib::smtAstAbstractNode* tmp = nullptr;
        triton::__uint memSymId          = triton::engines::symbolic::UNSET;
        triton::__uint memAddr           = mem.getAddress();
        triton::uint32 symVarSize        = mem.getSize();
        triton::uint32 size_quotient     = symVarSize;
        triton::uint128 cv               = mem.getConcreteValue();

        memSymId = this->getSymbolicMemoryId(memAddr);

        // First we create a symbolic variable
        symVar = this->addSymbolicVariable(triton::engines::symbolic::MEM, memAddr, symVarSize * BYTE_SIZE_BIT, symVarComment);
        smt2lib::smtAstAbstractNode* symVarNode = smt2lib::variable(symVar->getSymVarName());

        if (symVarNode == nullptr)
          throw std::runtime_error("SymbolicEngine::convertMemToSymVar(): Can't create smtAstAbstractNode (nullptr)");

        /* Split expression in bytes */
        std::list<smt2lib::smtAstAbstractNode*> symMemChunk;
        while (size_quotient) {
            tmp = smt2lib::extract(((BYTE_SIZE_BIT * size_quotient) - 1), ((BYTE_SIZE_BIT * size_quotient) - BYTE_SIZE_BIT), symVarNode);
            symMemChunk.push_back(tmp);

            if (tmp == nullptr)
              throw std::runtime_error("SymbolicEngine::convertMemToSymVar(): Can't create extract (nullptr)");

            if (memSymId == triton::engines::symbolic::UNSET) {
              if (size_quotient > 1 or symVarSize == 1) {
                expression = this->newSymbolicExpression(tmp, triton::engines::symbolic::MEM, "byte reference");
              }
              else {
                smt2lib::smtAstAbstractNode* concat = smt2lib::concat(symMemChunk);
                expression = this->newSymbolicExpression(concat, triton::engines::symbolic::MEM);
              }
            }
            else {
              expression = this->getSymbolicExpressionFromId(memSymId);
              expression->setAst(tmp);
            }

            if (expression == nullptr)
              throw std::runtime_error("SymbolicEngine::convertMemToSymVar(): Can't create symbolic expression (nullptr)");

            this->addMemoryReference((memAddr + size_quotient) - 1, expression->getId());

            size_quotient--;
        }

        /* Setup the concrete value to the symbolic variable */
        if (cv == 0)
          symVar->setSymVarConcreteValue(triton::api.getLastMemoryValue(mem));
        else
          symVar->setSymVarConcreteValue(cv);

        return symVar;
      }


      SymbolicVariable* SymbolicEngine::convertRegToSymVar(triton::arch::RegisterOperand& reg, std::string symVarComment) {
        SymbolicVariable* symVar        = nullptr;
        SymbolicExpression* expression  = nullptr;
        triton::__uint regSymId         = triton::engines::symbolic::UNSET;
        triton::uint32 parentId         = reg.getParent().getId();
        triton::uint32 symVarSize       = reg.getBitSize();
        triton::uint128 cv              = reg.getConcreteValue();

        if (!triton::api.isCpuRegValid(parentId))
          throw std::runtime_error("SymbolicEngine::convertRegToSymVar(): Invalid register id");

        regSymId = this->getSymbolicRegisterId(reg);
        if (regSymId == triton::engines::symbolic::UNSET) {
          symVar = this->addSymbolicVariable(triton::engines::symbolic::REG, parentId, symVarSize, symVarComment);

          smt2lib::smtAstAbstractNode* tmp = smt2lib::variable(symVar->getSymVarName());
          if (tmp == nullptr)
            throw std::runtime_error("SymbolicEngine::convertRegToSymVar(): Can't create smtAstAbstractNode (nullptr)");

          SymbolicExpression* se = this->newSymbolicExpression(tmp, triton::engines::symbolic::REG);
          if (se == nullptr)
            throw std::runtime_error("SymbolicEngine::convertRegToSymVar(): Can't create symbolic expression (nullptr)");

          this->symbolicReg[parentId] = se->getId();
        }

        else {
          expression = this->getSymbolicExpressionFromId(regSymId);
          symVar = this->addSymbolicVariable(triton::engines::symbolic::REG, parentId, symVarSize, symVarComment);
          expression->setAst(smt2lib::variable(symVar->getSymVarName()));
        }

        /* Setup the concrete value to the symbolic variable */
        if (cv == 0)
          symVar->setSymVarConcreteValue(triton::api.getLastRegisterValue(reg));
        else
          symVar->setSymVarConcreteValue(cv);

        return symVar;
      }


      /* Add a new symbolic variable */
      SymbolicVariable* SymbolicEngine::addSymbolicVariable(triton::engines::symbolic::symkind_e kind, triton::__uint kindValue, triton::uint32 size, std::string comment) {
        triton::__uint uniqueId  = this->getUniqueSymVarId();
        SymbolicVariable* symVar = new SymbolicVariable(kind, kindValue, uniqueId, size, comment);

        if (symVar == nullptr)
          throw std::runtime_error("SymbolicEngine::addSymbolicVariable(): Cannot allocate a new symbolic variable");

        this->symbolicVariables[uniqueId] = symVar;
        return symVar;
      }


      /* Returns an immediate symbolic operand */
      smt2lib::smtAstAbstractNode* SymbolicEngine::buildSymbolicImmediateOperand(triton::arch::ImmediateOperand& imm) {
        smt2lib::smtAstAbstractNode* node = smt2lib::bv(imm.getValue(), imm.getBitSize());
        return node;
      }


      /* Returns a symbolic memory operand */
      smt2lib::smtAstAbstractNode* SymbolicEngine::buildSymbolicMemoryOperand(triton::arch::MemoryOperand& mem) {
        std::list<smt2lib::smtAstAbstractNode*> opVec;

        smt2lib::smtAstAbstractNode* tmp         = nullptr;
        triton::__uint address                   = mem.getAddress();
        triton::__uint size                      = mem.getSize();
        triton::__uint symMem                    = triton::engines::symbolic::UNSET;
        triton::uint8 concreteValue[DQWORD_SIZE] = {0};
        triton::uint128 value                    = triton::api.getLastMemoryValue(mem);

        triton::fromUint128ToBuffer(value, concreteValue);

        while (size) {
          symMem = this->getSymbolicMemoryId(address + size - 1);
          if (symMem != triton::engines::symbolic::UNSET) {
            tmp = smt2lib::reference(symMem);
            opVec.push_back(smt2lib::extract((BYTE_SIZE_BIT - 1), 0, tmp));
          }
          else {
            tmp = smt2lib::bv(concreteValue[size - 1], BYTE_SIZE_BIT);
            opVec.push_back(smt2lib::extract((BYTE_SIZE_BIT - 1), 0, tmp));
          }
          size--;
        }

        switch (opVec.size()) {
          case DQWORD_SIZE:
          case QWORD_SIZE:
          case DWORD_SIZE:
          case WORD_SIZE:
            tmp = smt2lib::concat(opVec);
            break;
          case BYTE_SIZE:
            tmp = opVec.front();
            break;
        }

        return tmp;
      }


      /* Returns a symbolic register operand */
      smt2lib::smtAstAbstractNode* SymbolicEngine::buildSymbolicRegisterOperand(triton::arch::RegisterOperand& reg) {
        smt2lib::smtAstAbstractNode* op = nullptr;
        triton::__uint symReg           = this->getSymbolicRegisterId(reg);
        triton::uint32 bvSize           = reg.getBitSize();
        triton::uint32 high             = reg.getHigh();
        triton::uint32 low              = reg.getLow();

        if (symReg != triton::engines::symbolic::UNSET)
          op = smt2lib::extract(high, low, smt2lib::reference(symReg));
        else
          op = smt2lib::bv(triton::api.getLastRegisterValue(reg), bvSize);

        return op;
      }


      /* Returns the new symbolic memory expression */
      SymbolicExpression* SymbolicEngine::createSymbolicMemoryExpression(triton::arch::Instruction& inst, smt2lib::smtAstAbstractNode* node, triton::arch::MemoryOperand& mem, std::string comment) {
        smt2lib::smtAstAbstractNode*            tmp;
        std::list<smt2lib::smtAstAbstractNode*> ret;

        SymbolicExpression* se   = nullptr;
        triton::__uint address   = mem.getAddress();
        triton::__uint writeSize = mem.getSize();

        /*
         * As the x86's memory can be accessed without alignment, each byte of the
         * memory must be assigned to an unique reference.
         */
        while (writeSize) {
          /* Extract each byte of the memory */
          tmp = smt2lib::extract(((writeSize * BYTE_SIZE_BIT) - 1), ((writeSize * BYTE_SIZE_BIT) - BYTE_SIZE_BIT), node);
          se = this->newSymbolicExpression(tmp, triton::engines::symbolic::MEM, "byte reference - " + comment);
          ret.push_back(tmp);
          inst.addSymbolicExpression(se);
          /* Assign memory with little endian */
          this->addMemoryReference((address + writeSize) - 1, se->getId());
          writeSize--;
        }

        /* If there is only one reference, we return the symbolic expression */
        if (ret.size() == 1)
          return se;

        /* Otherwise, we return the concatenation of all symbolic expressions */
        se = this->newSymbolicExpression(smt2lib::concat(ret), triton::engines::symbolic::MEM, "concat reference - " + comment);
        inst.addSymbolicExpression(se);
        return se;
      }


      /* Returns the new symbolic register expression */
      SymbolicExpression* SymbolicEngine::createSymbolicRegisterExpression(triton::arch::Instruction& inst, smt2lib::smtAstAbstractNode* node, triton::arch::RegisterOperand& reg, std::string comment) {
        smt2lib::smtAstAbstractNode* finalExpr  = nullptr;
        smt2lib::smtAstAbstractNode* origReg    = nullptr;
        triton::__uint regSize                  = reg.getSize();
        triton::arch::RegisterOperand parentReg = reg.getParent();

        if (reg.isFlag())
          throw std::runtime_error("SymbolicEngine::createSymbolicRegisterExpression(): The register cannot be a flag.");

        origReg = this->buildSymbolicRegisterOperand(parentReg);

        switch (regSize) {
          case BYTE_SIZE:
            if (reg.getLow() == 0) {
              finalExpr = smt2lib::concat(smt2lib::extract((triton::api.cpuRegBitSize() - 1), BYTE_SIZE_BIT, origReg), node);
            }
            else {
              finalExpr = smt2lib::concat(
                            smt2lib::extract((triton::api.cpuRegBitSize() - 1), WORD_SIZE_BIT, origReg),
                            smt2lib::concat(node, smt2lib::extract((BYTE_SIZE_BIT - 1), 0, origReg))
                          );
            }
            break;

          case WORD_SIZE:
            finalExpr = smt2lib::concat(smt2lib::extract((triton::api.cpuRegBitSize() - 1), WORD_SIZE_BIT, origReg), node);
            break;

          case DWORD_SIZE:
            /* In AMD64, if a reg32 is written, it clears the 32-bit MSB of the corresponding register (Thx Wisk!) */
            if (triton::api.getArchitecture() == triton::arch::ARCH_X86_64) {
              finalExpr = smt2lib::zx(DWORD_SIZE_BIT, node);
              break;
            }

          case QWORD_SIZE:
          case DQWORD_SIZE:
            finalExpr = node;
            break;
        }

        triton::engines::symbolic::SymbolicExpression* se = this->newSymbolicExpression(finalExpr, triton::engines::symbolic::REG, comment);
        this->assignSymbolicExpressionToRegister(se, parentReg);
        inst.addSymbolicExpression(se);

        return se;
      }


      /* Returns the new symbolic flag expression */
      SymbolicExpression* SymbolicEngine::createSymbolicFlagExpression(triton::arch::Instruction& inst, smt2lib::smtAstAbstractNode* node, triton::arch::RegisterOperand& flag, std::string comment) {
        if (!flag.isFlag())
          throw std::runtime_error("SymbolicEngine::createSymbolicFlagExpression(): The register must be a flag.");
        triton::engines::symbolic::SymbolicExpression *se = this->newSymbolicExpression(node, triton::engines::symbolic::REG, comment);
        this->assignSymbolicExpressionToRegister(se, flag);
        inst.addSymbolicExpression(se);
        return se;
      }


      /* Returns the new symbolic volatile expression */
      SymbolicExpression* SymbolicEngine::createSymbolicVolatileExpression(triton::arch::Instruction& inst, smt2lib::smtAstAbstractNode* node, std::string comment) {
        triton::engines::symbolic::SymbolicExpression* se = this->newSymbolicExpression(node, triton::engines::symbolic::UNDEF, comment);
        inst.addSymbolicExpression(se);
        return se;
      }


      /* Add and assign a new memory reference */
      void SymbolicEngine::addMemoryReference(triton::__uint mem, triton::__uint id) {
        this->memoryReference[mem] = id;
      }


      /* Assigns a symbolic expression to a register */
      bool SymbolicEngine::assignSymbolicExpressionToRegister(SymbolicExpression *se, triton::arch::RegisterOperand& reg) {
        triton::arch::RegisterOperand parent = reg.getParent();
        triton::uint32 id = parent.getId();

        /* We can assign an expression only on parent registers */
        if (parent.isValid()) {
          se->setKind(triton::engines::symbolic::REG);
          this->symbolicReg[id] = se->getId();
          return true;
        }

        return false;
      }


      /* Returns true if the symbolic engine is enable. Otherwise returns false. */
      bool SymbolicEngine::isEnabled(void) {
        return this->enableFlag;
      }


      /* Returns true if the symbolic expression ID exists. */
      bool SymbolicEngine::isSymbolicExpressionIdExists(triton::__uint symExprId) {
        if (this->symbolicExpressions.find(symExprId) != this->symbolicExpressions.end())
          return true;
        return false;
      }


      /* Enables or disables the symbolic engine */
      void SymbolicEngine::enable(bool flag) {
        this->enableFlag = flag;
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */

