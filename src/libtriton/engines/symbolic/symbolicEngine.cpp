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



namespace triton {
  namespace engines {
    namespace symbolic {

      SymbolicEngine::SymbolicEngine(triton::arch::Architecture* architecture,
                                     const triton::modes::SharedModes& modes,
                                     const triton::ast::SharedAstContext& astCtxt,
                                     triton::callbacks::Callbacks* callbacks)
        : triton::engines::symbolic::SymbolicSimplification(callbacks),
          triton::engines::symbolic::PathManager(modes, astCtxt),
          astCtxt(astCtxt),
          modes(modes) {

        if (architecture == nullptr)
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::SymbolicEngine(): The architecture pointer must be valid.");

        this->architecture      = architecture;
        this->callbacks         = callbacks;
        this->enableFlag        = true;
        this->numberOfRegisters = this->architecture->numberOfRegisters();
        this->uniqueSymExprId   = 0;
        this->uniqueSymVarId    = 0;

        this->symbolicReg.resize(this->numberOfRegisters);
      }


      SymbolicEngine::SymbolicEngine(const SymbolicEngine& other)
        : triton::engines::symbolic::SymbolicSimplification(other),
          triton::engines::symbolic::PathManager(other),
          astCtxt(other.astCtxt),
          modes(other.modes) {

        this->alignedMemoryReference      = other.alignedMemoryReference;
        this->architecture                = other.architecture;
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


      SymbolicEngine& SymbolicEngine::operator=(const SymbolicEngine& other) {
        triton::engines::symbolic::SymbolicSimplification::operator=(other);
        triton::engines::symbolic::PathManager::operator=(other);

        this->alignedMemoryReference      = other.alignedMemoryReference;
        this->architecture                = other.architecture;
        this->astCtxt                     = other.astCtxt;
        this->callbacks                   = other.callbacks;
        this->enableFlag                  = other.enableFlag;
        this->memoryReference             = other.memoryReference;
        this->modes                       = other.modes;
        this->numberOfRegisters           = other.numberOfRegisters;
        this->symbolicExpressions         = other.symbolicExpressions;
        this->symbolicReg                 = other.symbolicReg;
        this->symbolicVariables           = other.symbolicVariables;
        this->uniqueSymExprId             = other.uniqueSymExprId;
        this->uniqueSymVarId              = other.uniqueSymVarId;

        return *this;
      }


      /*
       * Concretize a register. If the register is setup as nullptr, the next assignment
       * will be over the concretization. This method must be called before symbolic
       * processing.
       */
      void SymbolicEngine::concretizeRegister(const triton::arch::Register& reg) {
        triton::arch::register_e parentId = reg.getParent();

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
        this->removeAlignedMemory(addr, BYTE_SIZE);
      }


      /* Same as concretizeMemory but with all address memory */
      void SymbolicEngine::concretizeAllMemory(void) {
        this->memoryReference.clear();
        this->alignedMemoryReference.clear();
      }


      /* Gets an aligned entry. */
      inline SharedSymbolicExpression SymbolicEngine::getAlignedMemory(triton::uint64 address, triton::uint32 size) {
        return this->alignedMemoryReference[std::make_pair(address, size)].lock();
      }


      /* Checks if the aligned memory is recored. */
      bool SymbolicEngine::isAlignedMemory(triton::uint64 address, triton::uint32 size) {
        if (this->alignedMemoryReference.find(std::make_pair(address, size)) != this->alignedMemoryReference.end()) {
          /* Also check if the symbolic expression is alive */
          if (this->alignedMemoryReference[std::make_pair(address, size)].lock()) {
            return true;
          }
          /* Also check if the symbolic expression is alive */
          else {
            this->removeAlignedMemory(address, size);
          }
        }
        return false;
      }


      /* Adds an aligned memory */
      void SymbolicEngine::addAlignedMemory(triton::uint64 address, triton::uint32 size, const SharedSymbolicExpression& expr) {
        this->removeAlignedMemory(address, size);
        if (!(this->modes->isModeEnabled(triton::modes::ONLY_ON_SYMBOLIZED) && expr->getAst()->isSymbolized() == false))
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
      SharedSymbolicVariable SymbolicEngine::getSymbolicVariable(triton::usize symVarId) const {
        auto it = this->symbolicVariables.find(symVarId);
        if (it == this->symbolicVariables.end())
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::getSymbolicVariable(): Unregistred symbolic variable.");

        if (auto node = it->second.lock())
          return node;
        else
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::getSymbolicVariable(): This symbolic variable is dead.");
      }


      /* Returns the symbolic variable otherwise returns nullptr */
      SharedSymbolicVariable SymbolicEngine::getSymbolicVariable(const std::string& symVarName) const {
        /*
         * FIXME: When there is a ton of symvar, this loop takes a while to go through.
         *        What about adding two maps {id:symvar} and {string:symvar}? See #648.
         */
        for (auto& sv: this->symbolicVariables) {
          if (auto symVar = sv.second.lock()) {
            if (symVar->getName() == symVarName) {
              return symVar;
            }
          }
        }
        throw triton::exceptions::SymbolicEngine("SymbolicEngine::getSymbolicVariable(): Unregistred or dead symbolic variable.");
      }


      /* Returns all symbolic variables */
      std::unordered_map<triton::usize, SharedSymbolicVariable> SymbolicEngine::getSymbolicVariables(void) const {
        // Copy and clean up dead weak ref
        std::unordered_map<triton::usize, SharedSymbolicVariable> ret;
        std::vector<triton::usize> toRemove;

        for (auto& kv : this->symbolicVariables) {
          if (auto sp = kv.second.lock()) {
            ret[kv.first] = sp;
          } else {
            toRemove.push_back(kv.first);
          }
        }

        for (auto id : toRemove)
          this->symbolicVariables.erase(id);

        return ret;
      }


      /* Returns the shared symbolic expression corresponding to the register */
      const SharedSymbolicExpression& SymbolicEngine::getSymbolicRegister(const triton::arch::Register& reg) const {
        triton::arch::register_e parentId = reg.getParent();

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
        const triton::ast::SharedAbstractNode& node = this->getMemoryAst(mem);
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
      SharedSymbolicExpression SymbolicEngine::newSymbolicExpression(const triton::ast::SharedAbstractNode& node, triton::engines::symbolic::expression_e type, const std::string& comment) {
        /* Each symbolic expression must have an unique id */
        triton::usize id = this->getUniqueSymExprId();

        /* Performes transformation if there are rules recorded */
        const triton::ast::SharedAbstractNode& snode = this->processSimplification(node);

        /* Allocates the new shared symbolic expression */
        SharedSymbolicExpression expr = std::make_shared<SymbolicExpression>(snode, id, type, comment);
        if (expr == nullptr)
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::newSymbolicExpression(): not enough memory");

        /* Save and returns the new shared symbolic expression */
        this->symbolicExpressions[id] = expr;
        return expr;
      }


      /* Removes the symbolic expression corresponding to the id */
      void SymbolicEngine::removeSymbolicExpression(triton::usize symExprId) {
        if (this->symbolicExpressions.find(symExprId) != this->symbolicExpressions.end()) {
          /* Remove aligned memory */
          auto expr = this->getSymbolicExpression(symExprId);
          if (expr->getType() == MEMORY_EXPRESSION) {
            auto mem = expr->getOriginMemory();
            this->removeAlignedMemory(mem.getAddress(), mem.getSize());
          }

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
        }
      }


      /* Gets the shared symbolic expression from a symbolic id */
      SharedSymbolicExpression SymbolicEngine::getSymbolicExpression(triton::usize symExprId) const {
        auto it = this->symbolicExpressions.find(symExprId);
        if (it == this->symbolicExpressions.end())
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::getSymbolicExpression(): symbolic expression id not found");

        if (auto sp = it->second.lock())
          return sp;

        this->symbolicExpressions.erase(symExprId);
        throw triton::exceptions::SymbolicEngine("SymbolicEngine::getSymbolicExpression(): symbolic expression is not available anymore");
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


      /* Slices all expressions from a given one */
      std::map<triton::usize, SharedSymbolicExpression> SymbolicEngine::sliceExpressions(const SharedSymbolicExpression& expr) {
        std::map<triton::usize, SharedSymbolicExpression> exprs;

        if (expr == nullptr)
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::sliceExpressions(): expr cannot be null.");

        exprs[expr->getId()] = expr;
        auto worklist = triton::ast::childrenExtraction(expr->getAst(), true /* unroll */, false /* revert */);

        for (auto&& n : worklist) {
          if (n->getType() == triton::ast::REFERENCE_NODE) {
            auto expr  = reinterpret_cast<triton::ast::ReferenceNode*>(n.get())->getSymbolicExpression();
            auto eid   = expr->getId();
            exprs[eid] = expr;
          }
        }

        return exprs;
      }


      /* Returns a list which contains all tainted expressions */
      std::vector<SharedSymbolicExpression> SymbolicEngine::getTaintedSymbolicExpressions(void) const {
        std::vector<SharedSymbolicExpression> taintedExprs;
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
      std::map<triton::arch::register_e, SharedSymbolicExpression> SymbolicEngine::getSymbolicRegisters(void) const {
        std::map<triton::arch::register_e, SharedSymbolicExpression> ret;

        for (triton::uint32 it = 0; it < this->numberOfRegisters; it++) {
          if (this->symbolicReg[it] != nullptr) {
            ret[triton::arch::register_e(it)] = this->symbolicReg[it];
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
       * symbolizeExpression(43, 8)
       * #43 = SymVar_4
       */
      SharedSymbolicVariable SymbolicEngine::symbolizeExpression(triton::usize exprId, triton::uint32 symVarSize, const std::string& symVarComment) {
        const SharedSymbolicExpression& expression = this->getSymbolicExpression(exprId);
        const SharedSymbolicVariable& symVar       = this->newSymbolicVariable(UNDEFINED_VARIABLE, 0, symVarSize, symVarComment);
        const triton::ast::SharedAbstractNode& tmp = this->astCtxt->variable(symVar);

        if (expression->getAst())
           this->setConcreteVariableValue(symVar, expression->getAst()->evaluate());

        expression->setAst(tmp);

        return symVar;
      }


      /* The memory size is used to define the symbolic variable's size. */
      SharedSymbolicVariable SymbolicEngine::symbolizeMemory(const triton::arch::MemoryAccess& mem, const std::string& symVarComment) {
        triton::uint64 memAddr    = mem.getAddress();
        triton::uint32 symVarSize = mem.getSize();
        triton::uint512 cv        = this->architecture->getConcreteMemoryValue(mem);

        /* First we create a symbolic variable */
        const SharedSymbolicVariable& symVar = this->newSymbolicVariable(MEMORY_VARIABLE, memAddr, symVarSize * BYTE_SIZE_BIT, symVarComment);

        /* Create the AST node */
        const triton::ast::SharedAbstractNode& symVarNode = this->astCtxt->variable(symVar);

        /* Setup the concrete value to the symbolic variable */
        this->setConcreteVariableValue(symVar, cv);

        /* Record the aligned symbolic variable for a symbolic optimization */
        if (this->modes->isModeEnabled(triton::modes::ALIGNED_MEMORY)) {
          const SharedSymbolicExpression& se = this->newSymbolicExpression(symVarNode, MEMORY_EXPRESSION, "aligned Byte reference");
          se->setOriginMemory(mem);
          this->addAlignedMemory(memAddr, symVarSize, se);
        }

        /*  Split expression in bytes */
        for (triton::sint32 index = symVarSize-1; index >= 0; index--) {
          triton::uint32 high = ((BYTE_SIZE_BIT * (index + 1)) - 1);
          triton::uint32 low  = ((BYTE_SIZE_BIT * (index + 1)) - BYTE_SIZE_BIT);

          /* Isolate the good part of the symbolic variable */
          const triton::ast::SharedAbstractNode& tmp = this->astCtxt->extract(high, low, symVarNode);

          /* Create a new symbolic expression containing the symbolic variable */
          const SharedSymbolicExpression& se = this->newSymbolicExpression(tmp, MEMORY_EXPRESSION, "Byte reference");
          se->setOriginMemory(triton::arch::MemoryAccess(memAddr+index, BYTE_SIZE));

          /* Assign the symbolic expression to the memory cell */
          this->addMemoryReference(memAddr+index, se);
        }

        return symVar;
      }


      SharedSymbolicVariable SymbolicEngine::symbolizeRegister(const triton::arch::Register& reg, const std::string& symVarComment) {
        const triton::arch::Register& parent  = this->architecture->getRegister(reg.getParent());
        triton::uint32 symVarSize             = reg.getBitSize();
        triton::uint512 cv                    = this->architecture->getConcreteRegisterValue(reg);

        if (!this->architecture->isRegisterValid(parent.getId()))
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::symbolizeRegister(): Invalid register id");

        if (reg.isMutable() == false)
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::symbolizeRegister(): This register is immutable");

        /* Create the symbolic variable */
        const SharedSymbolicVariable& symVar = this->newSymbolicVariable(REGISTER_VARIABLE, reg.getId(), symVarSize, symVarComment);

        /* Create the AST node */
        const triton::ast::SharedAbstractNode& tmp = this->insertSubRegisterInParent(reg, this->astCtxt->variable(symVar), false);

        /* Setup the concrete value to the symbolic variable */
        this->setConcreteVariableValue(symVar, cv);

        /* Create a new symbolic expression containing the symbolic variable */
        const SharedSymbolicExpression& se = this->newSymbolicExpression(tmp, REGISTER_EXPRESSION);

        /* Assign the symbolic expression to the register */
        this->assignSymbolicExpressionToRegister(se, parent);

        return symVar;
      }


      /* Adds a new symbolic variable */
      SharedSymbolicVariable SymbolicEngine::newSymbolicVariable(triton::engines::symbolic::variable_e type, triton::uint64 origin, triton::uint32 size, const std::string& comment) {
        triton::usize uniqueId = this->getUniqueSymVarId();

        SharedSymbolicVariable symVar = std::make_shared<SymbolicVariable>(type, origin, uniqueId, size, comment);
        if (symVar == nullptr)
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::newSymbolicVariable(): Cannot allocate a new symbolic variable");

        this->symbolicVariables[uniqueId] = symVar;
        return symVar;
      }


      /* Returns the AST corresponding to the operand. */
      triton::ast::SharedAbstractNode SymbolicEngine::getOperandAst(const triton::arch::OperandWrapper& op) {
        switch (op.getType()) {
          case triton::arch::OP_IMM: return this->getImmediateAst(op.getConstImmediate());
          case triton::arch::OP_MEM: return this->getMemoryAst(op.getConstMemory());
          case triton::arch::OP_REG: return this->getRegisterAst(op.getConstRegister());
          default:
            throw triton::exceptions::SymbolicEngine("SymbolicEngine::getOperandAst(): Invalid operand.");
        }
      }


      /* Returns the AST corresponding to the operand. */
      triton::ast::SharedAbstractNode SymbolicEngine::getOperandAst(triton::arch::Instruction& inst, const triton::arch::OperandWrapper& op) {
        switch (op.getType()) {
          case triton::arch::OP_IMM: return this->getImmediateAst(inst, op.getConstImmediate());
          case triton::arch::OP_MEM: return this->getMemoryAst(inst, op.getConstMemory());
          case triton::arch::OP_REG: return this->getRegisterAst(inst, op.getConstRegister());
          default:
            throw triton::exceptions::SymbolicEngine("SymbolicEngine::getOperandAst(): Invalid operand.");
        }
      }


      triton::ast::SharedAbstractNode SymbolicEngine::getShiftAst(triton::arch::aarch64::shift_e type, triton::uint32 value, const triton::ast::SharedAbstractNode& node) {
        switch (type) {
          case triton::arch::aarch64::ID_SHIFT_ASR:
            return this->astCtxt->bvashr(node, this->astCtxt->bv(value, node->getBitvectorSize()));

          case triton::arch::aarch64::ID_SHIFT_LSL:
            return this->astCtxt->bvshl(node, this->astCtxt->bv(value, node->getBitvectorSize()));

          case triton::arch::aarch64::ID_SHIFT_LSR:
            return this->astCtxt->bvlshr(node, this->astCtxt->bv(value, node->getBitvectorSize()));

          case triton::arch::aarch64::ID_SHIFT_ROR:
            return this->astCtxt->bvror(node, value);

          default:
            throw triton::exceptions::SymbolicEngine("SymbolicEngine::getShiftAst(): Invalid shift operand.");
        }
      }


      triton::ast::SharedAbstractNode SymbolicEngine::getExtendAst(triton::arch::aarch64::extend_e type, triton::uint32 size, const triton::ast::SharedAbstractNode& node) {
        switch (type) {
          case triton::arch::aarch64::ID_EXTEND_UXTB:
            return this->astCtxt->zx(size, this->astCtxt->extract(7, 0, node));

          case triton::arch::aarch64::ID_EXTEND_UXTH:
            return this->astCtxt->zx(size, this->astCtxt->extract(15, 0, node));

          case triton::arch::aarch64::ID_EXTEND_UXTW:
            return this->astCtxt->zx(size, this->astCtxt->extract(31, 0, node));

          case triton::arch::aarch64::ID_EXTEND_UXTX:
            return this->astCtxt->zx(size, this->astCtxt->extract(63, 0, node));

          case triton::arch::aarch64::ID_EXTEND_SXTB:
            return this->astCtxt->sx(size, this->astCtxt->extract(7, 0, node));

          case triton::arch::aarch64::ID_EXTEND_SXTH:
            return this->astCtxt->sx(size, this->astCtxt->extract(15, 0, node));

          case triton::arch::aarch64::ID_EXTEND_SXTW:
            return this->astCtxt->sx(size, this->astCtxt->extract(31, 0, node));

          case triton::arch::aarch64::ID_EXTEND_SXTX:
            return this->astCtxt->sx(size, this->astCtxt->extract(63, 0, node));

          default:
            throw triton::exceptions::SymbolicEngine("SymbolicEngine::getExtendAst(): Invalid extend operand.");
        }
      }


      /* Returns the AST corresponding to the immediate */
      triton::ast::SharedAbstractNode SymbolicEngine::getImmediateAst(const triton::arch::Immediate& imm) {
        triton::ast::SharedAbstractNode node = this->astCtxt->bv(imm.getValue(), imm.getBitSize());

        /* Shift AST if it's a shift operand */
        if (imm.getShiftType() != triton::arch::aarch64::ID_SHIFT_INVALID)
          return this->getShiftAst(imm.getShiftType(), imm.getShiftValue(), node);

        return node;
      }


      /* Returns the AST corresponding to the immediate and defines the immediate as input of the instruction */
      triton::ast::SharedAbstractNode SymbolicEngine::getImmediateAst(triton::arch::Instruction& inst, const triton::arch::Immediate& imm) {
        triton::ast::SharedAbstractNode node = this->getImmediateAst(imm);
        inst.setReadImmediate(imm, node);
        return node;
      }


      /* Returns the AST corresponding to the memory */
      triton::ast::SharedAbstractNode SymbolicEngine::getMemoryAst(const triton::arch::MemoryAccess& mem) {
        std::vector<triton::ast::SharedAbstractNode> opVec;

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
        if (this->modes->isModeEnabled(triton::modes::ALIGNED_MEMORY) && this->isAlignedMemory(address, size)) {
          triton::ast::SharedAbstractNode anode = this->getAlignedMemory(address, size)->getAst();
          return anode;
        }

        /* Iterate on every memory cells to use their symbolic or concrete values */
        while (size) {
          const SharedSymbolicExpression& symMem = this->getSymbolicMemory(address + size - 1);
          /* Check if the memory cell is already symbolic */
          if (symMem != nullptr) {
            tmp = this->astCtxt->reference(symMem);
            opVec.push_back(this->astCtxt->extract((BYTE_SIZE_BIT - 1), 0, tmp));
          }
          /* Otherwise, use the concerte value */
          else {
            tmp = this->astCtxt->bv(concreteValue[size - 1], BYTE_SIZE_BIT);
            opVec.push_back(this->astCtxt->extract((BYTE_SIZE_BIT - 1), 0, tmp));
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
            tmp = this->astCtxt->concat(opVec);
            break;
          case BYTE_SIZE:
            tmp = opVec.front();
            break;
        }

        return tmp;
      }


      /* Returns the AST corresponding to the memory and defines the memory as input of the instruction */
      triton::ast::SharedAbstractNode SymbolicEngine::getMemoryAst(triton::arch::Instruction& inst, const triton::arch::MemoryAccess& mem) {
        triton::ast::SharedAbstractNode node = this->getMemoryAst(mem);

        /* Set load access */
        inst.setLoadAccess(mem, node);

        /* Set implicit read of the base register (LEA) */
        if (this->architecture->isRegisterValid(mem.getConstBaseRegister()))
          (void)this->getRegisterAst(inst, mem.getConstBaseRegister());

        /* Set implicit read of the index register (LEA) */
        if (this->architecture->isRegisterValid(mem.getConstIndexRegister()))
          (void)this->getRegisterAst(inst, mem.getConstIndexRegister());

        return node;
      }


      /* Returns the AST corresponding to the register */
      triton::ast::SharedAbstractNode SymbolicEngine::getRegisterAst(const triton::arch::Register& reg) {
        triton::ast::SharedAbstractNode node = nullptr;
        triton::uint32 bvSize                = reg.getBitSize();
        triton::uint32 high                  = reg.getHigh();
        triton::uint32 low                   = reg.getLow();
        triton::uint512 value                = this->architecture->getConcreteRegisterValue(reg);

        /* Check if the register is already symbolic */
        if (const SharedSymbolicExpression& symReg = this->getSymbolicRegister(reg)) {
          node = this->astCtxt->extract(high, low, this->astCtxt->reference(symReg));
        }
        /* Otherwise, use the concerte value */
        else {
          node = this->astCtxt->bv(value, bvSize);
        }

        /* extend AST if it's a extend operand (mainly used for AArch64) */
        if (reg.getExtendType() != triton::arch::aarch64::ID_EXTEND_INVALID)
          return this->getExtendAst(reg.getExtendType(), reg.getExtendSize(), node);

        /* Shift AST if it's a shift operand (mainly used for AArch64) */
        if (reg.getShiftType() != triton::arch::aarch64::ID_SHIFT_INVALID)
          return this->getShiftAst(reg.getShiftType(), reg.getShiftValue(), node);

        return node;
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
          case triton::arch::OP_MEM:
            return this->createSymbolicMemoryExpression(inst, node, dst.getConstMemory(), comment);
          case triton::arch::OP_REG:
            return this->createSymbolicRegisterExpression(inst, node, dst.getConstRegister(), comment);
          default:
            throw triton::exceptions::SymbolicEngine("SymbolicEngine::createSymbolicExpression(): Invalid operand.");
        }
      }


      /* Returns the new symbolic memory expression */
      const SharedSymbolicExpression& SymbolicEngine::createSymbolicMemoryExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const triton::arch::MemoryAccess& mem, const std::string& comment) {
        std::vector<triton::ast::SharedAbstractNode> ret;
        triton::ast::SharedAbstractNode tmp = nullptr;
        SharedSymbolicExpression se         = nullptr;
        triton::uint64 address              = mem.getAddress();
        triton::uint32 writeSize            = mem.getSize();

        /* Record the aligned memory for a symbolic optimization */
        if (this->modes->isModeEnabled(triton::modes::ALIGNED_MEMORY)) {
          const SharedSymbolicExpression& aligned = this->newSymbolicExpression(node, MEMORY_EXPRESSION, "Aligned Byte reference - " + comment);
          this->addAlignedMemory(address, writeSize, aligned);
        }

        /*
         * As the x86's memory can be accessed without alignment, each byte of the
         * memory must be assigned to an unique reference.
         */
        while (writeSize) {
          triton::uint32 high = ((writeSize * BYTE_SIZE_BIT) - 1);
          triton::uint32 low  = ((writeSize * BYTE_SIZE_BIT) - BYTE_SIZE_BIT);
          /* Extract each byte of the memory */
          tmp = this->astCtxt->extract(high, low, node);
          /* Assign each byte to a new symbolic expression */
          se = this->newSymbolicExpression(tmp, MEMORY_EXPRESSION, "Byte reference - " + comment);
          /* Set the origin of the symbolic expression */
          se->setOriginMemory(triton::arch::MemoryAccess(((address + writeSize) - 1), BYTE_SIZE));
          /* ret is the for the final expression */
          ret.push_back(tmp);
          /* add the symbolic expression to the instruction */
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
        tmp = this->astCtxt->concat(ret);

        /* Synchronize the concrete state */
        this->architecture->setConcreteMemoryValue(mem, tmp->evaluate());

        se = this->newSymbolicExpression(tmp, MEMORY_EXPRESSION, "Temporary concatenation reference - " + comment);
        se->setOriginMemory(triton::arch::MemoryAccess(address, mem.getSize()));

        /* Set explicit write of the memory access */
        inst.setStoreAccess(mem, node);

        /* Set implicit read of the base register (LEA) */
        if (this->architecture->isRegisterValid(mem.getConstBaseRegister()))
          (void)this->getRegisterAst(inst, mem.getConstBaseRegister());

        /* Set implicit read of the index register (LEA) */
        if (this->architecture->isRegisterValid(mem.getConstIndexRegister()))
          (void)this->getRegisterAst(inst, mem.getConstIndexRegister());

        return inst.addSymbolicExpression(se);
      }


      /* Returns the parent AST after inserting the subregister (node) in its AST. */
      triton::ast::SharedAbstractNode SymbolicEngine::insertSubRegisterInParent(const triton::arch::Register& reg, const triton::ast::SharedAbstractNode& node, bool zxForAssign) {
        const triton::arch::Register& parentReg   = this->architecture->getParentRegister(reg);
        triton::ast::SharedAbstractNode finalExpr = nullptr;
        triton::uint32 regSize                    = reg.getSize();

        switch (regSize) {
          case BYTE_SIZE: {
            auto origReg = this->getRegisterAst(parentReg);
            /* Mainly used for x86 */
            if (reg.getLow() == 0) {
              finalExpr = this->astCtxt->concat(
                            this->astCtxt->extract((parentReg.getBitSize() - 1), BYTE_SIZE_BIT, origReg),
                            node
                          );
            }
            else {
              finalExpr = this->astCtxt->concat(
                            this->astCtxt->extract((parentReg.getBitSize() - 1), WORD_SIZE_BIT, origReg),
                            this->astCtxt->concat(
                              node,
                              this->astCtxt->extract((BYTE_SIZE_BIT - 1), 0, origReg)
                            )
                          );
            }
            break;
          }
          case WORD_SIZE: {
            auto origReg = this->getRegisterAst(parentReg);
            /* Mainly used for x86 */
            finalExpr = this->astCtxt->concat(
                          this->astCtxt->extract((parentReg.getBitSize() - 1), WORD_SIZE_BIT, origReg),
                          node
                        );
            break;
          }
          case DWORD_SIZE:
          case QWORD_SIZE:
          case DQWORD_SIZE:
          case QQWORD_SIZE:
          case DQQWORD_SIZE: {
            if (zxForAssign == false) {
              if (parentReg.getBitSize() > reg.getBitSize()) {
                auto origReg = this->getRegisterAst(parentReg);
                finalExpr = this->astCtxt->concat(
                              this->astCtxt->extract((parentReg.getBitSize() - 1), reg.getHigh() + 1, origReg),
                              node
                            );
              }
              else {
                finalExpr = node;
              }
            }
            /* zxForAssign == true */
            else {
              finalExpr = this->astCtxt->zx(parentReg.getBitSize() - node->getBitvectorSize(), node);
            }
            break;
          }
        }

        return finalExpr;
      }


      /* Returns the new symbolic register expression */
      const SharedSymbolicExpression& SymbolicEngine::createSymbolicRegisterExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const triton::arch::Register& reg, const std::string& comment) {
        SharedSymbolicExpression se = nullptr;

        /* Check if the register is a flag */
        if (this->architecture->isFlag(reg)) {
          se = this->newSymbolicExpression(node, REGISTER_EXPRESSION, comment);
          this->assignSymbolicExpressionToRegister(se, reg);
        }
        else {
          se = this->newSymbolicExpression(this->insertSubRegisterInParent(reg, node), REGISTER_EXPRESSION, comment);
          this->assignSymbolicExpressionToRegister(se, this->architecture->getParentRegister(reg));
        }

        inst.setWrittenRegister(reg, node);
        return inst.addSymbolicExpression(se);
      }


      /* Returns the new symbolic volatile expression */
      const SharedSymbolicExpression& SymbolicEngine::createSymbolicVolatileExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const std::string& comment) {
        const SharedSymbolicExpression& se = this->newSymbolicExpression(node, VOLATILE_EXPRESSION, comment);
        return inst.addSymbolicExpression(se);
      }


      /* Adds and assign a new memory reference */
      inline void SymbolicEngine::addMemoryReference(triton::uint64 mem, const SharedSymbolicExpression& expr) {
        this->memoryReference[mem] = expr;
      }


      /* Assigns a symbolic expression to a register */
      void SymbolicEngine::assignSymbolicExpressionToRegister(const SharedSymbolicExpression& se, const triton::arch::Register& reg) {
        const triton::ast::SharedAbstractNode& node = se->getAst();
        triton::uint32 id                           = reg.getParent();

        /* We can assign an expression only on parent registers */
        if (reg.getId() != id) {
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::assignSymbolicExpressionToRegister(): We can assign an expression only on parent registers.");
        }

        /* Check if the size of the symbolic expression is equal to the target register */
        if (node->getBitvectorSize() != reg.getBitSize()) {
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::assignSymbolicExpressionToRegister(): The size of the symbolic expression is not equal to the target register.");
        }

        se->setType(REGISTER_EXPRESSION);
        se->setOriginRegister(reg);

        if (reg.isMutable()) {
          /* Assign if this register is mutable */
          this->symbolicReg[id] = se;
          /* Synchronize the concrete state */
          this->architecture->setConcreteRegisterValue(reg, node->evaluate());
        }
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
        if (this->modes->isModeEnabled(triton::modes::ALIGNED_MEMORY)) {
          this->addAlignedMemory(address, writeSize, se);
        }

        /*
         * As the x86's memory can be accessed without alignment, each byte of the
         * memory must be assigned to an unique reference.
         */
        while (writeSize) {
          triton::uint32 high = ((writeSize * BYTE_SIZE_BIT) - 1);
          triton::uint32 low  = ((writeSize * BYTE_SIZE_BIT) - BYTE_SIZE_BIT);
          /* Extract each byte of the memory */
          const triton::ast::SharedAbstractNode& tmp = this->astCtxt->extract(high, low, node);
          /* For each byte create a new symbolic expression */
          const SharedSymbolicExpression& byteRef = this->newSymbolicExpression(tmp, MEMORY_EXPRESSION, "Byte reference");
          /* Set the origin of the symbolic expression */
          byteRef->setOriginMemory(triton::arch::MemoryAccess(((address + writeSize) - 1), BYTE_SIZE));
          /* Assign memory with little endian */
          this->addMemoryReference((address + writeSize) - 1, byteRef);
          /* continue */
          writeSize--;
        }

        /* Synchronize the concrete state */
        this->architecture->setConcreteMemoryValue(mem, node->evaluate());
      }


      /* Returns true if the symbolic engine is enable */
      bool SymbolicEngine::isEnabled(void) const {
        return this->enableFlag;
      }


      /* Returns true if the symbolic expression ID exists */
      bool SymbolicEngine::isSymbolicExpressionExists(triton::usize symExprId) const {
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
                                                      this->architecture->gprBitSize()
                                                    )
                                                  )
                                                );


          /* Initialize the AST of the memory access (LEA) -> ((pc + base) + (index * scale) + disp) */
          auto leaAst = this->astCtxt->bvadd(
                          (mem.getPcRelative() ? this->astCtxt->bv(mem.getPcRelative(), bitSize) :
                            (this->architecture->isRegisterValid(base) ? this->getRegisterAst(base) :
                              this->astCtxt->bv(0, bitSize)
                            )
                          ),
                          this->astCtxt->bvadd(
                            this->astCtxt->bvmul(
                              (this->architecture->isRegisterValid(index) ? this->getRegisterAst(index) : this->astCtxt->bv(0, bitSize)),
                              this->astCtxt->bv(scaleValue, bitSize)
                            ),
                            this->astCtxt->bv(dispValue, bitSize)
                          )
                        );

          /* Use segments as base address instead of selector into the GDT. */
          if (segmentValue) {
            leaAst = this->astCtxt->bvadd(
                       this->astCtxt->bv(segmentValue, seg.getBitSize()),
                       this->astCtxt->sx((seg.getBitSize() - bitSize), leaAst)
                     );
          }

          /* Set AST */
          mem.setLeaAst(leaAst);

          /* Initialize the address only if it is not already defined */
          if (!mem.getAddress() || force)
            mem.setAddress(leaAst->evaluate().convert_to<triton::uint64>());
        }
      }


      triton::uint512 SymbolicEngine::getConcreteVariableValue(const SharedSymbolicVariable& symVar) const {
        return this->astCtxt->getVariableValue(symVar->getName());
      }


      void SymbolicEngine::setConcreteVariableValue(const SharedSymbolicVariable& symVar, const triton::uint512& value) {
        triton::uint512 max = -1;

        /* Check if the value is too big */
        max = max >> (512 - symVar->getSize());
        if (value > max) {
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::setConcreteVariableValue(): Can not set this value (too big) to this symbolic variable.");
        }

        /* Update the symbolic variable value */
        this->astCtxt->updateVariable(symVar->getName(), value);

        /* Synchronize concrete state */
        if (symVar->getType() == REGISTER_VARIABLE) {
          const triton::arch::Register& reg = this->architecture->getRegister(static_cast<triton::arch::register_e>(symVar->getOrigin()));
          this->architecture->setConcreteRegisterValue(reg, value);
        }

        else if (symVar->getType() == MEMORY_VARIABLE && symVar->getSize() && !(symVar->getSize() % BYTE_SIZE_BIT)) {
          triton::uint64 addr            = symVar->getOrigin();
          triton::uint32 size            = symVar->getSize() / BYTE_SIZE_BIT;
          triton::arch::MemoryAccess mem = triton::arch::MemoryAccess(addr, size);

          this->architecture->setConcreteMemoryValue(mem, value);
        }
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */
