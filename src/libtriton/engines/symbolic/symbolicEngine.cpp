//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <cstring>
#include <new>
#include <set>

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
        : triton::engines::symbolic::SymbolicSimplification(architecture, callbacks),
          triton::engines::symbolic::PathManager(modes, astCtxt),
          astCtxt(astCtxt),
          modes(modes) {

        if (architecture == nullptr) {
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::SymbolicEngine(): The architecture pointer must be valid.");
        }

        this->architecture      = architecture;
        this->callbacks         = callbacks;
        this->numberOfRegisters = this->architecture->numberOfRegisters();
        this->uniqueSymExprId   = 0;
        this->uniqueSymVarId    = 0;
        this->memoryArray       = nullptr;

        this->symbolicReg.resize(this->numberOfRegisters);
      }


      SymbolicEngine::SymbolicEngine(const SymbolicEngine& other)
        : triton::engines::symbolic::SymbolicSimplification(other),
          triton::engines::symbolic::PathManager(other),
          astCtxt(other.astCtxt),
          modes(other.modes) {

        this->alignedBitvectorMemory = other.alignedBitvectorMemory;
        this->architecture           = other.architecture;
        this->callbacks              = other.callbacks;
        this->memoryArray            = other.memoryArray;
        this->memoryBitvector        = other.memoryBitvector;
        this->numberOfRegisters      = other.numberOfRegisters;
        this->symbolicExpressions    = other.symbolicExpressions;
        this->symbolicReg            = other.symbolicReg;
        this->symbolicVariables      = other.symbolicVariables;
        this->uniqueSymExprId        = other.uniqueSymExprId;
        this->uniqueSymVarId         = other.uniqueSymVarId;
      }


      SymbolicEngine::~SymbolicEngine() {
        /* See #828: Release ownership before calling container destructor */
        this->memoryBitvector.clear();
        this->symbolicReg.clear();
        this->memoryArray = nullptr;
      }


      SymbolicEngine& SymbolicEngine::operator=(const SymbolicEngine& other) {
        triton::engines::symbolic::SymbolicSimplification::operator=(other);
        triton::engines::symbolic::PathManager::operator=(other);

        this->alignedBitvectorMemory = other.alignedBitvectorMemory;
        this->architecture           = other.architecture;
        this->astCtxt                = other.astCtxt;
        this->callbacks              = other.callbacks;
        this->memoryBitvector        = other.memoryBitvector;
        this->modes                  = other.modes;
        this->numberOfRegisters      = other.numberOfRegisters;
        this->symbolicExpressions    = other.symbolicExpressions;
        this->symbolicReg            = other.symbolicReg;
        this->symbolicVariables      = other.symbolicVariables;
        this->uniqueSymExprId        = other.uniqueSymExprId;
        this->uniqueSymVarId         = other.uniqueSymVarId;

        return *this;
      }


      /*
       * Concretize a register. If the register is setup as nullptr, the next assignment
       * will be over the concretization. This method must be called before symbolic
       * processing.
       */
      void SymbolicEngine::concretizeRegister(const triton::arch::Register& reg) {
        triton::arch::register_e parentId = reg.getParent();

        if (this->architecture->isRegisterValid(parentId)) {
          this->symbolicReg[parentId] = nullptr;
        }
      }


      /* Same as concretizeRegister but with all registers */
      void SymbolicEngine::concretizeAllRegister(void) {
        for (triton::uint32 i = 0; i < this->numberOfRegisters; i++) {
          this->symbolicReg[i] = nullptr;
        }
      }


      /*
       * Concretize a memory. If the memory is not found into the map, the next
       * assignment will be over the concretization. This method must be called
       * before symbolic processing.
       */
      void SymbolicEngine::concretizeMemory(const triton::arch::MemoryAccess& mem, bool array) {
        triton::uint64 addr = mem.getAddress();
        triton::uint32 size = mem.getSize();

        for (triton::uint32 index = 0; index < size; index++) {
          this->concretizeMemory(addr+index, array);
        }
      }


      /*
       * Concretize a memory. If the memory is not found into the map, the next
       * assignment will be over the concretization. This method must be called
       * before symbolic processing.
       */
      void SymbolicEngine::concretizeMemory(triton::uint64 addr, bool array) {
        /* Symbolic array */
        if (this->isArrayMode() && array) {
          auto cv = this->architecture->getConcreteMemoryValue(addr);
          auto cell = this->astCtxt->store(this->astCtxt->reference(this->getMemoryArray()), addr, this->astCtxt->bv(cv, triton::bitsize::byte));
          this->memoryArray = this->newSymbolicExpression(cell, MEMORY_EXPRESSION, "Concretization");
          this->memoryArray->setOriginMemory(triton::arch::MemoryAccess(addr, triton::size::byte));
        }

        /* Symbolic bitvector */
        this->memoryBitvector.erase(addr);
        this->removeAlignedMemory(addr, triton::size::byte);
      }


      /* Same as concretizeMemory but with all address memory */
      void SymbolicEngine::concretizeAllMemory(void) {
        this->memoryArray = nullptr;          /* abv logic */
        this->memoryBitvector.clear();        /* bv logic  */
        this->alignedBitvectorMemory.clear(); /* bv optim  */
      }


      /* Gets an aligned entry. */
      const SharedSymbolicExpression& SymbolicEngine::getAlignedMemory(triton::uint64 address, triton::uint32 size) {
        return this->alignedBitvectorMemory[std::make_pair(address, size)];
      }


      /* Checks if the aligned memory is recored. */
      bool SymbolicEngine::isAlignedMemory(triton::uint64 address, triton::uint32 size) {
        if (this->alignedBitvectorMemory.find(std::make_pair(address, size)) != this->alignedBitvectorMemory.end()) {
          return true;
        }
        return false;
      }


      /* Adds an aligned memory */
      void SymbolicEngine::addAlignedMemory(triton::uint64 address, triton::uint32 size, const SharedSymbolicExpression& expr) {
        this->removeAlignedMemory(address, size);
        if (!(this->modes->isModeEnabled(triton::modes::ONLY_ON_SYMBOLIZED) && expr->getAst()->isSymbolized() == false)) {
          this->alignedBitvectorMemory[std::make_pair(address, size)] = expr;
        }
      }


      /* Removes an aligned memory */
      void SymbolicEngine::removeAlignedMemory(triton::uint64 address, triton::uint32 size) {
        /*
         * Avoid accessing the alignedBitvectorMemory array when empty. This usually happens when
         * you initialize the symbolic engine and concretize whole sections of an executable using
         * setConcreteMemoryValue. No symbolic memory has been created yet but this function will
         * still try to rougly erase (size * 7) elements.
         */
        if (this->alignedBitvectorMemory.empty())
          return;

        /* Do nothing if we are in array mode */
        if (this->isArrayMode())
          return;

        /* Remove overloaded positive ranges */
        for (triton::uint32 index = 0; index < size; index++) {
          this->alignedBitvectorMemory.erase(std::make_pair(address+index, triton::size::byte));
          this->alignedBitvectorMemory.erase(std::make_pair(address+index, triton::size::word));
          this->alignedBitvectorMemory.erase(std::make_pair(address+index, triton::size::dword));
          this->alignedBitvectorMemory.erase(std::make_pair(address+index, triton::size::qword));
          this->alignedBitvectorMemory.erase(std::make_pair(address+index, triton::size::fword));
          this->alignedBitvectorMemory.erase(std::make_pair(address+index, triton::size::dqword));
          this->alignedBitvectorMemory.erase(std::make_pair(address+index, triton::size::qqword));
          this->alignedBitvectorMemory.erase(std::make_pair(address+index, triton::size::dqqword));
        }

        /* Remove overloaded negative ranges */
        for (triton::uint32 index = 1; index < triton::size::dqqword; index++) {
          if (index < triton::size::word)    this->alignedBitvectorMemory.erase(std::make_pair(address-index, triton::size::word));
          if (index < triton::size::dword)   this->alignedBitvectorMemory.erase(std::make_pair(address-index, triton::size::dword));
          if (index < triton::size::qword)   this->alignedBitvectorMemory.erase(std::make_pair(address-index, triton::size::qword));
          if (index < triton::size::fword)   this->alignedBitvectorMemory.erase(std::make_pair(address-index, triton::size::fword));
          if (index < triton::size::dqword)  this->alignedBitvectorMemory.erase(std::make_pair(address-index, triton::size::dqword));
          if (index < triton::size::qqword)  this->alignedBitvectorMemory.erase(std::make_pair(address-index, triton::size::qqword));
          if (index < triton::size::dqqword) this->alignedBitvectorMemory.erase(std::make_pair(address-index, triton::size::dqqword));
        }
      }


      /* Returns the reference memory if it's referenced otherwise returns nullptr */
      SharedSymbolicExpression SymbolicEngine::getSymbolicMemory(triton::uint64 addr) const {
        auto it = this->memoryBitvector.find(addr);
        if (it != this->memoryBitvector.end()) {
          return it->second;
        }
        return nullptr;
      }


      /* Returns the symbolic variable otherwise raises an exception */
      SharedSymbolicVariable SymbolicEngine::getSymbolicVariable(triton::usize symVarId) const {
        auto it = this->symbolicVariables.find(symVarId);
        if (it == this->symbolicVariables.end()) {
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::getSymbolicVariable(): Unregistred symbolic variable.");
        }

        if (auto node = it->second.lock()) {
          return node;
        }

        throw triton::exceptions::SymbolicEngine("SymbolicEngine::getSymbolicVariable(): This symbolic variable is dead.");
      }


      /* Returns the symbolic variable otherwise returns nullptr */
      SharedSymbolicVariable SymbolicEngine::getSymbolicVariable(const std::string& name) const {
        /*
         * FIXME: 1) When there is a ton of symvar, this loop takes a while to go through.
         *           What about adding two maps {id:symvar} and {string:symvar}? See #648.
         *
         *        2) If we are looking for alias, we return the first occurrence. It's not
         *           ideal if we have multiple same aliases.
         */
        for (auto& sv: this->symbolicVariables) {
          if (auto symVar = sv.second.lock()) {
            if (symVar->getName() == name || symVar->getAlias() == name) {
              return symVar;
            }
          }
        }
        throw triton::exceptions::SymbolicEngine("SymbolicEngine::getSymbolicVariable(): Unregistred or dead symbolic variable.");
      }


      /* Returns all symbolic variables */
      std::map<triton::usize, SharedSymbolicVariable> SymbolicEngine::getSymbolicVariables(void) const {
        // Copy and clean up dead weak ref
        std::map<triton::usize, SharedSymbolicVariable> ret;
        std::vector<triton::usize> toRemove;

        for (auto& kv : this->symbolicVariables) {
          if (auto sp = kv.second.lock()) {
            ret[kv.first] = sp;
          } else {
            toRemove.push_back(kv.first);
          }
        }

        for (triton::usize id : toRemove) {
          this->symbolicVariables.erase(id);
        }

        return ret;
      }


      void SymbolicEngine::setImplicitReadRegisterFromEffectiveAddress(triton::arch::Instruction& inst, const triton::arch::MemoryAccess& mem) {
        /* Set implicit read of the segment register (LEA) */
        if (this->architecture->isRegisterValid(mem.getConstSegmentRegister())) {
          (void)this->getRegisterAst(inst, mem.getConstSegmentRegister());
        }

        /* Set implicit read of the base register (LEA) */
        if (this->architecture->isRegisterValid(mem.getConstBaseRegister())) {
          (void)this->getRegisterAst(inst, mem.getConstBaseRegister());
        }

        /* Set implicit read of the index register (LEA) */
        if (this->architecture->isRegisterValid(mem.getConstIndexRegister())) {
          (void)this->getRegisterAst(inst, mem.getConstIndexRegister());
        }
      }


      const SharedSymbolicExpression& SymbolicEngine::addSymbolicExpressions(triton::arch::Instruction& inst, triton::usize id) const {
        /* See #1002: There may be multiple new symbolic expressions when AST_OPTIMIZATIONS are on */
        for (triton::usize i = id; i != this->uniqueSymExprId; ++i) {
          if (this->isSymbolicExpressionExists(i)) {
            inst.addSymbolicExpression(this->getSymbolicExpression(i));
          }
        }
        return inst.symbolicExpressions.back();
      }


      /* Returns the shared symbolic expression corresponding to the register */
      const SharedSymbolicExpression& SymbolicEngine::getSymbolicRegister(const triton::arch::Register& reg) const {
        triton::arch::register_e parentId = reg.getParent();

        if (this->architecture->isRegisterValid(parentId)) {
          return this->symbolicReg.at(parentId);
        }

        throw triton::exceptions::SymbolicEngine("SymbolicEngine::getSymbolicRegister(): Invalid Register");
      }


      /* Returns the symbolic address value */
      triton::uint8 SymbolicEngine::getSymbolicMemoryValue(triton::uint64 address) {
        triton::arch::MemoryAccess mem(address, triton::size::byte);
        return static_cast<triton::uint8>(this->getSymbolicMemoryValue(mem));
      }


      /* Returns the symbolic memory value */
      triton::uint512 SymbolicEngine::getSymbolicMemoryValue(const triton::arch::MemoryAccess& mem) {
        const triton::ast::SharedAbstractNode& node = this->getMemoryAst(mem);
        return node->evaluate();
      }


      /* Returns the symbolic values of a memory area */
      std::vector<triton::uint8> SymbolicEngine::getSymbolicMemoryAreaValue(triton::uint64 baseAddr, triton::usize size) {
        std::vector<triton::uint8> area;

        area.reserve(size);
        for (triton::usize index = 0; index < size; index++) {
          area.push_back(this->getSymbolicMemoryValue(baseAddr + index));
        }

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


      /* Returns or init the symbolic memory array */
      SharedSymbolicExpression SymbolicEngine::getMemoryArray(void) {
        if (this->isArrayMode() && this->memoryArray == nullptr) {
          triton::uint32 gpr_size = this->architecture->gprBitSize();
          this->memoryArray = this->newSymbolicExpression(this->astCtxt->array(gpr_size), VOLATILE_EXPRESSION);
        }
        return this->memoryArray;
      }


      /* Creates a new symbolic expression with comment */
      SharedSymbolicExpression SymbolicEngine::newSymbolicExpression(const triton::ast::SharedAbstractNode& node, triton::engines::symbolic::expression_e type, const std::string& comment) {
        if (this->modes->isModeEnabled(triton::modes::AST_OPTIMIZATIONS)) {
          /*
           * Create volatile expression for extended part to avoid long
           * formulas while printing. Long formulas are introduced by
           * optimizations of AstContext::concat and AstContext::extract
           */
          if (node->getType() == triton::ast::ZX_NODE || node->getType() == triton::ast::SX_NODE) {
            auto n = node->getChildren()[1];
            if (n->getType() != triton::ast::REFERENCE_NODE && n->getType() != triton::ast::VARIABLE_NODE) {
              /* FIXME: We lost the origin if we create a new symbolic expression without returning it */
              auto e = this->newSymbolicExpression(n, VOLATILE_EXPRESSION, "Extended part - " + comment);
              node->setChild(1, this->astCtxt->reference(e));
            }
          }
        }

        /* Each symbolic expression must have an unique id */
        triton::usize id = this->getUniqueSymExprId();

        /* Performes transformation if there are rules recorded */
        const triton::ast::SharedAbstractNode& snode = this->simplify(node);

        /* Allocates the new shared symbolic expression */
        SharedSymbolicExpression expr = std::make_shared<SymbolicExpression>(snode, id, type, comment);
        if (expr == nullptr) {
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::newSymbolicExpression(): not enough memory");
        }

        /* Save and returns the new shared symbolic expression */
        this->symbolicExpressions[id] = expr;
        return expr;
      }


      /* Removes the symbolic expression corresponding to the id */
      void SymbolicEngine::removeSymbolicExpression(const SharedSymbolicExpression& expr) {
        if (this->symbolicExpressions.find(expr->getId()) != this->symbolicExpressions.end()) {
          /* Concretize memory */
          if (expr->getType() == MEMORY_EXPRESSION) {
            const auto& mem = expr->getOriginMemory();
            this->concretizeMemory(mem, false);
          }

          /* Concretize register */
          else if (expr->getType() == REGISTER_EXPRESSION) {
            const auto& reg = expr->getOriginRegister();
            this->concretizeRegister(reg);
          }

          /* Delete and remove the pointer */
          this->symbolicExpressions.erase(expr->getId());
        }
      }


      /* Gets the shared symbolic expression from a symbolic id */
      SharedSymbolicExpression SymbolicEngine::getSymbolicExpression(triton::usize symExprId) const {
        auto it = this->symbolicExpressions.find(symExprId);
        if (it == this->symbolicExpressions.end()) {
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::getSymbolicExpression(): symbolic expression id not found");
        }

        if (auto sp = it->second.lock()) {
          return sp;
        }

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
      std::unordered_map<triton::usize, SharedSymbolicExpression> SymbolicEngine::sliceExpressions(const SharedSymbolicExpression& expr) {
        std::unordered_map<triton::usize, SharedSymbolicExpression> exprs;

        if (expr == nullptr) {
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::sliceExpressions(): expr cannot be null.");
        }

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

        for (auto id : invalidSymExpr) {
          this->symbolicExpressions.erase(id);
        }

        return taintedExprs;
      }


      /* Returns the map of symbolic registers defined */
      std::unordered_map<triton::arch::register_e, SharedSymbolicExpression> SymbolicEngine::getSymbolicRegisters(void) const {
        std::unordered_map<triton::arch::register_e, SharedSymbolicExpression> ret;

        for (triton::uint32 it = 0; it < this->numberOfRegisters; it++) {
          if (this->symbolicReg[it] != nullptr) {
            ret[triton::arch::register_e(it)] = this->symbolicReg[it];
          }
        }

        return ret;
      }


      /* Returns the map of symbolic memory defined */
      const std::unordered_map<triton::uint64, SharedSymbolicExpression>& SymbolicEngine::getSymbolicMemory(void) const {
        return this->memoryBitvector;
      }


      /*
       * Converts an expression id to a symbolic variable.
       * e.g:
       * #43 = (_ bv10 8)
       * symbolizeExpression(43, 8)
       * #43 = SymVar_4
       */
      SharedSymbolicVariable SymbolicEngine::symbolizeExpression(triton::usize exprId, triton::uint32 symVarSize, const std::string& symVarAlias) {
        const SharedSymbolicExpression& expression = this->getSymbolicExpression(exprId);
        const SharedSymbolicVariable& symVar       = this->newSymbolicVariable(UNDEFINED_VARIABLE, 0, symVarSize, symVarAlias);
        const triton::ast::SharedAbstractNode& tmp = this->astCtxt->variable(symVar);

        if (expression->getAst()) {
           this->setConcreteVariableValue(symVar, expression->getAst()->evaluate());
        }

        expression->setAst(tmp);

        return symVar;
      }


      /* Symbolize a memory area to 8-bits symbolic variables */
      void SymbolicEngine::symbolizeMemory(triton::uint64 addr, triton::usize size) {
        for (triton::usize i = 0; i != size; i++) {
          this->symbolizeMemory(triton::arch::MemoryAccess(addr + i, triton::size::byte));
        }
      }


      /* The memory size is used to define the symbolic variable's size. */
      SharedSymbolicVariable SymbolicEngine::symbolizeMemory(const triton::arch::MemoryAccess& mem, const std::string& symVarAlias) {
        triton::uint64 memAddr    = mem.getAddress();
        triton::uint32 symVarSize = mem.getSize();
        triton::uint512 cv        = this->architecture->getConcreteMemoryValue(mem);

        /* First we create a symbolic variable */
        const SharedSymbolicVariable& symVar = this->newSymbolicVariable(MEMORY_VARIABLE, memAddr, symVarSize * bitsize::byte, symVarAlias);

        /* Create the AST node */
        const triton::ast::SharedAbstractNode& symVarNode = this->astCtxt->variable(symVar);

        /* Setup the concrete value to the symbolic variable */
        this->setConcreteVariableValue(symVar, cv);

        /* Record the aligned symbolic variable for a symbolic optimization */
        if (this->isAlignedMode() && this->isArrayMode() == false) {
          const SharedSymbolicExpression& aligned = this->newSymbolicExpression(symVarNode, MEMORY_EXPRESSION, "Aligned optimization");
          aligned->setOriginMemory(mem);
          this->addAlignedMemory(memAddr, symVarSize, aligned);
        }

        /*  Split expression in bytes */
        for (triton::sint32 index = symVarSize-1; index >= 0; index--) {
          triton::uint32 high = ((bitsize::byte * (index + 1)) - 1);
          triton::uint32 low  = ((bitsize::byte * (index + 1)) - bitsize::byte);

          /* Isolate the good part of the symbolic variable */
          const triton::ast::SharedAbstractNode& tmp = this->astCtxt->extract(high, low, symVarNode);

          /* Create a new symbolic expression containing the symbolic variable */
          /* Symbolic array */
          if (this->isArrayMode()) {
            const auto& cell = this->astCtxt->store(this->astCtxt->reference(this->getMemoryArray()), memAddr + index, tmp);
            this->memoryArray = this->newSymbolicExpression(cell, MEMORY_EXPRESSION, "Byte reference");
            this->memoryArray->setOriginMemory(triton::arch::MemoryAccess(memAddr + index, triton::size::byte));
            this->addBitvectorMemory(memAddr + index, this->memoryArray);
          }
          /* Symbolic bitvector */
          else {
            const SharedSymbolicExpression& se = this->newSymbolicExpression(tmp, MEMORY_EXPRESSION, "Byte reference");
            se->setOriginMemory(triton::arch::MemoryAccess(memAddr + index, triton::size::byte));
            this->addBitvectorMemory(memAddr + index, se);
          }
        }

        return symVar;
      }


      SharedSymbolicVariable SymbolicEngine::symbolizeRegister(const triton::arch::Register& reg, const std::string& symVarAlias) {
        const triton::arch::Register& parent  = this->architecture->getRegister(reg.getParent());
        triton::uint32 symVarSize             = reg.getBitSize();
        triton::uint512 cv                    = this->architecture->getConcreteRegisterValue(reg);

        if (!this->architecture->isRegisterValid(parent.getId()))
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::symbolizeRegister(): Invalid register id");

        if (reg.isMutable() == false)
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::symbolizeRegister(): This register is immutable");

        /* Create the symbolic variable */
        const SharedSymbolicVariable& symVar = this->newSymbolicVariable(REGISTER_VARIABLE, reg.getId(), symVarSize, symVarAlias);

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
      SharedSymbolicVariable SymbolicEngine::newSymbolicVariable(triton::engines::symbolic::variable_e type, triton::uint64 origin, triton::uint32 size, const std::string& alias) {
        triton::usize uniqueId = this->getUniqueSymVarId();

        SharedSymbolicVariable symVar = std::make_shared<SymbolicVariable>(type, origin, uniqueId, size, alias);
        if (symVar == nullptr) {
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::newSymbolicVariable(): Cannot allocate a new symbolic variable");
        }

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


      triton::ast::SharedAbstractNode SymbolicEngine::getShiftAst(const triton::arch::arm::ArmOperandProperties& shift, const triton::ast::SharedAbstractNode& node) const {
        auto imm = shift.getShiftImmediate();
        auto reg = shift.getShiftRegister();

        switch (shift.getShiftType()) {
          case triton::arch::arm::ID_SHIFT_ASR:
            return this->astCtxt->bvashr(node, this->astCtxt->bv(imm, node->getBitvectorSize()));

          case triton::arch::arm::ID_SHIFT_LSL:
            return this->astCtxt->bvshl(node, this->astCtxt->bv(imm, node->getBitvectorSize()));

          case triton::arch::arm::ID_SHIFT_LSR:
            return this->astCtxt->bvlshr(node, this->astCtxt->bv(imm, node->getBitvectorSize()));

          case triton::arch::arm::ID_SHIFT_ROR:
            return this->astCtxt->bvror(node, this->astCtxt->bv(imm, node->getBitvectorSize()));

          case triton::arch::arm::ID_SHIFT_RRX: /* Arm32 only. */
            return this->astCtxt->extract(
                      node->getBitvectorSize(),
                      1,
                      this->astCtxt->bvror(
                        this->astCtxt->concat(
                          node,
                          this->getRegisterAst(this->architecture->getRegister(triton::arch::ID_REG_ARM32_C))
                        ),
                        1
                      )
                    );

          case triton::arch::arm::ID_SHIFT_ASR_REG: /* Arm32 only. */
            return this->astCtxt->bvashr(
                      node,
                      this->astCtxt->zx(
                        this->architecture->getRegister(reg).getBitSize() - 8,
                        this->astCtxt->extract(
                          7,
                          0,
                          this->getRegisterAst(this->architecture->getRegister(reg))
                        )
                      )
                    );

          case triton::arch::arm::ID_SHIFT_LSL_REG: /* Arm32 only. */
            return this->astCtxt->bvshl(
                      node,
                      this->astCtxt->zx(
                        this->architecture->getRegister(reg).getBitSize() - 8,
                        this->astCtxt->extract(
                          7,
                          0,
                          this->getRegisterAst(this->architecture->getRegister(reg))
                        )
                      )
                    );

          case triton::arch::arm::ID_SHIFT_LSR_REG: /* Arm32 only. */
            return this->astCtxt->bvlshr(
                      node,
                      this->astCtxt->zx(
                        this->architecture->getRegister(reg).getBitSize() - 8,
                        this->astCtxt->extract(
                          7,
                          0,
                          this->getRegisterAst(this->architecture->getRegister(reg))
                        )
                      )
                    );

          case triton::arch::arm::ID_SHIFT_ROR_REG: /* Arm32 only. */
            return this->astCtxt->bvror(
                      node,
                      this->astCtxt->zx(
                        this->architecture->getRegister(reg).getBitSize() - 8,
                        this->astCtxt->extract(
                          7,
                          0,
                          this->getRegisterAst(this->architecture->getRegister(reg))
                        )
                      )
                    );

          case triton::arch::arm::ID_SHIFT_RRX_REG:
            /* NOTE: Capstone considers this as a viable shift operand but
             * according to the ARM manual this is not possible.
             */
            throw triton::exceptions::SymbolicEngine("SymbolicEngine::getShiftAst(): ID_SHIFT_RRX_REG is an invalid shift operand.");

          default:
            throw triton::exceptions::SymbolicEngine("SymbolicEngine::getShiftAst(): Invalid shift operand.");
        }
      }

      triton::ast::SharedAbstractNode SymbolicEngine::getIndexAst(const triton::arch::arm::ArmOperandProperties& vas_index, const triton::ast::SharedAbstractNode& node) const {
        auto vas_size = vas_index.getVASSize() * triton::bitsize::byte;

        auto low = vas_index.getVectorIndex() * vas_size;
        auto high = low + vas_size - 1;
        
        return this->astCtxt->extract(high, low, node);
      }


      triton::ast::SharedAbstractNode SymbolicEngine::getExtendAst(const triton::arch::arm::ArmOperandProperties& extend, const triton::ast::SharedAbstractNode& node) const {
        triton::uint32 size = extend.getExtendSize();

        switch (extend.getExtendType()) {
          case triton::arch::arm::ID_EXTEND_UXTB:
            return this->astCtxt->zx(size, this->astCtxt->bvshl(this->astCtxt->extract(7, 0, node), this->astCtxt->bv(extend.getShiftImmediate(), 8)));

          case triton::arch::arm::ID_EXTEND_UXTH:
            return this->astCtxt->zx(size, this->astCtxt->bvshl(this->astCtxt->extract(15, 0, node), this->astCtxt->bv(extend.getShiftImmediate(), 16)));

          case triton::arch::arm::ID_EXTEND_UXTW:
            return this->astCtxt->zx(size, this->astCtxt->bvshl(this->astCtxt->extract(31, 0, node), this->astCtxt->bv(extend.getShiftImmediate(), 32)));

          case triton::arch::arm::ID_EXTEND_UXTX:
            return this->astCtxt->zx(size, this->astCtxt->bvshl(this->astCtxt->extract(63, 0, node), this->astCtxt->bv(extend.getShiftImmediate(), 64)));

          case triton::arch::arm::ID_EXTEND_SXTB:
            return this->astCtxt->sx(size, this->astCtxt->bvshl(this->astCtxt->extract(7, 0, node), this->astCtxt->bv(extend.getShiftImmediate(), 8)));

          case triton::arch::arm::ID_EXTEND_SXTH:
            return this->astCtxt->sx(size, this->astCtxt->bvshl(this->astCtxt->extract(15, 0, node), this->astCtxt->bv(extend.getShiftImmediate(), 16)));

          case triton::arch::arm::ID_EXTEND_SXTW:
            return this->astCtxt->sx(size, this->astCtxt->bvshl(this->astCtxt->extract(31, 0, node), this->astCtxt->bv(extend.getShiftImmediate(), 32)));

          case triton::arch::arm::ID_EXTEND_SXTX:
            return this->astCtxt->sx(size, this->astCtxt->bvshl(this->astCtxt->extract(63, 0, node), this->astCtxt->bv(extend.getShiftImmediate(), 64)));

          default:
            throw triton::exceptions::SymbolicEngine("SymbolicEngine::getExtendAst(): Invalid extend operand.");
        }
      }


      /* Returns the AST corresponding to the immediate */
      triton::ast::SharedAbstractNode SymbolicEngine::getImmediateAst(const triton::arch::Immediate& imm) {
        triton::ast::SharedAbstractNode node = this->astCtxt->bv(imm.getValue(), imm.getBitSize());

        /* Shift AST if it's a shift operand */
        if (imm.getShiftType() != triton::arch::arm::ID_SHIFT_INVALID) {
          return this->getShiftAst(static_cast<const triton::arch::arm::ArmOperandProperties>(imm), node);
        }

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
        std::vector<triton::ast::SharedAbstractNode> cells;

        triton::ast::SharedAbstractNode tmp = nullptr;
        triton::uint64 address              = mem.getAddress();
        triton::uint32 size                 = mem.getSize();
        triton::uint8 raw[64]               = {0};
        triton::uint512 value               = this->architecture->getConcreteMemoryValue(mem);

        /* Convert the integer value to a raw buffer */
        triton::utils::fromUintToBuffer(value, raw);

        /*
         * Symbolic optimization
         * If the memory access is aligned, don't split the memory.
         */
        if (this->isArrayMode() == false && this->isAlignedMode() && this->isAlignedMemory(address, size)) {
          return this->getAlignedMemory(address, size)->getAst();
        }

        cells.reserve(size);
        while (size) {
          /* Symbolic Array */
          if (this->isArrayMode()) {
            auto gpr_size = this->architecture->gprBitSize();
            auto memor_ea = mem.getLeaAst() != nullptr ? mem.getLeaAst() : this->astCtxt->bv(address, gpr_size);
            auto final_ea = this->astCtxt->bvadd(memor_ea, this->astCtxt->bv(size - 1, gpr_size));

            /* Symbolic mode: Should we concretize memory indexing? */
            if (this->modes->isModeEnabled(triton::modes::SYMBOLIZE_LOAD) == false) {
              final_ea = this->astCtxt->bv(final_ea->evaluate(), gpr_size);
            }

            cells.push_back(this->astCtxt->select(this->astCtxt->reference(this->getMemoryArray()), final_ea));
          }
          /* Symbolic Bitvector */
          else {
            const SharedSymbolicExpression& symMem = this->getSymbolicMemory(address + size - 1);
            if (symMem) cells.push_back(this->astCtxt->reference(symMem));
            else        cells.push_back(this->astCtxt->bv(raw[size - 1], bitsize::byte));
          }
          size--;
        }

        /* If size is 1, return the memory cell */
        if (cells.size() == 1) {
          return cells.back();
        }

        /* Otherwise concat them all */
        return this->astCtxt->concat(cells);
      }


      /* Returns the AST corresponding to the memory and defines the memory as input of the instruction */
      triton::ast::SharedAbstractNode SymbolicEngine::getMemoryAst(triton::arch::Instruction& inst, const triton::arch::MemoryAccess& mem) {
        triton::ast::SharedAbstractNode node = this->getMemoryAst(mem);

        /* Set load access */
        inst.setLoadAccess(mem, node);

        /* Set implicit read of the base and index registers from an effective address */
        this->setImplicitReadRegisterFromEffectiveAddress(inst, mem);

        return node;
      }


      /* Returns the AST corresponding to the register */
      triton::ast::SharedAbstractNode SymbolicEngine::getRegisterAst(const triton::arch::Register& reg) const {
        triton::ast::SharedAbstractNode node = nullptr;
        triton::uint32 bvSize                = reg.getBitSize();
        triton::uint32 high                  = reg.getHigh();
        triton::uint32 low                   = reg.getLow();
        triton::uint512 value                = this->architecture->getConcreteRegisterValue(reg);

        /* Check if the register is already symbolic */
        const SharedSymbolicExpression& symReg = this->getSymbolicRegister(reg);
        if (symReg) node = this->astCtxt->extract(high, low, this->astCtxt->reference(symReg));
        else        node = this->astCtxt->bv(value, bvSize);

        /* extend AST if it's a extend operand (mainly used for AArch64) */
        if (reg.getExtendType() != triton::arch::arm::ID_EXTEND_INVALID) {
          return this->getExtendAst(static_cast<const triton::arch::arm::ArmOperandProperties>(reg), node);
        }

        /* Shift AST if it's a shift operand (mainly used for Arm) */
        if (reg.getShiftType() != triton::arch::arm::ID_SHIFT_INVALID) {
          return this->getShiftAst(static_cast<const triton::arch::arm::ArmOperandProperties>(reg), node);
        }

        /* Extract AST if it's have vector index (mainly used for Arm Neon) */
        if (reg.getVectorIndex() != -1 && reg.getVASSize() != 0) {
          return this->getIndexAst(static_cast<const triton::arch::arm::ArmOperandProperties>(reg), node);
        }

        return node;
      }


      /* Returns the AST corresponding to the register and defines the register as input of the instruction */
      triton::ast::SharedAbstractNode SymbolicEngine::getRegisterAst(triton::arch::Instruction& inst, const triton::arch::Register& reg) const {
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
        triton::ast::SharedAbstractNode tmp = nullptr;
        SharedSymbolicExpression se         = nullptr;
        triton::uint64 address              = mem.getAddress();
        triton::uint32 writeSize            = mem.getSize();
        triton::usize id                    = this->uniqueSymExprId;

        /* Record the aligned memory for a symbolic optimization */
        if (this->isAlignedMode() && this->isArrayMode() == false) {
          const SharedSymbolicExpression& aligned = this->newSymbolicExpression(node, MEMORY_EXPRESSION, "Aligned optimization - " + comment);
          aligned->setOriginMemory(mem);
          this->addAlignedMemory(address, writeSize, aligned);
          /* Refresh the current id to not link the aligned expression to the instruction */
          id = this->uniqueSymExprId;
        }

        /*
         * As the x86's memory can be accessed without alignment, each byte of the
         * memory must be assigned to an unique reference.
         */
        while (writeSize) {
          triton::uint32 high = ((writeSize * bitsize::byte) - 1);
          triton::uint32 low  = ((writeSize * bitsize::byte) - bitsize::byte);

          /* Extract each byte of the memory */
          tmp = this->astCtxt->extract(high, low, node);

          /* Symbolic array */
          if (this->isArrayMode()) {
            auto gpr_size = this->architecture->gprBitSize();
            auto memor_ea = mem.getLeaAst() != nullptr ? mem.getLeaAst() : this->astCtxt->bv(address, gpr_size);
            auto final_ea = this->astCtxt->bvadd(memor_ea, this->astCtxt->bv(writeSize - 1, gpr_size));

            /* Symbolic mode: Should we concretize memory indexing? */
            if (this->modes->isModeEnabled(triton::modes::SYMBOLIZE_STORE) == false) {
              final_ea = this->astCtxt->bv(final_ea->evaluate(), gpr_size);
            }

            auto cell = this->astCtxt->store(this->astCtxt->reference(this->getMemoryArray()), final_ea, tmp);
            this->memoryArray = this->newSymbolicExpression(cell, MEMORY_EXPRESSION, "Byte reference - " + comment);
            this->memoryArray->setOriginMemory(triton::arch::MemoryAccess((address + writeSize) - 1, triton::size::byte));
            this->addBitvectorMemory((address + writeSize) - 1, this->memoryArray);
          }
          /* Symbolic bitvector */
          else {
            se = this->newSymbolicExpression(tmp, MEMORY_EXPRESSION, "Byte reference - " + comment);
            se->setOriginMemory(triton::arch::MemoryAccess(((address + writeSize) - 1), triton::size::byte));
            this->addBitvectorMemory((address + writeSize) - 1, se);
          }

          /* continue */
          writeSize--;
        }

        /* Set implicit read of the base and index registers from an effective address */
        this->setImplicitReadRegisterFromEffectiveAddress(inst, mem);

        /* Set explicit write of the memory access */
        inst.setStoreAccess(mem, node);

        /* Synchronize the concrete state */
        this->architecture->setConcreteMemoryValue(mem, node->evaluate());

        /* Keep a symbolic expression that represents the original store assignment */
        se = this->newSymbolicExpression(node, MEMORY_EXPRESSION, "Original memory access - " + comment);
        se->setOriginMemory(mem);

        return this->addSymbolicExpressions(inst, id);
      }


      /* Returns the parent AST after inserting the subregister (node) in its AST. */
      triton::ast::SharedAbstractNode SymbolicEngine::insertSubRegisterInParent(const triton::arch::Register& reg, const triton::ast::SharedAbstractNode& node, bool zxForAssign) {
        const triton::arch::Register& parentReg = this->architecture->getParentRegister(reg);

        /* If it's a flag register, there is nothing to do with sub register */
        if (this->architecture->isFlag(reg)) {
          return node;
        }

        switch (reg.getSize()) {
          /* ----------------------------------------------------------------*/
          case triton::size::byte: {
            const auto& origReg = this->getRegisterAst(parentReg);
            /*
             * Mainly used for x86
             * r[........xxxxxxxx]
             */
            if (reg.getLow() == 0) {
              const auto& keep = this->astCtxt->extract((parentReg.getBitSize() - 1), bitsize::byte, origReg);
              return this->astCtxt->concat(keep, node);
            }
            /*
             * Mainly used for x86
             * r[xxxxxxxx........]
             */
            else {
              const auto& keep = this->astCtxt->extract((parentReg.getBitSize() - 1), bitsize::word, origReg);
              return this->astCtxt->concat(keep, this->astCtxt->concat(node, this->astCtxt->extract((bitsize::byte - 1), 0, origReg)));
            }
          }

          /* ----------------------------------------------------------------*/
          case triton::size::word: {
            const auto& origReg = this->getRegisterAst(parentReg);
            return this->astCtxt->concat(this->astCtxt->extract((parentReg.getBitSize() - 1), bitsize::word, origReg), node);
          }

          /* ----------------------------------------------------------------*/
          case triton::size::dword:
          case triton::size::qword:
          case triton::size::fword:
          case triton::size::dqword:
          case triton::size::qqword:
          case triton::size::dqqword: {
            if (zxForAssign == false) {
              if (parentReg.getBitSize() > reg.getBitSize()) {
                const auto& origReg = this->getRegisterAst(parentReg);
                return this->astCtxt->concat(this->astCtxt->extract((parentReg.getBitSize() - 1), reg.getHigh() + 1, origReg), node);
              }
              else {
                return node;
              }
            }
            /* zxForAssign == true */
            else {
              return this->astCtxt->zx(parentReg.getBitSize() - node->getBitvectorSize(), node);
            }
          }
          /* ----------------------------------------------------------------*/
        }

        throw triton::exceptions::SymbolicEngine("SymbolicEngine::insertSubRegisterInParent(): Invalid register size.");
      }


      /* Returns the new symbolic register expression */
      const SharedSymbolicExpression& SymbolicEngine::createSymbolicRegisterExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const triton::arch::Register& reg, const std::string& comment) {
        triton::usize id = this->uniqueSymExprId;
        SharedSymbolicExpression se = nullptr;

        se = this->newSymbolicExpression(this->insertSubRegisterInParent(reg, node), REGISTER_EXPRESSION, comment);
        this->assignSymbolicExpressionToRegister(se, this->architecture->getParentRegister(reg));

        inst.setWrittenRegister(reg, node);
        return this->addSymbolicExpressions(inst, id);
      }


      /* Returns the new symbolic volatile expression */
      const SharedSymbolicExpression& SymbolicEngine::createSymbolicVolatileExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const std::string& comment) {
        triton::usize id = this->uniqueSymExprId;
        const SharedSymbolicExpression& se = this->newSymbolicExpression(node, VOLATILE_EXPRESSION, comment);
        return this->addSymbolicExpressions(inst, id);
      }


      /* Adds a symbolic expression to the bitvector memory model */
      inline void SymbolicEngine::addBitvectorMemory(triton::uint64 mem, const SharedSymbolicExpression& expr) {
        this->memoryBitvector[mem] = expr;
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
        if (node->getBitvectorSize() != mem.getBitSize()) {
          throw triton::exceptions::SymbolicEngine("SymbolicEngine::assignSymbolicExpressionToMemory(): The size of the symbolic expression is not equal to the memory access.");
        }

        /* Record the aligned memory for a symbolic optimization */
        if (this->isAlignedMode() && this->isArrayMode() == false) {
          this->addAlignedMemory(address, writeSize, se);
        }

        /*
         * As the x86's memory can be accessed without alignment, each byte of the
         * memory must be assigned to an unique reference.
         */
        while (writeSize) {
          triton::uint32 high = ((writeSize * bitsize::byte) - 1);
          triton::uint32 low  = ((writeSize * bitsize::byte) - bitsize::byte);

          /* Extract each byte of the memory */
          const triton::ast::SharedAbstractNode& tmp = this->astCtxt->extract(high, low, node);

          /* Symbolic array */
          if (this->isArrayMode()) {
            const auto& cell = this->astCtxt->store(this->astCtxt->reference(this->getMemoryArray()), ((address + writeSize) - 1), tmp);
            this->memoryArray = this->newSymbolicExpression(cell, MEMORY_EXPRESSION, "Byte reference");
            this->memoryArray->setOriginMemory(triton::arch::MemoryAccess(((address + writeSize) - 1), triton::size::byte));
            this->addBitvectorMemory((address + writeSize) - 1, this->memoryArray);
          }
          /* Symbolic bitvector */
          else {
            const SharedSymbolicExpression& se = this->newSymbolicExpression(tmp, MEMORY_EXPRESSION, "Byte reference");
            se->setOriginMemory(triton::arch::MemoryAccess(((address + writeSize) - 1), triton::size::byte));
            this->addBitvectorMemory((address + writeSize) - 1, se);
          }

          writeSize--;
        }

        /* Synchronize the concrete state */
        this->architecture->setConcreteMemoryValue(mem, node->evaluate());
      }


      /* Returns true if the symbolic expression ID exists */
      bool SymbolicEngine::isSymbolicExpressionExists(triton::usize symExprId) const {
        auto it = this->symbolicExpressions.find(symExprId);

        if (it != this->symbolicExpressions.end()) {
          return (it->second.use_count() > 0);
        }

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
          if (expr && expr->isSymbolized()) {
            return true;
          }
        }
        return false;
      }


      /* Returns true if the register expression contains a symbolic variable. */
      bool SymbolicEngine::isRegisterSymbolized(const triton::arch::Register& reg) const {
        const SharedSymbolicExpression& expr = this->getSymbolicRegister(reg);
        if (expr) {
          return expr->isSymbolized();
        }
        return false;
      }


      /* Initializes the memory access AST (LOAD and STORE) */
      void SymbolicEngine::initLeaAst(triton::arch::MemoryAccess& mem, bool force) const {
        if (mem.getBitSize() >= bitsize::byte) {
          const triton::arch::Register& base  = mem.getConstBaseRegister();
          const triton::arch::Register& index = mem.getConstIndexRegister();
          const triton::arch::Register& seg   = mem.getConstSegmentRegister();
          triton::uint64 scaleValue           = mem.getConstScale().getValue();
          triton::uint64 dispValue            = mem.getConstDisplacement().getValue();
          triton::uint32 bitSize              = (this->architecture->isRegisterValid(base) ? base.getBitSize() :
                                                  (this->architecture->isRegisterValid(index) ? index.getBitSize() :
                                                    (mem.getConstDisplacement().getBitSize() ? mem.getConstDisplacement().getBitSize() :
                                                      this->architecture->gprBitSize()
                                                    )
                                                  )
                                                );

          /* Initialize the AST of the memory access (LEA) -> ((pc + base) + (index * scale) + disp) */
          auto pcPlusBaseAst    = mem.getPcRelative() ? this->astCtxt->bv(mem.getPcRelative(), bitSize) :
                                    (this->architecture->isRegisterValid(base) ? this->getRegisterAst(base) :
                                      this->astCtxt->bv(0, bitSize));

          auto indexMulScaleAst = this->astCtxt->bvmul(
                                    (this->architecture->isRegisterValid(index) ? this->getRegisterAst(index) : this->astCtxt->bv(0, bitSize)),
                                    this->astCtxt->bv(scaleValue, bitSize)
                                  );

          auto dispAst          = this->astCtxt->bv(dispValue, bitSize);
          auto leaAst           = this->astCtxt->bvadd(
                                    index.isSubtracted() ? this->astCtxt->bvsub(pcPlusBaseAst, indexMulScaleAst) : this->astCtxt->bvadd(pcPlusBaseAst, indexMulScaleAst),
                                    dispAst
                                  );

          /* Use segments as base address instead of selector into the GDT. */
          if (this->architecture->isRegisterValid(seg)) {
            leaAst = this->astCtxt->bvadd(
                       this->getRegisterAst(seg),
                       this->astCtxt->sx((seg.getBitSize() - bitSize), leaAst)
                     );
          }

          /* Set AST */
          mem.setLeaAst(leaAst);

          /* Initialize the address only if it is not already defined */
          if (!mem.getAddress() || force)
            mem.setAddress(static_cast<triton::uint64>(leaAst->evaluate()));
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

        else if (symVar->getType() == MEMORY_VARIABLE && symVar->getSize() && !(symVar->getSize() % bitsize::byte)) {
          triton::uint64 addr            = symVar->getOrigin();
          triton::uint32 size            = symVar->getSize() / bitsize::byte;
          triton::arch::MemoryAccess mem = triton::arch::MemoryAccess(addr, size);

          this->architecture->setConcreteMemoryValue(mem, value, false);
        }
      }


      inline bool SymbolicEngine::isAlignedMode(void) const {
        return this->modes->isModeEnabled(triton::modes::ALIGNED_MEMORY);
      }


      inline bool SymbolicEngine::isArrayMode(void) const {
        return this->modes->isModeEnabled(triton::modes::MEMORY_ARRAY);
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */
