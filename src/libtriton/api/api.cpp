//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>
#include <map>
#include <list>

#include <api.hpp>



/*!

\mainpage Triton: Dynamic Binary Analysis Framework

\tableofcontents

\section description_sec Description

Triton is a dynamic binary analysis (DBA) framework. It provides internal components
like a \ref engine_DSE_page (DSE) engine, a \ref engine_Taint_page, an intermediate representation based on \ref py_smt2lib_page of the x86 and x86-64
instructions set, \ref SMT_simplification_page, an \ref solver_interface_page and, the last but not least,
\ref py_triton_page. Based on these components, you are able to build program analysis tools,
automate reverse engineering and perform software verification.


<br>
<hr>
\section publications_sec Presentations and Publications

<ul>
  <li><b>How Triton may help to analyse obfuscated binaries</b><br>
  MISC magazine 82, 2015.
  [<a href="http://triton.quarkslab.com/files/misc82-triton.pdf">french article</a>]<br>
  Abstract: <i>Binary obfuscation is used to protect software's intellectual property.
  There exist different kinds of obfucation but roughly, it transforms a binary structure
  into another binary structure by preserving the same semantic. The aim of obfuscation is
  to ensure that the original information is "drown" in useless information that will make
  reverse engineering harder. In this article we will show how we can analyse an ofbuscated
  program and break some obfuscations using the Triton framework.</i></li>

  <li><b>Triton: A Concolic Execution Framework</b><br>
  Talk at SSTIC, Rennes, 2015.
  [<a href="http://triton.quarkslab.com/files/sstic2015_wp_fr_saudel_salwan.pdf">french paper</a>]
  [<a href="http://triton.quarkslab.com/files/sstic2015_slide_en_saudel_salwan.pdf">detailed english slide</a>]
  [<a href="http://triton.quarkslab.com/files/sstic2015_slide_fr_saudel_salwan.pdf">light french slide</a>]
  [<a href="http://triton.quarkslab.com/files/TritonSSTIC2015.txt">bibtex</a>]<br>
  Abstract: <i>This talk is about the release of Triton, a concolic execution framework based on Pin.
  It provides components like a taint engine, a dynamic symbolic execution engine, a snapshot engine,
  translation of x64 instruction to SMT2, a Z3 interface to solve constraints and Python bindings.
  Based on these components, Triton offers the possibility to build tools for vulnerabilities research or
  reverse-engineering assistance.</i></li>

  <li><b>Dynamic Behavior Analysis Using Binary Instrumentation</b><br>
  Talk at St'Hack, Bordeaux, 2015.
  [<a href="http://triton.quarkslab.com/files/sthack2015_salwan.pdf">slide</a>]<br>
  Abstract: <i>This talk can be considered like the part 2 of our talk at SecurityDay.
  In the previous part, we talked about how it was possible to cover a targeted
  function in memory using the DSE (Dynamic Symbolic Execution) approach. Cover
  a function (or its states) doesn't mean find all vulnerabilities, some vulnerability
  doesn't crashes the program. That's why we must implement specific analysis to
  find specific bugs. These analysis are based on the binary instrumentation and
  the runtime behavior analysis of the program. In this talk, we will see how it's
  possible to find these following kind of bugs : off-by-one, stack / heap overflow,
  use-after-free, format string and {write, read}-what-where.</i></li>

  <li><b>Covering a function using a Dynamic Symbolic Execution approach</b><br>
  Talk at Security Day, Lille, 2015.
  [<a href="http://triton.quarkslab.com/files/secday2015_salwan.pdf">slide</a>]<br>
  Abstract: <i>This talk is about binary analysis and instrumentation. We will see how it's possible to
  target a specific function, snapshot the context memory/registers before the function, translate the instrumentation
  into an intermediate representation,apply a taint analysis based on this IR, build/keep formulas for a Dynamic
  Symbolic Execution (DSE), generate a concrete value to go through a specific path, restore the context memory/register and
  generate another concrete value to go through another path then repeat this operation until the target function is covered.</i></li>
</ul>


<br>
<hr>
\section install_sec Installation

To be able to compile Triton, you must install these libraries before:

 lib name                                                                      | version
-------------------------------------------------------------------------------|---------
 [libboost](http://www.boost.org/)                                             | >= 1.58
 [libpython](https://www.python.org/)                                          | 2.7.x
 [libz3](https://github.com/Z3Prover/z3)                                       | n/a
 [libcapstone](http://www.capstone-engine.org/)                                | >= 3.0
 [Pin](https://software.intel.com/en-us/articles/pintool-downloads) (optional) | 71313

Once libraries installed, you can use `cmake` to build the `libTriton`.

~~~~~~~~~~~~~{.sh}
$ git clone https://github.com/JonathanSalwan/Triton.git
$ cd Triton
$ mkdir build
$ cd build
$ cmake ..
$ make
$ sudo make install
$ cd ..
$ sudo python ./setup.py install
~~~~~~~~~~~~~

This project is also shipped with a Pin \ref Tracer_page and may be compiled with these following commands:

~~~~~~~~~~~~~{.sh}
$ cd pin-2.14-71313-gcc.4.4.7-linux/source/tools/
$ git clone https://github.com/JonathanSalwan/Triton.git
$ cd Triton
$ mkdir build
$ cd build
$ cmake -DPINTOOL=yes ..
$ make
$ cd ..
$ ./triton ./src/examples/pin/ir.py /usr/bin/id
~~~~~~~~~~~~~

It's not recommended to use the pintool on a kernel `4.x`. The last version of Pin doesn't support very well this branch (`4.x`). Anyway, if you feel lucky, you can compile the Triton pintool with the `-DKERNEL4=yes` flag.

~~~~~~~~~~~~~{.sh}
$ cmake -DPINTOOL=yes -DKERNEL4=yes ..
$ make
~~~~~~~~~~~~~

*/



namespace triton {

  /* External access to the API */
  API api = API();


  API::API() {
    this->arch      = arch::Architecture();
    this->taint     = nullptr;
    this->sym       = nullptr;
    this->symBackup = nullptr;
    this->solver    = nullptr;
  }


  API::~API() {
    this->removeEngines();
  }



  /* Architecture API ============================================================================== */

  bool API::isArchitectureValid(void) {
    return this->arch.isValid();
  }


  uint32 API::getArchitecture(void) const {
    return this->arch.getArchitecture();
  }


  void API::checkArchitecture(void) {
    if (!this->isArchitectureValid())
      throw std::runtime_error("API::checkArchitecture(): You must define an architecture.");
  }


  triton::arch::AbstractCpu* API::getCpu(void) {
    if (!this->isArchitectureValid())
      throw std::runtime_error("API::checkArchitecture(): You must define an architecture.");
    return this->arch.getCpu();
  }


  void API::setArchitecture(uint32 arch) {
    /* Setup and init the targetd architecture */
    this->arch.setArchitecture(arch);
    this->initEngines();
  }


  void API::clearArchitecture(void) {
    this->checkArchitecture();
    this->arch.clearArchitecture();
  }


  bool API::isCpuFlag(triton::uint32 regId) {
    return this->arch.isFlag(regId);
  }


  bool API::isCpuReg(triton::uint32 regId) {
    return this->arch.isReg(regId);
  }


  bool API::isCpuRegValid(triton::uint32 regId) {
    return this->arch.isRegValid(regId);
  }


  triton::uint32 API::cpuRegSize(void) {
    return this->arch.regSize();
  }


  triton::uint32 API::cpuRegBitSize(void) {
    return this->arch.regBitSize();
  }


  triton::uint32 API::cpuInvalidReg(void) {
    return this->arch.invalidReg();
  }


  triton::uint32 API::cpuNumberOfReg(void) {
    return this->arch.numberOfReg();
  }


  std::tuple<std::string, triton::uint32, triton::uint32, triton::uint32> API::getCpuRegInformation(triton::uint32 reg) {
    return this->arch.getRegInfo(reg);
  }


  std::set<triton::arch::RegisterOperand*> API::getParentRegisters(void) {
    this->checkArchitecture();
    return this->arch.getParentRegisters();
  }


  triton::uint8 API::getLastMemoryValue(triton::__uint addr) {
    return this->arch.getLastMemoryValue(addr);
  }


  triton::uint128 API::getLastMemoryValue(triton::arch::MemoryOperand& mem) {
    return this->arch.getLastMemoryValue(mem);
  }


  triton::uint128 API::getLastRegisterValue(triton::arch::RegisterOperand& reg) {
    return this->arch.getLastRegisterValue(reg);
  }


  void API::setLastMemoryValue(triton::__uint addr, triton::uint8 value) {
    this->arch.setLastMemoryValue(addr, value);
  }


  void API::setLastMemoryValue(triton::arch::MemoryOperand& mem) {
    this->arch.setLastMemoryValue(mem);
  }


  void API::setLastRegisterValue(triton::arch::RegisterOperand& reg) {
    this->arch.setLastRegisterValue(reg);
  }


  void API::disassembly(triton::arch::Instruction& inst) {
    this->checkArchitecture();
    this->arch.disassembly(inst);
  }


  void API::buildSemantics(triton::arch::Instruction& inst) {
    this->checkArchitecture();

    /* Stage 1 - Update the context memory */
    std::list<triton::arch::MemoryOperand>::iterator it1;
    for (it1 = inst.memoryAccess.begin(); it1 != inst.memoryAccess.end(); it1++) {
      this->setLastMemoryValue(*it1);
    }

    /* Stage 2 - Update the context register */
    std::map<triton::uint32, triton::arch::RegisterOperand>::iterator it2;
    for (it2 = inst.registerState.begin(); it2 != inst.registerState.end(); it2++) {
      this->setLastRegisterValue(it2->second);
    }

    /* Stage 3 - Process the IR */
    this->arch.buildSemantics(inst);
  }



  /* Processing API ================================================================================ */

  void API::initEngines(void) {
    this->checkArchitecture();

    this->taint = new triton::engines::taint::TaintEngine();
    if (!this->taint)
      throw std::invalid_argument("API::initEngines(): No enough memory.");

    this->sym = new triton::engines::symbolic::SymbolicEngine();
    if (!this->sym)
      throw std::invalid_argument("API::initEngines(): No enough memory.");

    this->symBackup = new triton::engines::symbolic::SymbolicEngine();
    if (!this->symBackup)
      throw std::invalid_argument("API::initEngines(): No enough memory.");

    this->solver = new triton::engines::solver::SolverEngine();
    if (!this->solver)
      throw std::invalid_argument("API::initEngines(): No enough memory.");
  }


  void API::removeEngines(void) {
    if(this->isArchitectureValid()) {
      delete this->taint;
      delete this->sym;
      delete this->symBackup;
      delete this->solver;
    }
  }


  void API::resetEngines(void) {
    if(this->isArchitectureValid()) {
      this->removeEngines();
      this->initEngines();
      this->clearArchitecture();
      smt2lib::freeAllAstNodes();
    }
  }


  void API::processing(triton::arch::Instruction& inst) {
    this->checkArchitecture();
    this->disassembly(inst);
    this->buildSemantics(inst);
  }



  /* Symbolic Engine API ============================================================================ */

  void API::checkSymbolic(void) {
    if (!this->sym || !this->symBackup)
      throw std::runtime_error("API::checkSymbolic(): Symbolic engine is undefined.");
  }


  void API::backupSymbolicEngine(void) {
    *this->symBackup = *this->sym;
  }


  void API::restoreSymbolicEngine(void) {
    *this->sym = *this->symBackup;
  }


  triton::engines::symbolic::SymbolicEngine* API::getSymbolicEngine(void) {
    this->checkSymbolic();
    return this->sym;
  }


  triton::engines::symbolic::SymbolicVariable* API::convertExprToSymVar(triton::__uint exprId, triton::uint32 symVarSize, std::string symVarComment) {
    this->checkSymbolic();
    return this->sym->convertExprToSymVar(exprId, symVarSize, symVarComment);
  }


  triton::engines::symbolic::SymbolicVariable* API::convertMemToSymVar(triton::arch::MemoryOperand mem, std::string symVarComment) {
    this->checkSymbolic();
    return this->sym->convertMemToSymVar(mem, symVarComment);
  }


  triton::engines::symbolic::SymbolicVariable* API::convertRegToSymVar(triton::arch::RegisterOperand reg, std::string symVarComment) {
    this->checkSymbolic();
    return this->sym->convertRegToSymVar(reg, symVarComment);
  }


  smt2lib::smtAstAbstractNode* API::buildSymbolicOperand(triton::arch::OperandWrapper& op) {
    this->checkSymbolic();
    switch (op.getType()) {
      case triton::arch::OP_IMM: return this->buildSymbolicImmediateOperand(op.getImm());
      case triton::arch::OP_MEM: return this->buildSymbolicMemoryOperand(op.getMem());
      case triton::arch::OP_REG: return this->buildSymbolicRegisterOperand(op.getReg());
      default:
        throw std::runtime_error("API::buildSymbolicOperand(): Invalid operand.");
    }
  }


  smt2lib::smtAstAbstractNode* API::buildSymbolicImmediateOperand(triton::arch::ImmediateOperand& imm) {
    this->checkSymbolic();
    return this->sym->buildSymbolicImmediateOperand(imm);
  }


  smt2lib::smtAstAbstractNode* API::buildSymbolicMemoryOperand(triton::arch::MemoryOperand& mem) {
    this->checkSymbolic();
    return this->sym->buildSymbolicMemoryOperand(mem);
  }


  smt2lib::smtAstAbstractNode* API::buildSymbolicRegisterOperand(triton::arch::RegisterOperand& reg) {
    this->checkSymbolic();
    return this->sym->buildSymbolicRegisterOperand(reg);
  }


  triton::engines::symbolic::SymbolicExpression* API::newSymbolicExpression(smt2lib::smtAstAbstractNode* node, std::string comment) {
    this->checkSymbolic();
    return this->sym->newSymbolicExpression(node, triton::engines::symbolic::UNDEF, comment);
  }


  triton::engines::symbolic::SymbolicVariable* API::newSymbolicVariable(triton::uint32 varSize, std::string comment) {
    this->checkSymbolic();
    return this->sym->newSymbolicVariable(triton::engines::symbolic::UNDEF, 0, varSize, comment);
  }


  void API::removeSymbolicExpression(triton::__uint symExprId) {
    this->checkSymbolic();
    return this->sym->removeSymbolicExpression(symExprId);
  }


  triton::engines::symbolic::SymbolicExpression* API::createSymbolicExpression(triton::arch::Instruction& inst, smt2lib::smtAstAbstractNode* node, triton::arch::OperandWrapper& dst, std::string comment) {
    this->checkSymbolic();
    switch (dst.getType()) {
      case triton::arch::OP_MEM: return this->createSymbolicMemoryExpression(inst, node, dst.getMem(), comment);
      case triton::arch::OP_REG: return this->createSymbolicRegisterExpression(inst, node, dst.getReg(), comment);
      default:
        throw std::runtime_error("API::buildSymbolicOperand(): Invalid operand.");
    }
    return nullptr;
  }


  triton::engines::symbolic::SymbolicExpression* API::createSymbolicMemoryExpression(triton::arch::Instruction& inst, smt2lib::smtAstAbstractNode* node, triton::arch::MemoryOperand& mem, std::string comment) {
    this->checkSymbolic();
    return this->sym->createSymbolicMemoryExpression(inst, node, mem, comment);
  }


  triton::engines::symbolic::SymbolicExpression* API::createSymbolicRegisterExpression(triton::arch::Instruction& inst, smt2lib::smtAstAbstractNode* node, triton::arch::RegisterOperand& reg, std::string comment) {
    this->checkSymbolic();
    return this->sym->createSymbolicRegisterExpression(inst, node, reg, comment);
  }


  triton::engines::symbolic::SymbolicExpression* API::createSymbolicFlagExpression(triton::arch::Instruction& inst, smt2lib::smtAstAbstractNode* node, triton::arch::RegisterOperand& flag, std::string comment) {
    this->checkSymbolic();
    return this->sym->createSymbolicFlagExpression(inst, node, flag, comment);
  }


  triton::engines::symbolic::SymbolicExpression* API::createSymbolicVolatileExpression(triton::arch::Instruction& inst, smt2lib::smtAstAbstractNode* node, std::string comment) {
    this->checkSymbolic();
    return this->sym->createSymbolicVolatileExpression(inst, node, comment);
  }


  void API::assignSymbolicExpressionToRegister(triton::engines::symbolic::SymbolicExpression* se, triton::arch::RegisterOperand& reg) {
    this->checkSymbolic();
    this->sym->assignSymbolicExpressionToRegister(se, reg);
  }


  triton::__uint API::getSymbolicMemoryId(triton::__uint addr) {
    this->checkSymbolic();
    return this->sym->getSymbolicMemoryId(addr);
  }


  triton::__uint API::getSymbolicRegisterId(triton::arch::RegisterOperand& reg) {
    this->checkSymbolic();
    return this->sym->getSymbolicRegisterId(reg);
  }


  void API::recordSimplificationCallback(triton::engines::symbolic::sfp cb) {
    this->checkSymbolic();
    return this->sym->recordSimplificationCallback(cb);
  }


  #ifdef TRITON_PYTHON_BINDINGS
  void API::recordSimplificationCallback(PyObject* cb) {
    this->checkSymbolic();
    return this->sym->recordSimplificationCallback(cb);
  }
  #endif


  void API::removeSimplificationCallback(triton::engines::symbolic::sfp cb) {
    this->checkSymbolic();
    return this->sym->removeSimplificationCallback(cb);
  }


  #ifdef TRITON_PYTHON_BINDINGS
  void API::removeSimplificationCallback(PyObject* cb) {
    this->checkSymbolic();
    return this->sym->removeSimplificationCallback(cb);
  }
  #endif


  smt2lib::smtAstAbstractNode* API::browseAstSummaries(smt2lib::smtAstAbstractNode* node) {
    this->checkSymbolic();
    return this->sym->browseAstSummaries(node);
  }


  std::map<std::string, triton::uint32> API::getAstSummariesStats(void) {
    this->checkSymbolic();
    return this->sym->getAstSummariesStats();
  }


  smt2lib::smtAstAbstractNode* API::processSimplification(smt2lib::smtAstAbstractNode* node) {
    this->checkSymbolic();
    return this->sym->processSimplification(node);
  }


  triton::engines::symbolic::SymbolicExpression* API::getSymbolicExpressionFromId(triton::__uint symExprId) {
    this->checkSymbolic();
    return this->sym->getSymbolicExpressionFromId(symExprId);
  }


  triton::engines::symbolic::SymbolicVariable* API::getSymbolicVariableFromId(triton::__uint symVarId) {
    this->checkSymbolic();
    return this->sym->getSymbolicVariableFromId(symVarId);
  }


  triton::engines::symbolic::SymbolicVariable* API::getSymbolicVariableFromName(std::string& symVarName) {
    this->checkSymbolic();
    return this->sym->getSymbolicVariableFromName(symVarName);
  }


  void API::enableSymbolicEngine(bool flag) {
    this->checkSymbolic();
    this->sym->enable(flag);
  }


  void API::enableSymbolicOptimization(enum triton::engines::symbolic::optimization_e opti) {
    this->checkSymbolic();
    this->sym->enableOptimization(opti);
  }


  void API::disableSymbolicOptimization(enum triton::engines::symbolic::optimization_e opti) {
    this->checkSymbolic();
    this->sym->disableOptimization(opti);
  }


  bool API::isSymbolicEngineEnabled(void) {
    this->checkSymbolic();
    return this->sym->isEnabled();
  }


  bool API::isSymbolicExpressionIdExists(triton::__uint symExprId) {
    this->checkSymbolic();
    return this->sym->isSymbolicExpressionIdExists(symExprId);
  }


  bool API::isSymbolicOptimizationEnabled(enum triton::engines::symbolic::optimization_e opti) {
    this->checkSymbolic();
    return this->sym->isOptimizationEnabled(opti);
  }


  void API::concretizeAllMem(void) {
    this->checkSymbolic();
    this->sym->concretizeAllMem();
  }


  void API::concretizeAllReg(void) {
    this->checkSymbolic();
    this->sym->concretizeAllReg();
  }


  void API::concretizeMem(triton::arch::MemoryOperand& mem) {
    this->checkSymbolic();
    this->sym->concretizeMem(mem);
  }


  void API::concretizeMem(triton::__uint addr) {
    this->checkSymbolic();
    this->sym->concretizeMem(addr);
  }


  void API::concretizeReg(triton::arch::RegisterOperand& reg) {
    this->checkSymbolic();
    this->sym->concretizeReg(reg);
  }


  smt2lib::smtAstAbstractNode* API::getFullAst(smt2lib::smtAstAbstractNode* node) {
    this->checkSymbolic();
    return this->sym->getFullAst(node);
  }


  smt2lib::smtAstAbstractNode* API::getAstFromId(triton::__uint symExprId) {
    this->checkSymbolic();
    triton::engines::symbolic::SymbolicExpression* symExpr = this->getSymbolicExpressionFromId(symExprId);
    return symExpr->getAst();
  }


  smt2lib::smtAstAbstractNode* API::getFullAstFromId(triton::__uint symExprId) {
    this->checkSymbolic();
    smt2lib::smtAstAbstractNode* partialAst = this->getAstFromId(symExprId);
    return this->getFullAst(partialAst);
  }


  std::list<triton::engines::symbolic::SymbolicExpression*> API::getTaintedSymbolicExpressions(void) {
    this->checkSymbolic();
    return this->sym->getTaintedSymbolicExpressions();
  }


  std::map<triton::__uint, triton::engines::symbolic::SymbolicExpression*>& API::getSymbolicExpressions(void) {
    this->checkSymbolic();
    return this->sym->getSymbolicExpressions();
  }


  std::map<triton::__uint, triton::engines::symbolic::SymbolicVariable*>& API::getSymbolicVariables(void) {
    this->checkSymbolic();
    return this->sym->getSymbolicVariables();
  }


  std::string API::getVariablesDeclaration(void) {
    this->checkSymbolic();
    return this->sym->getVariablesDeclaration();
  }



  /* Solver Engine API ============================================================================= */

  void API::checkSolver(void) {
    if (!this->solver)
      throw std::runtime_error("API::checkSolver(): Solver engine is undefined.");
  }


  std::map<triton::uint32, triton::engines::solver::SolverModel> API::getModel(smt2lib::smtAstAbstractNode *node) {
    this->checkSolver();
    return this->solver->getModel(node);
  }


  std::list<std::map<triton::uint32, triton::engines::solver::SolverModel>> API::getModels(smt2lib::smtAstAbstractNode *node, triton::uint32 limit) {
    this->checkSolver();
    return this->solver->getModels(node, limit);
  }


  triton::uint512 API::evaluateAst(smt2lib::smtAstAbstractNode *node) {
    this->checkSolver();
    return this->solver->evaluateAst(node);
  }



  /* Taint engine API ============================================================================== */

  void API::checkTaint(void) {
    if (!this->taint)
      throw std::runtime_error("API::checkTaint(): Taint engine is undefined.");
  }


  triton::engines::taint::TaintEngine* API::getTaintEngine(void) {
    this->checkTaint();
    return this->taint;
  }


  void API::enableTaintEngine(bool flag) {
    this->checkTaint();
    this->taint->enable(flag);
  }


  bool API::isTaintEngineEnabled(void) {
    this->checkTaint();
    return this->taint->isEnabled();
  }


  bool API::isAddrTainted(__uint addr, uint32 size) {
    this->checkTaint();
    return this->taint->isAddrTainted(addr, size);
  }


  bool API::isTainted(arch::OperandWrapper& op) {
    this->checkTaint();
    switch (op.getType()) {
      case triton::arch::OP_IMM: return triton::engines::taint::UNTAINTED;
      case triton::arch::OP_MEM: return this->isMemTainted(op.getMem());
      case triton::arch::OP_REG: return this->isRegTainted(op.getReg());
      default:
        throw std::runtime_error("API::isTainted(): Invalid operand.");
    }
  }


  bool API::isMemTainted(arch::MemoryOperand& mem) {
    this->checkTaint();
    return this->taint->isMemTainted(mem);
  }


  bool API::isRegTainted(arch::RegisterOperand& reg) {
    this->checkTaint();
    return this->taint->isRegTainted(reg);
  }


  bool API::setTaint(arch::OperandWrapper& op, bool flag) {
    this->checkTaint();
    switch (op.getType()) {
      case triton::arch::OP_IMM: return triton::engines::taint::UNTAINTED;
      case triton::arch::OP_MEM: return this->setTaintMem(op.getMem(), flag);
      case triton::arch::OP_REG: return this->setTaintReg(op.getReg(), flag);
      default:
        throw std::runtime_error("API::setTaint(): Invalid operand.");
    }
  }


  bool API::setTaintMem(arch::MemoryOperand& mem, bool flag) {
    this->checkTaint();
    this->taint->setTaintMem(mem, flag);
    return flag;
  }


  bool API::setTaintReg(arch::RegisterOperand& reg, bool flag) {
    this->checkTaint();
    this->taint->setTaintReg(reg, flag);
    return flag;
  }


  bool API::taintAddr(__uint addr) {
    this->checkTaint();
    return this->taint->taintAddr(addr);
  }


  bool API::taintMem(arch::MemoryOperand& mem) {
    this->checkTaint();
    return this->taint->taintMem(mem);
  }


  bool API::taintReg(arch::RegisterOperand& reg) {
    this->checkTaint();
    return this->taint->taintReg(reg);
  }


  bool API::untaintAddr(__uint addr) {
    this->checkTaint();
    return this->taint->untaintAddr(addr);
  }


  bool API::untaintMem(arch::MemoryOperand& mem) {
    this->checkTaint();
    return this->taint->untaintMem(mem);
  }


  bool API::untaintReg(arch::RegisterOperand& reg) {
    this->checkTaint();
    return this->taint->untaintReg(reg);
  }


  bool API::taintUnion(triton::arch::OperandWrapper& op1, triton::arch::OperandWrapper& op2) {
    triton::uint32 t1 = op1.getType();
    triton::uint32 t2 = op2.getType();

    if (t1 == triton::arch::OP_MEM && t2 == triton::arch::OP_IMM)
      return this->taintUnionMemImm(op1.getMem());

    if (t1 == triton::arch::OP_MEM && t2 == triton::arch::OP_MEM)
      return this->taintUnionMemMem(op1.getMem(), op2.getMem());

    if (t1 == triton::arch::OP_MEM && t2 == triton::arch::OP_REG)
      return this->taintUnionMemReg(op1.getMem(), op2.getReg());

    if (t1 == triton::arch::OP_REG && t2 == triton::arch::OP_IMM)
      return this->taintUnionRegImm(op1.getReg());

    if (t1 == triton::arch::OP_REG && t2 == triton::arch::OP_MEM)
      return this->taintUnionRegMem(op1.getReg(), op2.getMem());

    if (t1 == triton::arch::OP_REG && t2 == triton::arch::OP_REG)
      return this->taintUnionRegReg(op1.getReg(), op2.getReg());

    throw std::runtime_error("API::taintUnion(): Invalid operands.");
  }


  bool API::taintAssignment(triton::arch::OperandWrapper& op1, triton::arch::OperandWrapper& op2) {
    triton::uint32 t1 = op1.getType();
    triton::uint32 t2 = op2.getType();

    if (t1 == triton::arch::OP_MEM && t2 == triton::arch::OP_IMM)
      return this->taintAssignmentMemImm(op1.getMem());

    if (t1 == triton::arch::OP_MEM && t2 == triton::arch::OP_MEM)
      return this->taintAssignmentMemMem(op1.getMem(), op2.getMem());

    if (t1 == triton::arch::OP_MEM && t2 == triton::arch::OP_REG)
      return this->taintAssignmentMemReg(op1.getMem(), op2.getReg());

    if (t1 == triton::arch::OP_REG && t2 == triton::arch::OP_IMM)
      return this->taintAssignmentRegImm(op1.getReg());

    if (t1 == triton::arch::OP_REG && t2 == triton::arch::OP_MEM)
      return this->taintAssignmentRegMem(op1.getReg(), op2.getMem());

    if (t1 == triton::arch::OP_REG && t2 == triton::arch::OP_REG)
      return this->taintAssignmentRegReg(op1.getReg(), op2.getReg());

    throw std::runtime_error("API::taintAssignment(): Invalid operands.");
  }


  bool API::taintUnionMemImm(arch::MemoryOperand& memDst) {
    this->checkTaint();

    bool flag = triton::engines::taint::UNTAINTED;
    triton::__uint memAddrDst = memDst.getAddress();
    triton::uint32 writeSize  = memDst.getSize();

    flag = this->taint->unionMemImm(memDst);

    /* Taint each byte of reference expression */
    for (triton::uint32 i = 0; i != writeSize; i++) {
      triton::__uint byteId = this->getSymbolicMemoryId(memAddrDst + i);
      if (byteId == triton::engines::symbolic::UNSET)
        continue;
      triton::engines::symbolic::SymbolicExpression* byte = this->getSymbolicExpressionFromId(byteId);
      byte->isTainted = flag;
    }

    return flag;
  }


  bool API::taintUnionMemMem(arch::MemoryOperand& memDst, arch::MemoryOperand& memSrc) {
    this->checkTaint();

    bool flag = triton::engines::taint::UNTAINTED;
    triton::__uint memAddrDst = memDst.getAddress();
    triton::__uint memAddrSrc = memSrc.getAddress();
    triton::uint32 writeSize  = memDst.getSize();

    flag = this->taint->unionMemMem(memDst, memSrc);

    /* Taint each byte of reference expression */
    for (triton::uint32 i = 0; i != writeSize; i++) {
      triton::__uint byteId = this->getSymbolicMemoryId(memAddrDst + i);
      if (byteId == triton::engines::symbolic::UNSET)
        continue;
      triton::engines::symbolic::SymbolicExpression* byte = this->getSymbolicExpressionFromId(byteId);
      byte->isTainted = this->isAddrTainted(memAddrDst + i) | this->isAddrTainted(memAddrSrc + i);
    }

    return flag;
  }


  bool API::taintUnionMemReg(arch::MemoryOperand& memDst, arch::RegisterOperand& regSrc) {
    this->checkTaint();

    bool flag = triton::engines::taint::UNTAINTED;
    triton::__uint memAddrDst = memDst.getAddress();
    triton::uint32 writeSize  = memDst.getSize();

    flag = this->taint->unionMemReg(memDst, regSrc);

    /* Taint each byte of reference expression */
    for (triton::uint32 i = 0; i != writeSize; i++) {
      triton::__uint byteId = this->getSymbolicMemoryId(memAddrDst + i);
      if (byteId == triton::engines::symbolic::UNSET)
        continue;
      triton::engines::symbolic::SymbolicExpression* byte = this->getSymbolicExpressionFromId(byteId);
      byte->isTainted = flag;
    }

    return flag;
  }


  bool API::taintUnionRegImm(arch::RegisterOperand& regDst) {
    this->checkTaint();
    return this->taint->unionRegImm(regDst);
  }


  bool API::taintUnionRegMem(arch::RegisterOperand& regDst, arch::MemoryOperand& memSrc) {
    this->checkTaint();
    return this->taint->unionRegMem(regDst, memSrc);
  }


  bool API::taintUnionRegReg(arch::RegisterOperand& regDst, arch::RegisterOperand& regSrc) {
    this->checkTaint();
    return this->taint->unionRegReg(regDst, regSrc);
  }


  bool API::taintAssignmentMemImm(arch::MemoryOperand& memDst) {
    this->checkTaint();

    bool flag = triton::engines::taint::UNTAINTED;
    triton::__uint memAddrDst = memDst.getAddress();
    triton::uint32 writeSize  = memDst.getSize();

    flag = this->taint->assignmentMemImm(memDst);

    /* Taint each byte of reference expression */
    for (triton::uint32 i = 0; i != writeSize; i++) {
      triton::__uint byteId = this->getSymbolicMemoryId(memAddrDst + i);
      if (byteId == triton::engines::symbolic::UNSET)
        continue;
      triton::engines::symbolic::SymbolicExpression* byte = this->getSymbolicExpressionFromId(byteId);
      byte->isTainted = flag;
    }

    return flag;
  }


  bool API::taintAssignmentMemMem(arch::MemoryOperand& memDst, arch::MemoryOperand& memSrc) {
    this->checkTaint();

    bool flag = triton::engines::taint::UNTAINTED;
    triton::__uint memAddrDst = memDst.getAddress();
    triton::__uint memAddrSrc = memSrc.getAddress();
    triton::uint32 writeSize  = memDst.getSize();

    flag = this->taint->assignmentMemMem(memDst, memSrc);

    /* Taint each byte of reference expression */
    for (triton::uint32 i = 0; i != writeSize; i++) {
      triton::__uint byteId = this->getSymbolicMemoryId(memAddrDst + i);
      if (byteId == triton::engines::symbolic::UNSET)
        continue;
      triton::engines::symbolic::SymbolicExpression* byte = this->getSymbolicExpressionFromId(byteId);
      byte->isTainted = this->isAddrTainted(memAddrSrc + i);
    }

    return flag;
  }


  bool API::taintAssignmentMemReg(arch::MemoryOperand& memDst, arch::RegisterOperand& regSrc) {
    this->checkTaint();

    bool flag = triton::engines::taint::UNTAINTED;
    triton::__uint memAddrDst = memDst.getAddress();
    triton::uint32 writeSize  = memDst.getSize();

    flag = this->taint->assignmentMemReg(memDst, regSrc);

    /* Taint each byte of reference expression */
    for (triton::uint32 i = 0; i != writeSize; i++) {
      triton::__uint byteId = this->getSymbolicMemoryId(memAddrDst + i);
      if (byteId == triton::engines::symbolic::UNSET)
        continue;
      triton::engines::symbolic::SymbolicExpression* byte = this->getSymbolicExpressionFromId(byteId);
      byte->isTainted = flag;
    }

    return flag;
  }


  bool API::taintAssignmentRegImm(arch::RegisterOperand& regDst) {
    this->checkTaint();
    return this->taint->assignmentRegImm(regDst);
  }


  bool API::taintAssignmentRegMem(arch::RegisterOperand& regDst, arch::MemoryOperand& memSrc) {
    this->checkTaint();
    return this->taint->assignmentRegMem(regDst, memSrc);
  }


  bool API::taintAssignmentRegReg(arch::RegisterOperand& regDst, arch::RegisterOperand& regSrc) {
    this->checkTaint();
    return this->taint->assignmentRegReg(regDst, regSrc);
  }

}; /* triton namespace */

