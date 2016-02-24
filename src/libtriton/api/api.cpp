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
like a \ref engine_DSE_page (DSE) engine, a \ref engine_Taint_page, \ref py_ast_page of the x86 and the x86-64
instruction set semantics, \ref SMT_simplification_page, a \ref solver_interface_page and, the last but not least,
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
    this->arch              = arch::Architecture();
    this->astRepresentation = nullptr;
    this->solver            = nullptr;
    this->sym               = nullptr;
    this->symBackup         = nullptr;
    this->taint             = nullptr;
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


  triton::arch::cpuInterface* API::getCpu(void) {
    if (!this->isArchitectureValid())
      throw std::runtime_error("API::checkArchitecture(): You must define an architecture.");
    return this->arch.getCpu();
  }


  void API::setArchitecture(triton::uint32 arch) {
    /* Setup and init the targeted architecture */
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


  bool API::isCpuRegister(triton::uint32 regId) {
    return this->arch.isRegister(regId);
  }


  bool API::isCpuRegisterValid(triton::uint32 regId) {
    return this->arch.isRegisterValid(regId);
  }


  triton::uint32 API::cpuRegisterSize(void) {
    return this->arch.registerSize();
  }


  triton::uint32 API::cpuRegisterBitSize(void) {
    return this->arch.registerBitSize();
  }


  triton::uint32 API::cpuInvalidRegister(void) {
    return this->arch.invalidRegister();
  }


  triton::uint32 API::cpuNumberOfRegisters(void) {
    return this->arch.numberOfRegisters();
  }


  std::tuple<std::string, triton::uint32, triton::uint32, triton::uint32> API::getCpuRegInformation(triton::uint32 reg) {
    return this->arch.getRegisterInformation(reg);
  }


  std::set<triton::arch::RegisterOperand*> API::getAllRegisters(void) {
    this->checkArchitecture();
    return this->arch.getAllRegisters();
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

    this->astRepresentation = new triton::ast::representations::AstRepresentation();
    if (!this->astRepresentation)
      throw std::invalid_argument("API::initEngines(): No enough memory.");
  }


  void API::removeEngines(void) {
    if(this->isArchitectureValid()) {
      delete this->astRepresentation;
      delete this->solver;
      delete this->sym;
      delete this->symBackup;
      delete this->taint;
    }
  }


  void API::resetEngines(void) {
    if(this->isArchitectureValid()) {
      this->removeEngines();
      this->initEngines();
      this->clearArchitecture();
      triton::ast::freeAllAstNodes();
    }
  }


  void API::processing(triton::arch::Instruction& inst) {
    this->checkArchitecture();
    this->disassembly(inst);
    this->buildSemantics(inst);
  }



  /* AST representation interface API =============================================================== */

  void API::checkAstRepresentation(void) {
    if (!this->astRepresentation)
      throw std::runtime_error("API::checkAstRepresentation(): AST representation interface is undefined.");
  }


  std::ostream& API::printAstRepresentation(std::ostream& stream, triton::ast::AbstractNode* node) {
    this->checkAstRepresentation();
    return this->astRepresentation->print(stream, node);
  }


  triton::uint32 API::getAstRepresentationMode(void) {
    this->checkAstRepresentation();
    return this->astRepresentation->getMode();
  }


  void API::setAstRepresentationMode(triton::uint32 mode) {
    this->checkAstRepresentation();
    this->astRepresentation->setMode(mode);
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


  triton::engines::symbolic::SymbolicVariable* API::convertExpressionToSymbolicVariable(triton::__uint exprId, triton::uint32 symVarSize, std::string symVarComment) {
    this->checkSymbolic();
    return this->sym->convertExpressionToSymbolicVariable(exprId, symVarSize, symVarComment);
  }


  triton::engines::symbolic::SymbolicVariable* API::convertMemoryToSymbolicVariable(triton::arch::MemoryOperand mem, std::string symVarComment) {
    this->checkSymbolic();
    return this->sym->convertMemoryToSymbolicVariable(mem, symVarComment);
  }


  triton::engines::symbolic::SymbolicVariable* API::convertRegisterToSymbolicVariable(triton::arch::RegisterOperand reg, std::string symVarComment) {
    this->checkSymbolic();
    return this->sym->convertRegisterToSymbolicVariable(reg, symVarComment);
  }


  triton::ast::AbstractNode* API::buildSymbolicOperand(triton::arch::OperandWrapper& op) {
    this->checkSymbolic();
    switch (op.getType()) {
      case triton::arch::OP_IMM: return this->buildSymbolicImmediateOperand(op.getImmediate());
      case triton::arch::OP_MEM: return this->buildSymbolicMemoryOperand(op.getMemory());
      case triton::arch::OP_REG: return this->buildSymbolicRegisterOperand(op.getRegister());
      default:
        throw std::runtime_error("API::buildSymbolicOperand(): Invalid operand.");
    }
  }


  triton::ast::AbstractNode* API::buildSymbolicImmediateOperand(triton::arch::ImmediateOperand& imm) {
    this->checkSymbolic();
    return this->sym->buildSymbolicImmediateOperand(imm);
  }


  triton::ast::AbstractNode* API::buildSymbolicMemoryOperand(triton::arch::MemoryOperand& mem) {
    this->checkSymbolic();
    return this->sym->buildSymbolicMemoryOperand(mem);
  }


  triton::ast::AbstractNode* API::buildSymbolicRegisterOperand(triton::arch::RegisterOperand& reg) {
    this->checkSymbolic();
    return this->sym->buildSymbolicRegisterOperand(reg);
  }


  triton::engines::symbolic::SymbolicExpression* API::newSymbolicExpression(triton::ast::AbstractNode* node, std::string comment) {
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


  triton::engines::symbolic::SymbolicExpression* API::createSymbolicExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, triton::arch::OperandWrapper& dst, std::string comment) {
    this->checkSymbolic();
    switch (dst.getType()) {
      case triton::arch::OP_MEM: return this->createSymbolicMemoryExpression(inst, node, dst.getMemory(), comment);
      case triton::arch::OP_REG: return this->createSymbolicRegisterExpression(inst, node, dst.getRegister(), comment);
      default:
        throw std::runtime_error("API::buildSymbolicOperand(): Invalid operand.");
    }
    return nullptr;
  }


  triton::engines::symbolic::SymbolicExpression* API::createSymbolicMemoryExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, triton::arch::MemoryOperand& mem, std::string comment) {
    this->checkSymbolic();
    return this->sym->createSymbolicMemoryExpression(inst, node, mem, comment);
  }


  triton::engines::symbolic::SymbolicExpression* API::createSymbolicRegisterExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, triton::arch::RegisterOperand& reg, std::string comment) {
    this->checkSymbolic();
    return this->sym->createSymbolicRegisterExpression(inst, node, reg, comment);
  }


  triton::engines::symbolic::SymbolicExpression* API::createSymbolicFlagExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, triton::arch::RegisterOperand& flag, std::string comment) {
    this->checkSymbolic();
    return this->sym->createSymbolicFlagExpression(inst, node, flag, comment);
  }


  triton::engines::symbolic::SymbolicExpression* API::createSymbolicVolatileExpression(triton::arch::Instruction& inst, triton::ast::AbstractNode* node, std::string comment) {
    this->checkSymbolic();
    return this->sym->createSymbolicVolatileExpression(inst, node, comment);
  }


  void API::assignSymbolicExpressionToMemory(triton::engines::symbolic::SymbolicExpression* se, triton::arch::MemoryOperand& mem) {
    this->checkSymbolic();
    this->sym->assignSymbolicExpressionToMemory(se, mem);
  }


  void API::assignSymbolicExpressionToRegister(triton::engines::symbolic::SymbolicExpression* se, triton::arch::RegisterOperand& reg) {
    this->checkSymbolic();
    this->sym->assignSymbolicExpressionToRegister(se, reg);
  }


  triton::__uint API::getSymbolicMemoryId(triton::__uint addr) {
    this->checkSymbolic();
    return this->sym->getSymbolicMemoryId(addr);
  }


  std::map<triton::arch::RegisterOperand, triton::engines::symbolic::SymbolicExpression*> API::getSymbolicRegisters(void) {
    this->checkSymbolic();
    return this->sym->getSymbolicRegisters();
  }


  std::map<triton::__uint, triton::engines::symbolic::SymbolicExpression*> API::getSymbolicMemory(void) {
    this->checkSymbolic();
    return this->sym->getSymbolicMemory();
  }


  triton::__uint API::getSymbolicRegisterId(triton::arch::RegisterOperand& reg) {
    this->checkSymbolic();
    return this->sym->getSymbolicRegisterId(reg);
  }


  triton::uint8 API::getSymbolicMemoryValue(triton::__uint address) {
    this->checkSymbolic();
    return this->sym->getSymbolicMemoryValue(address);
  }


  triton::uint128 API::getSymbolicMemoryValue(triton::arch::MemoryOperand& mem) {
    this->checkSymbolic();
    return this->sym->getSymbolicMemoryValue(mem);
  }


  triton::uint8 API::getMemoryValue(triton::__uint addr) {
    this->checkSymbolic();
    if (this->isSymbolicEmulationEnabled())
      return this->getSymbolicMemoryValue(addr);
    return this->getLastMemoryValue(addr);
  }


  triton::uint128 API::getMemoryValue(triton::arch::MemoryOperand& mem) {
    this->checkSymbolic();
    if (this->isSymbolicEmulationEnabled())
      return this->getSymbolicMemoryValue(mem);
    return this->getLastMemoryValue(mem);
  }


  triton::uint128 API::getRegisterValue(triton::arch::RegisterOperand& reg) {
    this->checkSymbolic();
    if (this->isSymbolicEmulationEnabled())
      return this->getSymbolicRegisterValue(reg);
    return this->getLastRegisterValue(reg);
  }


  triton::uint128 API::getSymbolicRegisterValue(triton::arch::RegisterOperand& reg) {
    this->checkSymbolic();
    return this->sym->getSymbolicRegisterValue(reg);
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


  triton::ast::AbstractNode* API::browseAstDictionaries(triton::ast::AbstractNode* node) {
    this->checkSymbolic();
    return this->sym->browseAstDictionaries(node);
  }


  std::map<std::string, triton::uint32> API::getAstDictionariesStats(void) {
    this->checkSymbolic();
    return this->sym->getAstDictionariesStats();
  }


  triton::ast::AbstractNode* API::processSimplification(triton::ast::AbstractNode* node, bool z3) {
    this->checkSymbolic();
    return this->sym->processSimplification(node, z3);
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


  std::vector<triton::ast::AbstractNode*>& API::getPathConstraint(void) {
    this->checkSymbolic();
    return this->sym->getPathConstraint();
  }


  triton::ast::AbstractNode* API::getPathConstraintAst(void) {
    this->checkSymbolic();
    return this->sym->getPathConstraintAst();
  }


  void API::addPathConstraint(triton::ast::AbstractNode* pc) {
    this->checkSymbolic();
    this->sym->addPathConstraint(pc);
  }


  void API::enableSymbolicEngine(bool flag) {
    this->checkSymbolic();
    this->sym->enable(flag);
  }


  void API::enableSymbolicEmulation(bool flag) {
    this->checkSymbolic();
    this->sym->emulation(flag);
  }


  void API::enableSymbolicZ3Simplification(bool flag) {
    this->checkSymbolic();
    this->sym->enableZ3Simplification(flag);
  }


  void API::enableSymbolicOptimization(enum triton::engines::symbolic::optimization_e opti, bool flag) {
    this->checkSymbolic();
    this->sym->enableOptimization(opti, flag);
  }


  bool API::isSymbolicEmulationEnabled(void) {
    this->checkSymbolic();
    return this->sym->isEmulationEnabled();
  }


  bool API::isSymbolicEngineEnabled(void) {
    this->checkSymbolic();
    return this->sym->isEnabled();
  }


  bool API::isSymbolicZ3SimplificationEnabled(void) {
    this->checkSymbolic();
    return this->sym->isZ3SimplificationEnabled();
  }


  bool API::isSymbolicExpressionIdExists(triton::__uint symExprId) {
    this->checkSymbolic();
    return this->sym->isSymbolicExpressionIdExists(symExprId);
  }


  bool API::isSymbolicOptimizationEnabled(enum triton::engines::symbolic::optimization_e opti) {
    this->checkSymbolic();
    return this->sym->isOptimizationEnabled(opti);
  }


  void API::concretizeAllMemory(void) {
    this->checkSymbolic();
    this->sym->concretizeAllMemory();
  }


  void API::concretizeAllRegister(void) {
    this->checkSymbolic();
    this->sym->concretizeAllRegister();
  }


  void API::concretizeMemory(triton::arch::MemoryOperand& mem) {
    this->checkSymbolic();
    this->sym->concretizeMemory(mem);
  }


  void API::concretizeMemory(triton::__uint addr) {
    this->checkSymbolic();
    this->sym->concretizeMemory(addr);
  }


  void API::concretizeRegister(triton::arch::RegisterOperand& reg) {
    this->checkSymbolic();
    this->sym->concretizeRegister(reg);
  }


  triton::ast::AbstractNode* API::getFullAst(triton::ast::AbstractNode* node) {
    this->checkSymbolic();
    return this->sym->getFullAst(node);
  }


  triton::ast::AbstractNode* API::getAstFromId(triton::__uint symExprId) {
    this->checkSymbolic();
    triton::engines::symbolic::SymbolicExpression* symExpr = this->getSymbolicExpressionFromId(symExprId);
    return symExpr->getAst();
  }


  triton::ast::AbstractNode* API::getFullAstFromId(triton::__uint symExprId) {
    this->checkSymbolic();
    triton::ast::AbstractNode* partialAst = this->getAstFromId(symExprId);
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


  std::map<triton::uint32, triton::engines::solver::SolverModel> API::getModel(triton::ast::AbstractNode *node) {
    this->checkSolver();
    return this->solver->getModel(node);
  }


  std::list<std::map<triton::uint32, triton::engines::solver::SolverModel>> API::getModels(triton::ast::AbstractNode *node, triton::uint32 limit) {
    this->checkSolver();
    return this->solver->getModels(node, limit);
  }


  triton::uint512 API::evaluateAstViaZ3(triton::ast::AbstractNode *node) {
    this->checkSolver();
    return this->solver->evaluateAstViaZ3(node);
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


  bool API::isTainted(arch::OperandWrapper& op) {
    this->checkTaint();
    switch (op.getType()) {
      case triton::arch::OP_IMM: return triton::engines::taint::UNTAINTED;
      case triton::arch::OP_MEM: return this->isMemoryTainted(op.getMemory());
      case triton::arch::OP_REG: return this->isRegisterTainted(op.getRegister());
      default:
        throw std::runtime_error("API::isTainted(): Invalid operand.");
    }
  }


  bool API::isMemoryTainted(__uint addr, uint32 size) {
    this->checkTaint();
    return this->taint->isMemoryTainted(addr, size);
  }


  bool API::isMemoryTainted(arch::MemoryOperand& mem) {
    this->checkTaint();
    return this->taint->isMemoryTainted(mem);
  }


  bool API::isRegisterTainted(arch::RegisterOperand& reg) {
    this->checkTaint();
    return this->taint->isRegisterTainted(reg);
  }


  bool API::setTaint(arch::OperandWrapper& op, bool flag) {
    this->checkTaint();
    switch (op.getType()) {
      case triton::arch::OP_IMM: return triton::engines::taint::UNTAINTED;
      case triton::arch::OP_MEM: return this->setTaintMemory(op.getMemory(), flag);
      case triton::arch::OP_REG: return this->setTaintRegister(op.getRegister(), flag);
      default:
        throw std::runtime_error("API::setTaint(): Invalid operand.");
    }
  }


  bool API::setTaintMemory(arch::MemoryOperand& mem, bool flag) {
    this->checkTaint();
    this->taint->setTaintMemory(mem, flag);
    return flag;
  }


  bool API::setTaintRegister(arch::RegisterOperand& reg, bool flag) {
    this->checkTaint();
    this->taint->setTaintRegister(reg, flag);
    return flag;
  }


  bool API::taintMemory(__uint addr) {
    this->checkTaint();
    return this->taint->taintMemory(addr);
  }


  bool API::taintMemory(arch::MemoryOperand& mem) {
    this->checkTaint();
    return this->taint->taintMemory(mem);
  }


  bool API::taintRegister(arch::RegisterOperand& reg) {
    this->checkTaint();
    return this->taint->taintRegister(reg);
  }


  bool API::untaintMemory(__uint addr) {
    this->checkTaint();
    return this->taint->untaintMemory(addr);
  }


  bool API::untaintMemory(arch::MemoryOperand& mem) {
    this->checkTaint();
    return this->taint->untaintMemory(mem);
  }


  bool API::untaintRegister(arch::RegisterOperand& reg) {
    this->checkTaint();
    return this->taint->untaintRegister(reg);
  }


  bool API::taintUnion(triton::arch::OperandWrapper& op1, triton::arch::OperandWrapper& op2) {
    triton::uint32 t1 = op1.getType();
    triton::uint32 t2 = op2.getType();

    if (t1 == triton::arch::OP_MEM && t2 == triton::arch::OP_IMM)
      return this->taintUnionMemoryImmediate(op1.getMemory());

    if (t1 == triton::arch::OP_MEM && t2 == triton::arch::OP_MEM)
      return this->taintUnionMemoryMemory(op1.getMemory(), op2.getMemory());

    if (t1 == triton::arch::OP_MEM && t2 == triton::arch::OP_REG)
      return this->taintUnionMemoryRegister(op1.getMemory(), op2.getRegister());

    if (t1 == triton::arch::OP_REG && t2 == triton::arch::OP_IMM)
      return this->taintUnionRegisterImmediate(op1.getRegister());

    if (t1 == triton::arch::OP_REG && t2 == triton::arch::OP_MEM)
      return this->taintUnionRegisterMemory(op1.getRegister(), op2.getMemory());

    if (t1 == triton::arch::OP_REG && t2 == triton::arch::OP_REG)
      return this->taintUnionRegisterRegister(op1.getRegister(), op2.getRegister());

    throw std::runtime_error("API::taintUnion(): Invalid operands.");
  }


  bool API::taintAssignment(triton::arch::OperandWrapper& op1, triton::arch::OperandWrapper& op2) {
    triton::uint32 t1 = op1.getType();
    triton::uint32 t2 = op2.getType();

    if (t1 == triton::arch::OP_MEM && t2 == triton::arch::OP_IMM)
      return this->taintAssignmentMemoryImmediate(op1.getMemory());

    if (t1 == triton::arch::OP_MEM && t2 == triton::arch::OP_MEM)
      return this->taintAssignmentMemoryMemory(op1.getMemory(), op2.getMemory());

    if (t1 == triton::arch::OP_MEM && t2 == triton::arch::OP_REG)
      return this->taintAssignmentMemoryRegister(op1.getMemory(), op2.getRegister());

    if (t1 == triton::arch::OP_REG && t2 == triton::arch::OP_IMM)
      return this->taintAssignmentRegisterImmediate(op1.getRegister());

    if (t1 == triton::arch::OP_REG && t2 == triton::arch::OP_MEM)
      return this->taintAssignmentRegisterMemory(op1.getRegister(), op2.getMemory());

    if (t1 == triton::arch::OP_REG && t2 == triton::arch::OP_REG)
      return this->taintAssignmentRegisterRegister(op1.getRegister(), op2.getRegister());

    throw std::runtime_error("API::taintAssignment(): Invalid operands.");
  }


  bool API::taintUnionMemoryImmediate(arch::MemoryOperand& memDst) {
    this->checkTaint();

    bool flag = triton::engines::taint::UNTAINTED;
    triton::__uint memAddrDst = memDst.getAddress();
    triton::uint32 writeSize  = memDst.getSize();

    flag = this->taint->unionMemoryImmediate(memDst);

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


  bool API::taintUnionMemoryMemory(arch::MemoryOperand& memDst, arch::MemoryOperand& memSrc) {
    this->checkTaint();

    bool flag = triton::engines::taint::UNTAINTED;
    triton::__uint memAddrDst = memDst.getAddress();
    triton::__uint memAddrSrc = memSrc.getAddress();
    triton::uint32 writeSize  = memDst.getSize();

    flag = this->taint->unionMemoryMemory(memDst, memSrc);

    /* Taint each byte of reference expression */
    for (triton::uint32 i = 0; i != writeSize; i++) {
      triton::__uint byteId = this->getSymbolicMemoryId(memAddrDst + i);
      if (byteId == triton::engines::symbolic::UNSET)
        continue;
      triton::engines::symbolic::SymbolicExpression* byte = this->getSymbolicExpressionFromId(byteId);
      byte->isTainted = this->isMemoryTainted(memAddrDst + i) | this->isMemoryTainted(memAddrSrc + i);
    }

    return flag;
  }


  bool API::taintUnionMemoryRegister(arch::MemoryOperand& memDst, arch::RegisterOperand& regSrc) {
    this->checkTaint();

    bool flag = triton::engines::taint::UNTAINTED;
    triton::__uint memAddrDst = memDst.getAddress();
    triton::uint32 writeSize  = memDst.getSize();

    flag = this->taint->unionMemoryRegister(memDst, regSrc);

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


  bool API::taintUnionRegisterImmediate(arch::RegisterOperand& regDst) {
    this->checkTaint();
    return this->taint->unionRegisterImmediate(regDst);
  }


  bool API::taintUnionRegisterMemory(arch::RegisterOperand& regDst, arch::MemoryOperand& memSrc) {
    this->checkTaint();
    return this->taint->unionRegisterMemory(regDst, memSrc);
  }


  bool API::taintUnionRegisterRegister(arch::RegisterOperand& regDst, arch::RegisterOperand& regSrc) {
    this->checkTaint();
    return this->taint->unionRegisterRegister(regDst, regSrc);
  }


  bool API::taintAssignmentMemoryImmediate(arch::MemoryOperand& memDst) {
    this->checkTaint();

    bool flag = triton::engines::taint::UNTAINTED;
    triton::__uint memAddrDst = memDst.getAddress();
    triton::uint32 writeSize  = memDst.getSize();

    flag = this->taint->assignmentMemoryImmediate(memDst);

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


  bool API::taintAssignmentMemoryMemory(arch::MemoryOperand& memDst, arch::MemoryOperand& memSrc) {
    this->checkTaint();

    bool flag = triton::engines::taint::UNTAINTED;
    triton::__uint memAddrDst = memDst.getAddress();
    triton::__uint memAddrSrc = memSrc.getAddress();
    triton::uint32 writeSize  = memDst.getSize();

    flag = this->taint->assignmentMemoryMemory(memDst, memSrc);

    /* Taint each byte of reference expression */
    for (triton::uint32 i = 0; i != writeSize; i++) {
      triton::__uint byteId = this->getSymbolicMemoryId(memAddrDst + i);
      if (byteId == triton::engines::symbolic::UNSET)
        continue;
      triton::engines::symbolic::SymbolicExpression* byte = this->getSymbolicExpressionFromId(byteId);
      byte->isTainted = this->isMemoryTainted(memAddrSrc + i);
    }

    return flag;
  }


  bool API::taintAssignmentMemoryRegister(arch::MemoryOperand& memDst, arch::RegisterOperand& regSrc) {
    this->checkTaint();

    bool flag = triton::engines::taint::UNTAINTED;
    triton::__uint memAddrDst = memDst.getAddress();
    triton::uint32 writeSize  = memDst.getSize();

    flag = this->taint->assignmentMemoryRegister(memDst, regSrc);

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


  bool API::taintAssignmentRegisterImmediate(arch::RegisterOperand& regDst) {
    this->checkTaint();
    return this->taint->assignmentRegisterImmediate(regDst);
  }


  bool API::taintAssignmentRegisterMemory(arch::RegisterOperand& regDst, arch::MemoryOperand& memSrc) {
    this->checkTaint();
    return this->taint->assignmentRegisterMemory(regDst, memSrc);
  }


  bool API::taintAssignmentRegisterRegister(arch::RegisterOperand& regDst, arch::RegisterOperand& regSrc) {
    this->checkTaint();
    return this->taint->assignmentRegisterRegister(regDst, regSrc);
  }

}; /* triton namespace */

