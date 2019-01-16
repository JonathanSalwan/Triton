//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/api.hpp>
#include <triton/exceptions.hpp>

#include <list>
#include <map>
#include <new>


/*!

\mainpage Triton: Dynamic Binary Analysis Framework

\tableofcontents

\section description_sec Description

<b>Triton</b> is a dynamic binary analysis (DBA) framework. It provides internal components
like a <b>Dynamic Symbolic Execution</b> (DSE) engine, a <b>Taint</b> engine, <b>AST representations</b>
of the <b>x86</b>, <b>x86-64</b> and <b>AArch64</b> instructions set architecture (ISA), <b>SMT simplification</b> passes,
an <b>SMT Solver</b> interface and, the last but not least, <b>Python bindings</b>.


<br>
<hr>
\section publications_sec Presentations and Publications

<ul>
  <li><b>Symbolic Deobfuscation: From Virtualized Code Back to the Original</b><br>
  Talk at DIMVA, Paris-Saclay, 2018.
  [<a href="https://triton.quarkslab.com/files/DIMVA2018-deobfuscation-salwan-bardin-potet.pdf">paper</a>]
  [<a href="https://triton.quarkslab.com/files/DIMVA2018-slide-deobfuscation-salwan-bardin-potet.pdf">slide</a>]
  [<a href="https://triton.quarkslab.com/files/DeobfuscationDIMVA2018.txt">bibtex</a>]<br>
  Abstract: <i>Software protection has taken an important place during the last decade in order to protect legit
  software against reverse engineering or tampering. Virtualization is considered as one of the very best defenses
  against such attacks. We present a generic approach based on symbolic path exploration, taint and recompilation
  allowing to recover, from a virtualized code, a devirtualized code semantically identical to the original one
  and close in size. We define criteria and metrics to evaluate the relevance of the deobfuscated results in terms
  of correctness and precision. Finally we propose an open-source setup allowing to evaluate the proposed approach
  against several forms of virtualization.
  </i></li>

  <li><b>Deobfuscation of VM based software protection </b><br>
  Talk at SSTIC, Rennes, 2017.
  [<a href="https://triton.quarkslab.com/files/sstic2017-salwan-bardin-potet-paper.pdf">french paper</a>]
  [<a href="https://triton.quarkslab.com/files/sstic2017-salwan-bardin-potet-slide.pdf">english slide</a>]
  [<a href="https://static.sstic.org/videos2017/SSTIC_2017-06-07_P08.mp4">french video</a>]
  [<a href="https://triton.quarkslab.com/files/DeobfuscationSSTIC2017.txt">bibtex</a>]<br>
  Abstract: <i>In this presentation we describe an approach which consists to automatically analyze virtual
  machine based software protections and which recompiles a new version of the binary without such protections. This
  automated approach relies on a symbolic execution guide by a taint analysis and some concretization policies, then
  on a binary rewriting using LLVM transition.
  </i></li>

  <li><b>How Triton can help to reverse virtual machine based software protections</b><br>
  Talk at CSAW SOS, NYC, 2016.
  [<a href="https://triton.quarkslab.com/files/csaw2016-sos-rthomas-jsalwan.pdf">slide</a>]<br>
  Abstract: <i>The first part of the talk is going to be an introduction to the Triton framework
  to expose its components and to explain how they work together. Then, the second part will
  include demonstrations on how it's possible to reverse virtual machine based protections using
  taint analysis, symbolic execution, SMT simplifications and LLVM-IR optimizations.
  </i></li>

  <li><b>Dynamic Binary Analysis and Obfuscated Codes</b><br>
  Talk at St'Hack, Bordeaux, 2016.
  [<a href="https://triton.quarkslab.com/files/sthack2016-rthomas-jsalwan.pdf">slide</a>]<br>
  Abstract: <i>At this presentation we will talk about how a DBA (Dynamic Binary Analysis) may
  help a reverse engineer to reverse obfuscated code. We will first introduce some basic obfuscation
  techniques and then expose how it's possible to break some stuffs (using our open-source DBA framework - Triton) like
  detect opaque predicates, reconstruct CFG, find the original algorithm, isolate sensible
  data and many more... Then, we will conclude with a demo and few words about our future work.
  </i></li>

  <li><b>How Triton may help to analyse obfuscated binaries</b><br>
  MISC magazine 82, 2015.
  [<a href="https://triton.quarkslab.com/files/misc82-triton.pdf">french article</a>]<br>
  Abstract: <i>Binary obfuscation is used to protect software's intellectual property.
  There exist different kinds of obfucation but roughly, it transforms a binary structure
  into another binary structure by preserving the same semantic. The aim of obfuscation is
  to ensure that the original information is "drown" in useless information that will make
  reverse engineering harder. In this article we will show how we can analyse an ofbuscated
  program and break some obfuscations using the Triton framework.</i></li>

  <li><b>Triton: A Concolic Execution Framework</b><br>
  Talk at SSTIC, Rennes, 2015.
  [<a href="https://triton.quarkslab.com/files/sstic2015_wp_fr_saudel_salwan.pdf">french paper</a>]
  [<a href="https://triton.quarkslab.com/files/sstic2015_slide_en_saudel_salwan.pdf">detailed english slide</a>]
  [<a href="https://triton.quarkslab.com/files/sstic2015_slide_fr_saudel_salwan.pdf">light french slide</a>]
  [<a href="https://triton.quarkslab.com/files/TritonSSTIC2015.txt">bibtex</a>]<br>
  Abstract: <i>This talk is about the release of Triton, a concolic execution framework based on Pin.
  It provides components like a taint engine, a dynamic symbolic execution engine, a snapshot engine,
  translation of x64 instruction to SMT2, a Z3 interface to solve constraints and Python bindings.
  Based on these components, Triton offers the possibility to build tools for vulnerabilities research or
  reverse-engineering assistance.</i></li>

  <li><b>Dynamic Behavior Analysis Using Binary Instrumentation</b><br>
  Talk at St'Hack, Bordeaux, 2015.
  [<a href="https://triton.quarkslab.com/files/sthack2015_salwan.pdf">slide</a>]<br>
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
  [<a href="https://triton.quarkslab.com/files/secday2015_salwan.pdf">slide</a>]<br>
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
 [libboost](http://www.boost.org/)                                             | >= 1.55
 [libpython](https://www.python.org/)                                          | == 2.7.x
 [libz3](https://github.com/Z3Prover/z3)                                       | >= 4.6.0
 [libcapstone](http://www.capstone-engine.org/)                                | == 3.0.5
 [Pin](https://software.intel.com/en-us/articles/pintool-downloads) (optional) | == 71313

<hr>
\subsection linux_install_sec Linux Installation

Once the libraries are installed, you can use `cmake` and `make` to build the `libTriton`.

~~~~~~~~~~~~~{.sh}
$ git clone https://github.com/JonathanSalwan/Triton.git
$ cd Triton
$ mkdir build
$ cd build
$ cmake ..
$ sudo make -j install
~~~~~~~~~~~~~

<hr>
\subsection osx_install_sec OSX Installation

On OSX cmake might have some difficulties finding the correct python include/library paths.
You can run the following to build indenpendent of your python version:

~~~~~~~~~~~~~{.sh}
$ brew install boost capstone z3
$ git clone https://github.com/JonathanSalwan/Triton.git
$ cd Triton
$ mkdir build
$ cd build
$ cmake $(echo 'from os.path import abspath, join; from distutils.sysconfig import get_python_inc, get_python_lib; print "-DPYTHON_INCLUDE_DIR=%s -DPYTHON_LIBRARY=%s" % (get_python_inc(), abspath(join(get_python_lib(), "../../libpython2.7.dylib")))' | python) ..
$ sudo make -j install
~~~~~~~~~~~~~

<hr>
\subsection windows_install_sec Windows Installation

Once libraries installed, you can use `cmake` to generate the `.sln` file of the `libTriton`.

~~~~~~~~~~~~~{.sh}
> git clone https://github.com/JonathanSalwan/Triton.git
> cd Triton
> mkdir build
> cd build
> cmake -G "Visual Studio 14 2015 Win64" \
  -DBOOST_ROOT="C:/Users/jonathan/Works/Tools/boost_1_61_0" \
  -DPYTHON_INCLUDE_DIRS="C:/Python27/include" \
  -DPYTHON_LIBRARIES="C:/Python27/libs/python27.lib" \
  -DZ3_INCLUDE_DIRS="C:/Users/jonathan/Works/Tools/z3-4.4.1-x64-win/include" \
  -DZ3_LIBRARIES="C:/Users/jonathan/Works/Tools/z3-4.4.1-x64-win/bin/libz3.lib" \
  -DCAPSTONE_INCLUDE_DIRS="C:/Users/jonathan/Works/Tools/capstone-3.0.5-win64/include" \
  -DCAPSTONE_LIBRARIES="C:/Users/jonathan/Works/Tools/capstone-3.0.5-win64/capstone.lib" ..
~~~~~~~~~~~~~

However, if you prefer to directly download precompiled libraries, check out our [AppVeyor's artefacts](https://ci.appveyor.com/project/JonathanSalwan/triton/history).
Note that if you use AppVeyor's artefacts, you probably have to install the [Visual C++ Redistributable](https://www.microsoft.com/en-US/download/details.aspx?id=30679)
packages for Visual Studio 2012.

<hr>
\subsection libpintool_install_sec Pintool for Linux users

This project is also shipped with a \ref Tracer_page and may be compiled with these following commands:

~~~~~~~~~~~~~{.sh}
$ cd pin-2.14-71313-gcc.4.4.7-linux/source/tools/
$ git clone https://github.com/JonathanSalwan/Triton.git
$ cd Triton
$ mkdir build
$ cd build
$ cmake -DPINTOOL=on ..
$ make
$ cd ..
$ ./build/triton ./src/examples/pin/ir.py /usr/bin/id
~~~~~~~~~~~~~

It's not recommended to use the pintool on a kernel `4.x`. The version `71313` of Pin doesn't support very well
this branch (`4.x`). Anyway, if you feel lucky, you can compile the Triton pintool with the `-DKERNEL4=on` flag.

~~~~~~~~~~~~~{.sh}
$ cmake -DPINTOOL=on -DKERNEL4=on ..
$ make
~~~~~~~~~~~~~

Note that only the version `71313` of Pin is supported.

*/



namespace triton {

  API::API() : callbacks(*this), arch(&this->callbacks), modes(), astCtxt(this->modes) {
  }


  API::~API() {
    this->removeEngines();
  }



  /* Architecture API ============================================================================== */

  bool API::isArchitectureValid(void) const {
    return this->arch.isValid();
  }


  void API::checkArchitecture(void) const {
    if (!this->isArchitectureValid())
      throw triton::exceptions::API("API::checkArchitecture(): You must define an architecture.");
  }


  triton::arch::architecture_e API::getArchitecture(void) const {
    return this->arch.getArchitecture();
  }


  triton::arch::endianness_e API::getEndianness(void) const {
    return this->arch.getEndianness();
  }


  triton::arch::CpuInterface* API::getCpuInstance(void) {
    if (!this->isArchitectureValid())
      throw triton::exceptions::API("API::checkArchitecture(): You must define an architecture.");
    return this->arch.getCpuInstance();
  }


  void API::setArchitecture(triton::arch::architecture_e arch) {
    /* Setup and init the targeted architecture */
    this->arch.setArchitecture(arch);

    /* remove and re-init previous engines (when setArchitecture() has been called twice) */
    this->removeEngines();
    this->initEngines();
  }


  void API::clearArchitecture(void) {
    this->checkArchitecture();
    this->arch.clearArchitecture();
  }


  bool API::isFlag(triton::arch::register_e regId) const {
    return this->arch.isFlag(regId);
  }


  bool API::isFlag(const triton::arch::Register& reg) const {
    return this->arch.isFlag(reg);
  }


  bool API::isRegister(triton::arch::register_e regId) const {
    return this->arch.isRegister(regId);
  }


  bool API::isRegister(const triton::arch::Register& reg) const {
    return this->arch.isRegister(reg);
  }


  const triton::arch::Register& API::getRegister(triton::arch::register_e id) const {
    return this->arch.getRegister(id);
  }


  const triton::arch::Register& API::getParentRegister(const triton::arch::Register& reg) const {
    return this->arch.getParentRegister(reg);
  }


  const triton::arch::Register& API::getParentRegister(triton::arch::register_e id) const {
    return this->arch.getParentRegister(id);
  }


  bool API::isRegisterValid(triton::arch::register_e regId) const {
    return this->arch.isRegisterValid(regId);
  }


  bool API::isRegisterValid(const triton::arch::Register& reg) const {
    return this->arch.isRegisterValid(reg);
  }


  triton::uint32 API::getGprBitSize(void) const {
    return this->arch.gprBitSize();
  }


  triton::uint32 API::getGprSize(void) const {
    return this->arch.gprSize();
  }


  triton::uint32 API::getNumberOfRegisters(void) const {
    return this->arch.numberOfRegisters();
  }


  const std::unordered_map<triton::arch::register_e, const triton::arch::Register>& API::getAllRegisters(void) const {
    this->checkArchitecture();
    return this->arch.getAllRegisters();
  }


  std::set<const triton::arch::Register*> API::getParentRegisters(void) const {
    this->checkArchitecture();
    return this->arch.getParentRegisters();
  }


  triton::uint8 API::getConcreteMemoryValue(triton::uint64 addr, bool execCallbacks) const {
    this->checkArchitecture();
    return this->arch.getConcreteMemoryValue(addr, execCallbacks);
  }


  triton::uint512 API::getConcreteMemoryValue(const triton::arch::MemoryAccess& mem, bool execCallbacks) const {
    this->checkArchitecture();
    return this->arch.getConcreteMemoryValue(mem, execCallbacks);
  }


  std::vector<triton::uint8> API::getConcreteMemoryAreaValue(triton::uint64 baseAddr, triton::usize size, bool execCallbacks) const {
    this->checkArchitecture();
    return this->arch.getConcreteMemoryAreaValue(baseAddr, size, execCallbacks);
  }


  triton::uint512 API::getConcreteRegisterValue(const triton::arch::Register& reg, bool execCallbacks) const {
    this->checkArchitecture();
    return this->arch.getConcreteRegisterValue(reg, execCallbacks);
  }


  void API::setConcreteMemoryValue(triton::uint64 addr, triton::uint8 value) {
    this->checkArchitecture();
    this->arch.setConcreteMemoryValue(addr, value);
  }


  void API::setConcreteMemoryValue(const triton::arch::MemoryAccess& mem, const triton::uint512& value) {
    this->checkArchitecture();
    this->arch.setConcreteMemoryValue(mem, value);
  }


  void API::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const std::vector<triton::uint8>& values) {
    this->checkArchitecture();
    this->arch.setConcreteMemoryAreaValue(baseAddr, values);
  }


  void API::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const triton::uint8* area, triton::usize size) {
    this->checkArchitecture();
    this->arch.setConcreteMemoryAreaValue(baseAddr, area, size);
  }


  void API::setConcreteRegisterValue(const triton::arch::Register& reg, const triton::uint512& value) {
    this->checkArchitecture();
    this->arch.setConcreteRegisterValue(reg, value);
  }


  bool API::isMemoryMapped(triton::uint64 baseAddr, triton::usize size) {
    this->checkArchitecture();
    return this->arch.isMemoryMapped(baseAddr, size);
  }


  void API::unmapMemory(triton::uint64 baseAddr, triton::usize size) {
    this->checkArchitecture();
    this->arch.unmapMemory(baseAddr, size);
  }


  void API::disassembly(triton::arch::Instruction& inst) const {
    this->checkArchitecture();
    this->arch.disassembly(inst);
  }



  /* Processing API ================================================================================ */

  void API::initEngines(void) {
    this->checkArchitecture();

    this->symbolic = new(std::nothrow) triton::engines::symbolic::SymbolicEngine(&this->arch, this->modes, this->astCtxt, &this->callbacks);
    if (this->symbolic == nullptr)
      throw triton::exceptions::API("API::initEngines(): No enough memory.");

    this->solver = new(std::nothrow) triton::engines::solver::SolverEngine();
    if (this->solver == nullptr)
      throw triton::exceptions::API("API::initEngines(): No enough memory.");

    this->taint = new(std::nothrow) triton::engines::taint::TaintEngine(this->modes, this->symbolic, *this->getCpuInstance());
    if (this->taint == nullptr)
      throw triton::exceptions::API("API::initEngines(): No enough memory.");

    this->irBuilder = new(std::nothrow) triton::arch::IrBuilder(&this->arch, this->modes, this->astCtxt, this->symbolic, this->taint);
    if (this->irBuilder == nullptr)
      throw triton::exceptions::API("API::initEngines(): No enough memory.");
  }


  void API::removeEngines(void) {
    if (this->isArchitectureValid()) {
      delete this->irBuilder;
      delete this->solver;
      delete this->symbolic;
      delete this->taint;

      this->irBuilder           = nullptr;
      this->solver              = nullptr;
      this->symbolic            = nullptr;
      this->taint               = nullptr;
    }

    // Use default modes.
    this->modes = triton::modes::Modes();

    // Clean up the ast context
    this->astCtxt = triton::ast::AstContext(this->modes);
  }


  void API::reset(void) {
    if (this->isArchitectureValid()) {
      this->removeEngines();
      this->initEngines();
      this->clearArchitecture();
      this->removeAllCallbacks();
    }
  }


  bool API::processing(triton::arch::Instruction& inst) {
    this->checkArchitecture();
    this->arch.disassembly(inst);
    return this->irBuilder->buildSemantics(inst);
  }



  /* IR builder API ================================================================================= */

  void API::checkIrBuilder(void) const {
    if (!this->irBuilder)
      throw triton::exceptions::API("API::checkIrBuilder(): IR builder is undefined, you should define an architecture first.");
  }


  bool API::buildSemantics(triton::arch::Instruction& inst) {
    this->checkIrBuilder();
    return this->irBuilder->buildSemantics(inst);
  }


  triton::ast::AstContext& API::getAstContext(void) {
    return this->astCtxt;
  }



  /* AST representation API ========================================================================= */

  triton::uint32 API::getAstRepresentationMode(void) const {
    return this->astCtxt.getRepresentationMode();
  }


  void API::setAstRepresentationMode(triton::uint32 mode) {
    this->astCtxt.setRepresentationMode(mode);
  }



  /* Callbacks API ================================================================================= */

  void API::addCallback(triton::callbacks::getConcreteMemoryValueCallback cb) {
    this->callbacks.addCallback(cb);
  }


  void API::addCallback(triton::callbacks::getConcreteRegisterValueCallback cb) {
    this->callbacks.addCallback(cb);
  }


  void API::addCallback(triton::callbacks::setConcreteMemoryValueCallback cb) {
    this->callbacks.addCallback(cb);
  }


  void API::addCallback(triton::callbacks::setConcreteRegisterValueCallback cb) {
    this->callbacks.addCallback(cb);
  }


  void API::addCallback(triton::callbacks::symbolicSimplificationCallback cb) {
    this->callbacks.addCallback(cb);
  }


  void API::removeAllCallbacks(void) {
    this->callbacks.removeAllCallbacks();
  }


  void API::removeCallback(triton::callbacks::getConcreteMemoryValueCallback cb) {
    this->callbacks.removeCallback(cb);
  }


  void API::removeCallback(triton::callbacks::getConcreteRegisterValueCallback cb) {
    this->callbacks.removeCallback(cb);
  }


  void API::removeCallback(triton::callbacks::setConcreteMemoryValueCallback cb) {
    this->callbacks.removeCallback(cb);
  }


  void API::removeCallback(triton::callbacks::setConcreteRegisterValueCallback cb) {
    this->callbacks.removeCallback(cb);
  }


  void API::removeCallback(triton::callbacks::symbolicSimplificationCallback cb) {
    this->callbacks.removeCallback(cb);
  }


  triton::ast::SharedAbstractNode API::processCallbacks(triton::callbacks::callback_e kind, triton::ast::SharedAbstractNode node) const {
    if (this->callbacks.isDefined)
      return this->callbacks.processCallbacks(kind, node);
    return node;
  }


  void API::processCallbacks(triton::callbacks::callback_e kind, const triton::arch::MemoryAccess& mem) const {
    if (this->callbacks.isDefined)
      this->callbacks.processCallbacks(kind, mem);
  }


  void API::processCallbacks(triton::callbacks::callback_e kind, const triton::arch::Register& reg) const {
    if (this->callbacks.isDefined)
      this->callbacks.processCallbacks(kind, reg);
  }



  /* Modes API======================================================================================= */

  void API::enableMode(triton::modes::mode_e mode, bool flag) {
    this->modes.enableMode(mode, flag);
  }


  bool API::isModeEnabled(triton::modes::mode_e mode) const {
    return this->modes.isModeEnabled(mode);
  }



  /* Symbolic engine API ============================================================================ */

  void API::checkSymbolic(void) const {
    if (!this->symbolic)
      throw triton::exceptions::API("API::checkSymbolic(): Symbolic engine is undefined, you should define an architecture first.");
  }


  triton::engines::symbolic::SymbolicEngine* API::getSymbolicEngine(void) {
    this->checkSymbolic();
    return this->symbolic;
  }


  const triton::engines::symbolic::SharedSymbolicVariable& API::convertExpressionToSymbolicVariable(triton::usize exprId, triton::uint32 symVarSize, const std::string& symVarComment) {
    this->checkSymbolic();
    return this->symbolic->convertExpressionToSymbolicVariable(exprId, symVarSize, symVarComment);
  }


  const triton::engines::symbolic::SharedSymbolicVariable& API::convertMemoryToSymbolicVariable(const triton::arch::MemoryAccess& mem, const std::string& symVarComment) {
    this->checkSymbolic();
    return this->symbolic->convertMemoryToSymbolicVariable(mem, symVarComment);
  }


  const triton::engines::symbolic::SharedSymbolicVariable& API::convertRegisterToSymbolicVariable(const triton::arch::Register& reg, const std::string& symVarComment) {
    this->checkSymbolic();
    return this->symbolic->convertRegisterToSymbolicVariable(reg, symVarComment);
  }


  triton::ast::SharedAbstractNode API::getOperandAst(const triton::arch::OperandWrapper& op) {
    this->checkSymbolic();
    return this->symbolic->getOperandAst(op);
  }


  triton::ast::SharedAbstractNode API::getOperandAst(triton::arch::Instruction& inst, const triton::arch::OperandWrapper& op) {
    this->checkSymbolic();
    return this->symbolic->getOperandAst(inst, op);
  }


  triton::ast::SharedAbstractNode API::getImmediateAst(const triton::arch::Immediate& imm) {
    this->checkSymbolic();
    return this->symbolic->getImmediateAst(imm);
  }


  triton::ast::SharedAbstractNode API::getImmediateAst(triton::arch::Instruction& inst, const triton::arch::Immediate& imm) {
    this->checkSymbolic();
    return this->symbolic->getImmediateAst(inst, imm);
  }


  triton::ast::SharedAbstractNode API::getMemoryAst(const triton::arch::MemoryAccess& mem) {
    this->checkSymbolic();
    return this->symbolic->getMemoryAst(mem);
  }


  triton::ast::SharedAbstractNode API::getMemoryAst(triton::arch::Instruction& inst, const triton::arch::MemoryAccess& mem) {
    this->checkSymbolic();
    return this->symbolic->getMemoryAst(inst, mem);
  }


  triton::ast::SharedAbstractNode API::getRegisterAst(const triton::arch::Register& reg) {
    this->checkSymbolic();
    return this->symbolic->getRegisterAst(reg);
  }


  triton::ast::SharedAbstractNode API::getRegisterAst(triton::arch::Instruction& inst, const triton::arch::Register& reg) {
    this->checkSymbolic();
    return this->symbolic->getRegisterAst(inst, reg);
  }


  triton::engines::symbolic::SharedSymbolicExpression API::newSymbolicExpression(const triton::ast::SharedAbstractNode& node, const std::string& comment) {
    this->checkSymbolic();
    return this->symbolic->newSymbolicExpression(node, triton::engines::symbolic::VOLATILE_EXPRESSION, comment);
  }


  const triton::engines::symbolic::SharedSymbolicVariable& API::newSymbolicVariable(triton::uint32 varSize, const std::string& comment) {
    this->checkSymbolic();
    return this->symbolic->newSymbolicVariable(triton::engines::symbolic::UNDEFINED_VARIABLE, 0, varSize, comment);
  }


  void API::removeSymbolicExpression(triton::usize symExprId) {
    this->checkSymbolic();
    return this->symbolic->removeSymbolicExpression(symExprId);
  }


  const triton::engines::symbolic::SharedSymbolicExpression& API::createSymbolicExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const triton::arch::OperandWrapper& dst, const std::string& comment) {
    this->checkSymbolic();
    return this->symbolic->createSymbolicExpression(inst, node, dst, comment);
  }


  const triton::engines::symbolic::SharedSymbolicExpression& API::createSymbolicMemoryExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const triton::arch::MemoryAccess& mem, const std::string& comment) {
    this->checkSymbolic();
    return this->symbolic->createSymbolicMemoryExpression(inst, node, mem, comment);
  }


  const triton::engines::symbolic::SharedSymbolicExpression& API::createSymbolicRegisterExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const triton::arch::Register& reg, const std::string& comment) {
    this->checkSymbolic();
    return this->symbolic->createSymbolicRegisterExpression(inst, node, reg, comment);
  }


  const triton::engines::symbolic::SharedSymbolicExpression& API::createSymbolicFlagExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const triton::arch::Register& flag, const std::string& comment) {
    this->checkSymbolic();
    return this->symbolic->createSymbolicFlagExpression(inst, node, flag, comment);
  }


  const triton::engines::symbolic::SharedSymbolicExpression& API::createSymbolicVolatileExpression(triton::arch::Instruction& inst, const triton::ast::SharedAbstractNode& node, const std::string& comment) {
    this->checkSymbolic();
    return this->symbolic->createSymbolicVolatileExpression(inst, node, comment);
  }


  void API::assignSymbolicExpressionToMemory(const triton::engines::symbolic::SharedSymbolicExpression& se, const triton::arch::MemoryAccess& mem) {
    this->checkSymbolic();
    this->symbolic->assignSymbolicExpressionToMemory(se, mem);
  }


  void API::assignSymbolicExpressionToRegister(const triton::engines::symbolic::SharedSymbolicExpression& se, const triton::arch::Register& reg) {
    this->checkSymbolic();
    this->symbolic->assignSymbolicExpressionToRegister(se, reg);
  }


  triton::engines::symbolic::SharedSymbolicExpression API::getSymbolicMemory(triton::uint64 addr) const {
    this->checkSymbolic();
    return this->symbolic->getSymbolicMemory(addr);
  }


  std::map<triton::arch::register_e, triton::engines::symbolic::SharedSymbolicExpression> API::getSymbolicRegisters(void) const {
    this->checkSymbolic();
    return this->symbolic->getSymbolicRegisters();
  }


  std::map<triton::uint64, triton::engines::symbolic::SharedSymbolicExpression> API::getSymbolicMemory(void) const {
    this->checkSymbolic();
    return this->symbolic->getSymbolicMemory();
  }


  const triton::engines::symbolic::SharedSymbolicExpression& API::getSymbolicRegister(const triton::arch::Register& reg) const {
    this->checkSymbolic();
    return this->symbolic->getSymbolicRegister(reg);
  }


  triton::uint8 API::getSymbolicMemoryValue(triton::uint64 address) {
    this->checkSymbolic();
    return this->symbolic->getSymbolicMemoryValue(address);
  }


  triton::uint512 API::getSymbolicMemoryValue(const triton::arch::MemoryAccess& mem) {
    this->checkSymbolic();
    return this->symbolic->getSymbolicMemoryValue(mem);
  }


  std::vector<triton::uint8> API::getSymbolicMemoryAreaValue(triton::uint64 baseAddr, triton::usize size) {
    this->checkSymbolic();
    return this->symbolic->getSymbolicMemoryAreaValue(baseAddr, size);
  }


  triton::uint512 API::getSymbolicRegisterValue(const triton::arch::Register& reg) {
    this->checkSymbolic();
    return this->symbolic->getSymbolicRegisterValue(reg);
  }


  triton::ast::SharedAbstractNode API::processSimplification(const triton::ast::SharedAbstractNode& node, bool z3) const {
    this->checkSymbolic();
    if (z3 == true) {
      auto snode = this->processZ3Simplification(node);
      return this->symbolic->processSimplification(snode);
    }
    return this->symbolic->processSimplification(node);
  }


  triton::engines::symbolic::SharedSymbolicExpression API::getSymbolicExpressionFromId(triton::usize symExprId) const {
    this->checkSymbolic();
    return this->symbolic->getSymbolicExpressionFromId(symExprId);
  }


  const triton::uint512& API::getConcreteVariableValue(const triton::engines::symbolic::SharedSymbolicVariable& symVar) const {
    this->checkSymbolic();
    return this->symbolic->getConcreteVariableValue(symVar);
  }


  void API::setConcreteVariableValue(const triton::engines::symbolic::SharedSymbolicVariable& symVar, const triton::uint512& value) {
    this->checkSymbolic();
    this->symbolic->setConcreteVariableValue(symVar, value);
  }


  const triton::engines::symbolic::SharedSymbolicVariable& API::getSymbolicVariableFromId(triton::usize symVarId) const {
    this->checkSymbolic();
    return this->symbolic->getSymbolicVariableFromId(symVarId);
  }


  const triton::engines::symbolic::SharedSymbolicVariable& API::getSymbolicVariableFromName(const std::string& symVarName) const {
    this->checkSymbolic();
    return this->symbolic->getSymbolicVariableFromName(symVarName);
  }


  const std::vector<triton::engines::symbolic::PathConstraint>& API::getPathConstraints(void) const {
    this->checkSymbolic();
    return this->symbolic->getPathConstraints();
  }


  triton::ast::SharedAbstractNode API::getPathConstraintsAst(void) {
    this->checkSymbolic();
    return this->symbolic->getPathConstraintsAst();
  }


  void API::addPathConstraint(const triton::arch::Instruction& inst, const triton::engines::symbolic::SharedSymbolicExpression& expr) {
    this->checkSymbolic();
    this->symbolic->addPathConstraint(inst, expr);
  }


  void API::clearPathConstraints(void) {
    this->checkSymbolic();
    this->symbolic->clearPathConstraints();
  }


  void API::enableSymbolicEngine(bool flag) {
    this->checkSymbolic();
    this->symbolic->enable(flag);
  }


  bool API::isSymbolicEngineEnabled(void) const {
    this->checkSymbolic();
    return this->symbolic->isEnabled();
  }


  bool API::isSymbolicExpressionIdExists(triton::usize symExprId) const {
    this->checkSymbolic();
    return this->symbolic->isSymbolicExpressionIdExists(symExprId);
  }


  bool API::isMemorySymbolized(const triton::arch::MemoryAccess& mem) const {
    this->checkSymbolic();
    return this->symbolic->isMemorySymbolized(mem);
  }


  bool API::isMemorySymbolized(triton::uint64 addr, triton::uint32 size) const {
    this->checkSymbolic();
    return this->symbolic->isMemorySymbolized(addr, size);
  }


  bool API::isRegisterSymbolized(const triton::arch::Register& reg) const {
    this->checkSymbolic();
    return this->symbolic->isRegisterSymbolized(reg);
  }


  void API::concretizeAllMemory(void) {
    this->checkSymbolic();
    this->symbolic->concretizeAllMemory();
  }


  void API::concretizeAllRegister(void) {
    this->checkSymbolic();
    this->symbolic->concretizeAllRegister();
  }


  void API::concretizeMemory(const triton::arch::MemoryAccess& mem) {
    this->checkSymbolic();
    this->symbolic->concretizeMemory(mem);
  }


  void API::concretizeMemory(triton::uint64 addr) {
    this->checkSymbolic();
    this->symbolic->concretizeMemory(addr);
  }


  void API::concretizeRegister(const triton::arch::Register& reg) {
    this->checkSymbolic();
    this->symbolic->concretizeRegister(reg);
  }


  triton::ast::SharedAbstractNode API::unrollAst(const triton::ast::SharedAbstractNode& node) {
    this->checkSymbolic();
    return this->symbolic->unrollAst(node);
  }


  std::map<triton::usize, triton::engines::symbolic::SharedSymbolicExpression> API::sliceExpressions(const triton::engines::symbolic::SharedSymbolicExpression& expr) {
    this->checkSymbolic();
    return this->symbolic->sliceExpressions(expr);
  }


  std::list<triton::engines::symbolic::SharedSymbolicExpression> API::getTaintedSymbolicExpressions(void) const {
    this->checkSymbolic();
    return this->symbolic->getTaintedSymbolicExpressions();
  }


  std::unordered_map<triton::usize, triton::engines::symbolic::SharedSymbolicExpression> API::getSymbolicExpressions(void) const {
    this->checkSymbolic();
    return this->symbolic->getSymbolicExpressions();
  }


  const std::unordered_map<triton::usize, triton::engines::symbolic::SharedSymbolicVariable>& API::getSymbolicVariables(void) const {
    this->checkSymbolic();
    return this->symbolic->getSymbolicVariables();
  }



  /* Solver engine API ============================================================================= */

  void API::checkSolver(void) const {
    if (!this->solver)
      throw triton::exceptions::API("API::checkSolver(): Solver engine is undefined, you should define an architecture first.");
  }


  triton::engines::solver::solver_e API::getSolver(void) const {
    this->checkSolver();
    return this->solver->getSolver();
  }


  const triton::engines::solver::SolverInterface* API::getSolverInstance(void) const {
    this->checkSolver();
    return this->solver->getSolverInstance();
  }


  void API::setSolver(triton::engines::solver::solver_e kind) {
    this->checkSolver();
    this->solver->setSolver(kind);
  }


  void API::setCustomSolver(triton::engines::solver::SolverInterface* customSolver) {
    this->checkSolver();
    this->solver->setCustomSolver(customSolver);
  }


  bool API::isSolverValid(void) const {
    this->checkSolver();
    return this->solver->isValid();
  }


  std::map<triton::uint32, triton::engines::solver::SolverModel> API::getModel(const triton::ast::SharedAbstractNode& node) const {
    this->checkSolver();
    return this->solver->getModel(node);
  }


  std::list<std::map<triton::uint32, triton::engines::solver::SolverModel>> API::getModels(const triton::ast::SharedAbstractNode& node, triton::uint32 limit) const {
    this->checkSolver();
    return this->solver->getModels(node, limit);
  }


  bool API::isSat(const triton::ast::SharedAbstractNode& node) const {
    this->checkSolver();
    return this->solver->isSat(node);
  }


  triton::uint512 API::evaluateAstViaZ3(const triton::ast::SharedAbstractNode& node) const {
    this->checkSolver();
    #ifdef Z3_INTERFACE
    if (this->getSolver() == triton::engines::solver::SOLVER_Z3) {
      return reinterpret_cast<const triton::engines::solver::Z3Solver*>(this->getSolverInstance())->evaluate(node);
    }
    #endif
    throw triton::exceptions::API("API::evaluateAstViaZ3(): Solver instance must be a SOLVER_Z3.");
  }


  triton::ast::SharedAbstractNode API::processZ3Simplification(const triton::ast::SharedAbstractNode& node) const {
    this->checkSolver();
    #ifdef Z3_INTERFACE
    if (this->getSolver() == triton::engines::solver::SOLVER_Z3) {
      return reinterpret_cast<const triton::engines::solver::Z3Solver*>(this->getSolverInstance())->simplify(node);
    }
    #endif
    throw triton::exceptions::API("API::processZ3Simplification(): Solver instance must be a SOLVER_Z3.");
  }



  /* Taint engine API ============================================================================== */

  void API::checkTaint(void) const {
    if (!this->taint)
      throw triton::exceptions::API("API::checkTaint(): Taint engine is undefined, you should define an architecture first.");
  }


  triton::engines::taint::TaintEngine* API::getTaintEngine(void) {
    this->checkTaint();
    return this->taint;
  }


  const std::set<triton::uint64>& API::getTaintedMemory(void) const {
    this->checkTaint();
    return this->taint->getTaintedMemory();
  }


  std::set<const triton::arch::Register*> API::getTaintedRegisters(void) const {
    this->checkTaint();
    return this->taint->getTaintedRegisters();
  }


  void API::enableTaintEngine(bool flag) {
    this->checkTaint();
    this->taint->enable(flag);
  }


  bool API::isTaintEngineEnabled(void) const {
    this->checkTaint();
    return this->taint->isEnabled();
  }


  bool API::isTainted(const triton::arch::OperandWrapper& op) const {
    this->checkTaint();
    return this->taint->isTainted(op);
  }


  bool API::isMemoryTainted(triton::uint64 addr, uint32 size) const {
    this->checkTaint();
    return this->taint->isMemoryTainted(addr, size);
  }


  bool API::isMemoryTainted(const triton::arch::MemoryAccess& mem) const {
    this->checkTaint();
    return this->taint->isMemoryTainted(mem);
  }


  bool API::isRegisterTainted(const triton::arch::Register& reg) const {
    this->checkTaint();
    return this->taint->isRegisterTainted(reg);
  }


  bool API::setTaint(const triton::arch::OperandWrapper& op, bool flag) {
    this->checkTaint();
    return this->taint->setTaint(op, flag);
  }


  bool API::setTaintMemory(const triton::arch::MemoryAccess& mem, bool flag) {
    this->checkTaint();
    this->taint->setTaintMemory(mem, flag);
    return flag;
  }


  bool API::setTaintRegister(const triton::arch::Register& reg, bool flag) {
    this->checkTaint();
    this->taint->setTaintRegister(reg, flag);
    return flag;
  }


  bool API::taintMemory(triton::uint64 addr) {
    this->checkTaint();
    return this->taint->taintMemory(addr);
  }


  bool API::taintMemory(const triton::arch::MemoryAccess& mem) {
    this->checkTaint();
    return this->taint->taintMemory(mem);
  }


  bool API::taintRegister(const triton::arch::Register& reg) {
    this->checkTaint();
    return this->taint->taintRegister(reg);
  }


  bool API::untaintMemory(triton::uint64 addr) {
    this->checkTaint();
    return this->taint->untaintMemory(addr);
  }


  bool API::untaintMemory(const triton::arch::MemoryAccess& mem) {
    this->checkTaint();
    return this->taint->untaintMemory(mem);
  }


  bool API::untaintRegister(const triton::arch::Register& reg) {
    this->checkTaint();
    return this->taint->untaintRegister(reg);
  }


  bool API::taintUnion(const triton::arch::OperandWrapper& op1, const triton::arch::OperandWrapper& op2) {
    this->checkTaint();
    return this->taint->taintUnion(op1, op2);
  }


  bool API::taintAssignment(const triton::arch::OperandWrapper& op1, const triton::arch::OperandWrapper& op2) {
    this->checkTaint();
    return this->taint->taintAssignment(op1, op2);
  }


  bool API::taintUnionMemoryImmediate(const triton::arch::MemoryAccess& memDst) {
    this->checkTaint();
    return this->taint->taintUnionMemoryImmediate(memDst);
  }


  bool API::taintUnionMemoryMemory(const triton::arch::MemoryAccess& memDst, const triton::arch::MemoryAccess& memSrc) {
    this->checkTaint();
    return this->taint->taintUnionMemoryMemory(memDst, memSrc);
  }


  bool API::taintUnionMemoryRegister(const triton::arch::MemoryAccess& memDst, const triton::arch::Register& regSrc) {
    this->checkTaint();
    return this->taint->taintUnionMemoryRegister(memDst, regSrc);
  }


  bool API::taintUnionRegisterImmediate(const triton::arch::Register& regDst) {
    this->checkTaint();
    return this->taint->taintUnionRegisterImmediate(regDst);
  }


  bool API::taintUnionRegisterMemory(const triton::arch::Register& regDst, const triton::arch::MemoryAccess& memSrc) {
    this->checkTaint();
    return this->taint->taintUnionRegisterMemory(regDst, memSrc);
  }


  bool API::taintUnionRegisterRegister(const triton::arch::Register& regDst, const triton::arch::Register& regSrc) {
    this->checkTaint();
    return this->taint->taintUnionRegisterRegister(regDst, regSrc);
  }


  bool API::taintAssignmentMemoryImmediate(const triton::arch::MemoryAccess& memDst) {
    this->checkTaint();
    return this->taint->taintAssignmentMemoryImmediate(memDst);
  }


  bool API::taintAssignmentMemoryMemory(const triton::arch::MemoryAccess& memDst, const triton::arch::MemoryAccess& memSrc) {
    this->checkTaint();
    return this->taint->taintAssignmentMemoryMemory(memDst, memSrc);
  }


  bool API::taintAssignmentMemoryRegister(const triton::arch::MemoryAccess& memDst, const triton::arch::Register& regSrc) {
    this->checkTaint();
    return this->taint->taintAssignmentMemoryRegister(memDst, regSrc);
  }


  bool API::taintAssignmentRegisterImmediate(const triton::arch::Register& regDst) {
    this->checkTaint();
    return this->taint->taintAssignmentRegisterImmediate(regDst);
  }


  bool API::taintAssignmentRegisterMemory(const triton::arch::Register& regDst, const triton::arch::MemoryAccess& memSrc) {
    this->checkTaint();
    return this->taint->taintAssignmentRegisterMemory(regDst, memSrc);
  }


  bool API::taintAssignmentRegisterRegister(const triton::arch::Register& regDst, const triton::arch::Register& regSrc) {
    this->checkTaint();
    return this->taint->taintAssignmentRegisterRegister(regDst, regSrc);
  }

}; /* triton namespace */
