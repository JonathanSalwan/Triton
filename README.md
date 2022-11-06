<p align="center"><img width="50%" src="https://triton-library.github.io/files/triton2.png"/></p>

**Triton** is a dynamic binary analysis library. It provides internal components that allow you to build your program analysis tools,
automate reverse engineering, perform software verification or just emulate code.

* Dynamic **symbolic** execution
* Dynamic **taint** analysis
* AST representation of the **x86**, **x86-64**, **ARM32** and **AArch64** ISA semantic
* Expressions **synthesis**
* SMT **simplification** passes
* **Lifting** to **LLVM** as well as **Z3** and back
* **SMT solver** interface to **Z3** and **Bitwuzla**
* **C++** and **Python** API

<p align="center">
    <img src="https://triton-library.github.io/files/triton_v09_architecture.svg" width="80%"/></br>
    <img src="https://triton-library.github.io/files/triton_multi_os.png"/>
</p>

As **Triton** is a kind of a part-time project, please, **don't blame us** if it is not fully reliable. [Open issues](https://github.com/JonathanSalwan/Triton/issues) or
[pull requests](https://github.com/JonathanSalwan/Triton/pulls) are always better than trolling =). However, you can follow the development on twitter
[@qb_triton](https://twitter.com/qb_triton).

<p align="center">
  <a href="https://github.com/JonathanSalwan/Triton/actions/workflows/linux.yml/">
    <img src="https://img.shields.io/github/workflow/status/JonathanSalwan/Triton/Tests%20on%20Linux/master?label=Linux&logo=linux&logoColor=white">
  </a>
  &nbsp;
  <a href="https://github.com/JonathanSalwan/Triton/actions/workflows/osx.yml/">
    <img src="https://img.shields.io/github/workflow/status/JonathanSalwan/Triton/Tests%20on%20OSX/master?label=OSX&logo=apple">
  </a>
  &nbsp;
  <a href="https://ci.appveyor.com/project/JonathanSalwan/triton">
    <img src="https://img.shields.io/appveyor/ci/JonathanSalwan/triton/master.svg?label=Windows&logo=windows">
  </a>
  &nbsp;
  <a href="https://codecov.io/gh/JonathanSalwan/Triton">
    <img src="https://codecov.io/gh/JonathanSalwan/Triton/branch/master/graph/badge.svg" alt="Codecov" />
  </a>
  &nbsp;
  <a href="https://github.com/JonathanSalwan/Triton/releases">
    <img src="https://img.shields.io/github/v/release/JonathanSalwan/Triton?logo=github">
  </a>
  &nbsp;
  <a href="https://github.com/jonathansalwan/Triton/tree/dev-v1.0">
    <img src="https://img.shields.io/static/v1?label=dev&message=v1.0&logo=github&color=blue">
  </a>
  &nbsp;
  <a href="https://twitter.com/qb_triton">
   <img src="https://img.shields.io/twitter/follow/qb_triton?color=1da1f2&label=Follow&logo=twitter&logoColor=white&style=square">
  </a>
</p>

# Quick start

* [Installation](#install)
* [Python API](https://triton-library.github.io/documentation/doxygen/py_triton_page.html)
* [C++ API](https://triton-library.github.io/documentation/doxygen/annotated.html)
* [Python Examples](https://github.com/JonathanSalwan/Triton/tree/master/src/examples/python)
* [They already used Triton](#they-already-used-triton)

## Getting started

```python
from triton import *

>>> # Create the Triton context with a defined architecture
>>> ctx = TritonContext(ARCH.X86_64)

>>> # Define concrete values (optional)
>>> ctx.setConcreteRegisterValue(ctx.registers.rip, 0x40000)

>>> # Symbolize data (optional)
>>> ctx.symbolizeRegister(ctx.registers.rax, 'my_rax')

>>> # Execute instructions
>>> ctx.processing(Instruction(b"\x48\x35\x34\x12\x00\x00")) # xor rax, 0x1234
>>> ctx.processing(Instruction(b"\x48\x89\xc1")) # mov rcx, rax

>>> # Get the symbolic expression
>>> rcx_expr = ctx.getSymbolicRegister(ctx.registers.rcx)
>>> print(rcx_expr)
(define-fun ref!8 () (_ BitVec 64) ref!1) ; MOV operation - 0x40006: mov rcx, rax

>>> # Solve constraint
>>> ctx.getModel(rcx_expr.getAst() == 0xdead)
{0: my_rax:64 = 0xcc99}

>>> # 0xcc99 XOR 0x1234 is indeed equal to 0xdead
>>> hex(0xcc99 ^ 0x1234)
'0xdead'
```


## Install

Triton relies on the following dependencies:

```
* libcapstone                >= 4.0.x   https://github.com/capstone-engine/capstone
* libboost      (optional)   >= 1.68
* libpython     (optional)   >= 3.6
* libz3         (optional)   >= 4.6.0   https://github.com/Z3Prover/z3
* libbitwuzla   (optional)   n/a        https://github.com/bitwuzla/bitwuzla
* llvm          (optional)   >= 12
```


### Linux and MacOS

```console
$ git clone https://github.com/JonathanSalwan/Triton
$ cd Triton
$ mkdir build ; cd build
$ cmake ..
$ make -j3
$ sudo make install
```

By default, LLVM and Bitwuzla are not compiled. If you want to enjoy the full power of Triton, the cmake compile is:

```console
$ cmake -DLLVM_INTERFACE=ON -DCMAKE_PREFIX_PATH=$(llvm-config --prefix) -DBITWUZLA_INTERFACE=ON ..
```

#### MacOS M1 Note:

In case if you get compilation errors like:

```
Could NOT find PythonLibs (missing: PYTHON_LIBRARIES PYTHON_INCLUDE_DIRS)
```

Try to specify `PYTHON_EXECUTABLE`, `PYTHON_LIBRARIES` and `PYTHON_INCLUDE_DIRS` for your specific Python version:

```console
cmake -DCMAKE_INSTALL_PREFIX=/opt/homebrew/ \
      -DPYTHON_EXECUTABLE=/opt/homebrew/bin/python3 \
      -DPYTHON_LIBRARIES=/opt/homebrew/Cellar/python@3.10/3.10.8/Frameworks/Python.framework/Versions/3.10/lib/libpython3.10.dylib \
      -DPYTHON_INCLUDE_DIRS=/opt/homebrew/opt/python@3.10/Frameworks/Python.framework/Versions/3.10/include/python3.10/ \
      ..
```

This information you can get out from this snippet:

```python
from sysconfig import get_paths
info = get_paths()
print(info)
```

### Windows

You can use cmake to generate the .sln file of libTriton.

```console
> git clone https://github.com/JonathanSalwan/Triton.git
> cd Triton
> mkdir build
> cd build
> cmake -G "Visual Studio 14 2015 Win64" \
  -DBOOST_ROOT="C:/Users/jonathan/Works/Tools/boost_1_61_0" \
  -DPYTHON_INCLUDE_DIRS="C:/Python36/include" \
  -DPYTHON_LIBRARIES="C:/Python36/libs/python36.lib" \
  -DZ3_INCLUDE_DIRS="C:/Users/jonathan/Works/Tools/z3-4.6.0-x64-win/include" \
  -DZ3_LIBRARIES="C:/Users/jonathan/Works/Tools/z3-4.6.0-x64-win/bin/libz3.lib" \
  -DCAPSTONE_INCLUDE_DIRS="C:/Users/jonathan/Works/Tools/capstone-4.0.2-win64/include" \
  -DCAPSTONE_LIBRARIES="C:/Users/jonathan/Works/Tools/capstone-4.0.2-win64/capstone.lib" ..
```

However, if you prefer to directly download the precompiled library, check out our AppVeyor's [artefacts](https://ci.appveyor.com/project/JonathanSalwan/triton/history).
Note that if you use AppVeyor's artefacts, you probably have to install the [Visual C++ Redistributable](https://www.microsoft.com/en-US/download/details.aspx?id=30679)
packages for Visual Studio 2012.


### Installing from vcpkg

The Triton port in vcpkg is kept up to date by Microsoft team members and community contributors.
The url of vcpkg is: https://github.com/Microsoft/vcpkg. You can download and install Triton using
the vcpkg dependency manager:

```console
$ git clone https://github.com/Microsoft/vcpkg.git
$ cd vcpkg
$ ./bootstrap-vcpkg.sh  # ./bootstrap-vcpkg.bat for Windows
$ ./vcpkg integrate install
$ ./vcpkg install triton
```

If the version is out of date, please [create an issue or pull request](https://github.com/Microsoft/vcpkg) on the vcpkg repository.


# Contributors

Triton is strongly powered by [Quarkslab](https://quarkslab.com) for years but also by several contributors:

* [**Alberto Garcia Illera**](https://twitter.com/algillera) - Cruise Automation
* [**Alexey Vishnyakov**](https://vishnya.xyz/) - ISP RAS
* [**Black Binary**](https://github.com/black-binary) - n/a
* [**Christian Heitman**](https://github.com/cnheitman) - Quarkslab
* [**Daniil Kuts**](https://github.com/apach301) - ISP RAS
* [**Jessy Campos**](https://github.com/ek0) - n/a
* [**Matteo F.**](https://twitter.com/fvrmatteo) - n/a
* [**Pierrick Brunet**](https://github.com/pbrunet) - Quarkslab
* [**PixelRick**](https://github.com/PixelRick) - n/a
* [**Romain Thomas**](https://twitter.com/rh0main) - Quarkslab
* [**And many more**](https://github.com/JonathanSalwan/Triton/graphs/contributors)


## They already used Triton

### Tools

* [Ponce](https://github.com/illera88/Ponce): IDA 2016 plugin contest winner! Symbolic Execution just one-click away!
* [QSynthesis](https://github.com/quarkslab/qsynthesis): Greybox Synthesizer geared for deobfuscation of assembly instructions.
* [Pimp](https://github.com/kamou/pimp): Triton based R2 plugin for concolic execution and total control.
* [Exrop](https://github.com/d4em0n/exrop): Automatic ROPChain Generation.

### Papers and conference

<ul dir="auto">
<li>
<b>Strong Optimistic Solving for Dynamic Symbolic Execution</b><br />
 <b>Talk at</b>: Ivannikov Memorial Workshop, Kazan, Russia, 2022. [<a href="publications/IVMEM2022-strong-optimistic-parygina.pdf">paper</a>] [<a href="publications/IVMEM2022-slide-strong-optimistic-parygina.pdf">slide</a>]<br />
 <b>Authors</b>: Parygina D., Vishnyakov A., Fedotov A.<br />
 <b>Abstract</b>: <em>Dynamic symbolic execution (DSE) is an effective method
 for automated program testing and bug detection. It is increasing the code
 coverage by the complex branches exploration during hybrid fuzzing. DSE tools
 invert the branches along some execution path and help fuzzer examine
 previously unavailable program parts. DSE often faces over- and underconstraint
 problems. The first one leads to significant analysis complication while the
 second one causes inaccurate symbolic execution.
 We propose strong optimistic solving method that eliminates irrelevant path
 predicate constraints for target branch inversion. We eliminate such symbolic
 constraints that the target branch is not control dependent on. Moreover, we
 separately handle symbolic branches that have nested control transfer
 instructions that pass control beyond the parent branch scope, e.g. return,
 goto, break, etc. We implement the proposed method in our dynamic symbolic
 execution tool Sydr.
 We evaluate the strong optimistic strategy, the optimistic strategy that
 contains only the last constraint negation, and their combination. The results
 show that the strategies combination helps increase either the code coverage or
 the average number of correctly inverted branches per one minute. It is optimal
 to apply both strategies together in contrast with other configurations.</em>
</li><br/>
<li>
<b>Greybox Program Synthesis: A New Approach to Attack Dataflow Obfuscation</b><br />
 <b>Talk at</b>: Blackhat USA, Las Vegas, Nevada, 2021. [<a href="publications/BHUSA2021-David-Greybox-Program-Synthesis.pdf">slide</a>]<br />
 <b>Authors</b>: Robin David<br />
 <b>Abstract</b>: <em>This talk presents the latest advances in program synthesis applied for deobfuscation. It aims at demystifying this analysis technique
 by showing how it can be put into action on obfuscation. Especially the implementation Qsynthesis released for this talk shows a complete end-to-end workflow
 to deobfuscate assembly instructions back in optimized (deobfuscated) instructions reassembled back in the binary.</em>
</li><br/>
<li>
<b>From source code to crash test-case through software testing automation</b><br />
 <b>Talk at</b>: C&ESAR, Rennes, France, 2021. [<a href="publications/CESAR2021_robin-david-paper.pdf">paper</a>] [<a href="publications/CESAR2021_robin-david-slide.pdf">slide</a>]<br />
 <b>Authors</b>: Robin David, Jonathan Salwan, Justin Bourroux<br />
 <b>Abstract</b>: <em>This paper present an approach automating the software testing process from a source code to the dynamic testing of the compiled program.  More specifically, from a static
 analysis report indicating alerts on source lines it enables testing to cover these lines dynamically and opportunistically checking whether  whether or not they can trigger
 a crash. The result is a test corpus allowing to cover alerts and to trigger them if they happen to be true positives. This paper discuss the  methodology employed to track
 alerts down in the compiled binary, the testing engines selection process and the results obtained on a TCP/IP stack implementation for embedded  and IoT systems.</em>
</li><br/>
<li>
<b>Symbolic Security Predicates: Hunt Program Weaknesses</b><br />
 <b>Talk at</b>: Ivannikov ISP RAS Open Conference, Moscow, Russia, 2021. [<a href="publications/ISPOPEN2021-security-predicates-vishnyakov.pdf">paper</a>] [<a href="publications/ISPOPEN2021-slide-security-predicates-vishnyakov.pdf">slide</a>]<br />
 <b>Authors</b>: A.Vishnyakov, V.Logunova, E.Kobrin, D.Kuts, D.Parygina, A.Fedotov<br />
 <b>Abstract</b>: <em>Dynamic symbolic execution (DSE) is a powerful method for
 path exploration during hybrid fuzzing and automatic bug detection. We propose
 security predicates to effectively detect undefined behavior and memory access
 violation errors. Initially, we symbolically execute program on paths that
 don’t trigger any errors (hybrid fuzzing may explore these paths). Then we
 construct a symbolic security predicate to verify some error condition. Thus, we
 may change the program data flow to entail null pointer dereference, division
 by zero, out-of-bounds access, or integer overflow weaknesses. Unlike static
 analysis, dynamic symbolic execution does not only report errors but also
 generates new input data to reproduce them. Furthermore, we introduce function
 semantics modeling for common C/C++ standard library functions. We aim to model
 the control flow inside a function with a single symbolic formula. This assists
 bug detection, speeds up path exploration, and overcomes overconstraints in
 path predicate. We implement the proposed techniques in our dynamic symbolic
 execution tool Sydr. Thus, we utilize powerful methods from Sydr such as path
 predicate slicing that eliminates irrelevant constraints.
 We present Juliet Dynamic to measure dynamic bug detection tools accuracy. The
 testing system also verifies that generated inputs trigger sanitizers. We
 evaluate Sydr accuracy for 11 CWEs from Juliet test suite. Sydr shows 95.59%
 overall accuracy. We make Sydr evaluation artifacts publicly available to
 facilitate results reproducibility.</em>
</li><br/>
<li>
<b>Towards Symbolic Pointers Reasoning in Dynamic Symbolic Execution</b><br />
 <b>Talk at</b>: Ivannikov Memorial Workshop, Nizhny Novgorod, Russia, 2021. [<a href="publications/IVMEM2021-symbolic-pointers-kuts.pdf">paper</a>] [<a href="publications/IVMEM2021-slide-symbolic-pointers-kuts.pdf">slide</a>]<br />
 <b>Authors</b>: Daniil Kuts<br />
 <b>Abstract</b>: <em>Dynamic symbolic execution is a widely used technique for
 automated software testing, designed for execution paths exploration and
 program errors detection. A hybrid approach has recently become widespread,
 when the main goal of symbolic execution is helping fuzzer increase program
 coverage. The more branches symbolic executor can invert, the more useful it is
 for fuzzer. A program control flow often depends on memory values, which are
 obtained by computing address indexes from user input. However, most DSE tools
 don't support such dependencies, so they miss some desired program branches. We
 implement symbolic addresses reasoning on memory reads in our dynamic symbolic
 execution tool Sydr. Possible memory access regions are determined by either
 analyzing memory address symbolic expressions, or binary searching with
 SMT-solver. We propose an enhanced linearization technique to model memory
 accesses. Different memory modeling methods are compared on the set of
 programs. Our evaluation shows that symbolic addresses handling allows to
 discover new symbolic branches and increase the program coverage.</em>
</li><br/>
<li>
<b>QSynth: A Program Synthesis based Approach for Binary Code Deobfuscation</b><br />
 <b>Talk at</b>: BAR, San Diego, California, 2020. [<a href="publications/BAR2020-qsynth-robin-david.pdf">paper</a>]<br />
 <b>Authors</b>: Robin David, Luigi Coniglio, Mariano Ceccato<br />
 <b>Abstract</b>: <em>We present a generic approach leveraging both DSE and program synthesis to successfully synthesize programs  obfuscated with Mixed-Boolean-Arithmetic, Data-Encoding
 or Virtualization. The synthesis algorithm proposed is an offline enumerate synthesis primitive guided by top-down breath-first search.  We shows its effectiveness
 against a state-of-the-art obfuscator and its scalability as it supersedes other similar approaches based on synthesis. We also show its effectiveness in presence of
 composite obfuscation (combination of various techniques). This ongoing work enlightens the effectiveness of synthesis to target certain kinds of obfuscations and
 opens the way to more robust algorithms and simplification strategies.</em>
</li><br/>
<li>
<b>Sydr: Cutting Edge Dynamic Symbolic Execution</b><br />
 <b>Talk at</b>: Ivannikov ISP RAS Open Conference, Moscow, Russia, 2020. [<a href="publications/ISPRAS2020-sydr.pdf">paper</a>] [<a href="publications/ISPOPEN2020-slide-sydr-vishnyakov.pdf">slide</a>] [<a href="https://www.ispras.ru/conf/2020/video/compiler-technology-11-december.mp4#t=6021">video</a>]<br />
 <b>Authors</b>: A.Vishnyakov, A.Fedotov, D.Kuts, A.Novikov, D.Parygina, E.Kobrin, V.Logunova, P.Belecky, S.Kurmangaleev<br />
 <b>Abstract</b>: <em>Dynamic symbolic execution (DSE) has enormous amount of applications in computer  security (fuzzing, vulnerability discovery, reverse-engineering, etc.). We propose
 several performance and accuracy improvements for dynamic symbolic execution.  Skipping non-symbolic instructions allows to build a path predicate 1.2--3.5 times faster.
 Symbolic engine simplifies formulas during symbolic execution. Path  predicate slicing eliminates irrelevant conjuncts from solver queries. We handle each jump table
 (switch statement) as multiple branches and describe the method for symbolic execution of multi-threaded programs. The proposed solutions were implemented in Sydr tool.
 Sydr performs inversion of branches in path predicate. Sydr combines DynamoRIO dynamic binary instrumentation tool with Triton symbolic engine.</em>
</li><br/>
<li>
<b>Symbolic Deobfuscation: From Virtualized Code Back to the Original</b><br />
 <b>Talk at</b>: DIMVA, Paris-Saclay, France, 2018. [<a href="publications/DIMVA2018-deobfuscation-salwan-bardin-potet.pdf">paper</a>] [<a href="publications/DIMVA2018-slide-deobfuscation-salwan-bardin-potet.pdf">slide</a>]<br />
 <b>Authors</b>: Jonathan Salwan, Sébastien Bardin, Marie-Laure Potet<br />
 <b>Abstract</b>: <em>Software protection has taken an important place during the last decade in order to protect legit software against reverse engineering or tampering.
 Virtualization is considered as one of the very best defenses against such attacks. We present a generic approach based on symbolic path exploration, taint and
 recompilation allowing to recover, from a virtualized code, a devirtualized code semantically identical to the original one and close in size. We define criteria
 and metrics to evaluate the relevance of the deobfuscated results in terms of correctness and precision. Finally we propose an open-source setup allowing to evaluate
 the proposed approach against several forms of virtualization.</em>
</li><br/>
<li>
<b>Deobfuscation of VM based software protection </b><br />
 <b>Talk at</b>: SSTIC, Rennes, France, 2017. [<a href="publications/SSTIC2017-French-Article-desobfuscation_binaire_reconstruction_de_fonctions_virtualisees-salwan_potet_bardin.pdf">french paper</a>] [<a href="publications/SSTIC2017_Deobfuscation_of_VM_based_software_protection.pdf">english slide</a>] [<a href="https://static.sstic.org/videos2017/SSTIC_2017-06-07_P08.mp4">french video</a>]<br />
 <b>Authors</b>: Jonathan Salwan, Sébastien Bardin, Marie-Laure Potet<br />
 <b>Abstract</b>: <em>In this presentation we describe an approach which consists to automatically analyze virtual machine based software protections and which recompiles a new
 version of the binary without such protections. This automated approach relies on a symbolic execution guide by a taint analysis and some concretization policies, then
 on a binary rewriting using LLVM transition.</em>
</li><br/>
<li>
<b>How Triton can help to reverse virtual machine based software protections</b><br />
 <b>Talk at</b>: CSAW SOS, NYC, New York, 2016. [<a href="publications/CSAW2016-SOS-Virtual-Machine-Deobfuscation-RThomas_JSalwan.pdf">slide</a>]<br />
 <b>Authors</b>: Jonathan Salwan, Romain Thomas<br />
 <b>Abstract</b>: <em>The first part of the talk is going to be an introduction to the Triton framework to expose its components and to explain how they work together.
 Then, the second part will include demonstrations on how it's possible to reverse virtual machine based protections using taint analysis, symbolic execution, SMT
 simplifications and LLVM-IR optimizations.</em>
</li><br/>
<li>
<b>Dynamic Binary Analysis and Obfuscated Codes</b><br  />
 <b>Talk at</b>: St'Hack, Bordeaux, France, 2016. [<a href="publications/StHack2016_Dynamic_Binary_Analysis_and_Obfuscated_Codes_RThomas_JSalwan.pdf">slide</a>]<br  />
 <b>Authors</b>: Jonathan Salwan, Romain Thomas<br />
 <b>Abstract</b>: <em>At this presentation we will talk about how a DBA (Dynamic Binary Analysis) may help a reverse engineer to reverse obfuscated code. We will first
 introduce some basic obfuscation techniques and then expose how it's possible to break some stuffs (using our open-source DBA framework - Triton) like detect opaque
 predicates, reconstruct CFG, find the original algorithm, isolate sensible data and many more... Then, we will conclude with a demo and few words about our future work.</em>
</li><br/>
<li>
<b>How Triton may help to analyse obfuscated binaries</b><br  />
 <b>Publication at</b>: MISC magazine 82, 2015. [<a href="publications/MISC-82_French_Paper_How_Triton_may_help_to_analyse_obfuscated_binaries_RThomas_JSalwan.pdf">french article</a>]<br  />
 <b>Authors</b>: Jonathan Salwan, Romain Thomas<br />
 <b>Abstract</b>: <em>Binary obfuscation is used to protect software's intellectual property. There exist different kinds of obfucation but roughly, it transforms a binary
 structure into another binary structure by preserving the same semantic. The aim of obfuscation is to ensure that the original information is "drown" in useless information
 that will make reverse engineering harder. In this article we will show how we can analyse an ofbuscated program and break some obfuscations using the Triton framework.</em>
</li><br/>
<li>
<b>Triton: A Concolic Execution Framework</b><br  />
 <b>Talk at</b>: SSTIC, Rennes, France, 2015. [<a href="publications/SSTIC2015_French_Paper_Triton_Framework_dexecution_Concolique_FSaudel_JSalwan.pdf">french paper</a>] [<a href="publications/SSTIC2015_English_slide_detailed_version_Triton_Concolic_Execution_FrameWork_FSaudel_JSalwan.pdf">detailed english slide</a>] <br />
 <b>Authors</b>: Jonathan Salwan, Florent Saudel<br />
 <b>Abstract</b>: <em>This talk is about the release of Triton, a concolic execution framework based on Pin. It provides components like a taint engine, a dynamic symbolic execution
 engine, a snapshot engine, translation of x64 instruction to SMT2, a Z3 interface to solve constraints and Python bindings. Based on these components, Triton offers the possibility
 to build tools for vulnerabilities research or reverse-engineering assistance.</em>
</li><br/>
<li>
<b>Dynamic Behavior Analysis Using Binary Instrumentation</b><br  />
 <b>Talk at</b>: St'Hack, Bordeaux, France, 2015. [<a href="publications/StHack2015_Dynamic_Behavior_Analysis_using_Binary_Instrumentation_Jonathan_Salwan.pdf">slide</a>]<br  />
 <b>Authors</b>: Jonathan Salwan<br />
 <b>Abstract</b>: <em>This talk can be considered like the part 2 of our talk at SecurityDay. In the previous part, we talked about how it was possible to cover a targeted function
 in memory using the DSE (Dynamic Symbolic Execution) approach. Cover a function (or its states) doesn't mean find all vulnerabilities, some vulnerability doesn't crashes the program.
 That's why we must implement specific analysis to find specific bugs. These analysis are based on the binary instrumentation and the runtime behavior analysis of the program. In this
 talk, we will see how it's possible to find these following kind of bugs : off-by-one, stack / heap overflow, use-after-free, format string and {write, read}-what-where.</em>
</li><br/>
<li>
<b>Covering a function using a Dynamic Symbolic Execution approach</b><br  />
 <b>Talk at</b>: Security Day, Lille, France, 2015. [<a href="publications/SecurityDay2015_dynamic_symbolic_execution_Jonathan_Salwan.pdf">slide</a>]<br  />
 <b>Authors</b>: Jonathan Salwan<br />
 <b>Abstract</b>: <em>This talk is about binary analysis and instrumentation. We will see how it's possible to target a specific function, snapshot the context memory/registers before the
 function, translate the instrumentation into an intermediate representation,apply a taint analysis based on this IR, build/keep formulas for a Dynamic Symbolic Execution (DSE), generate
 a concrete value to go through a specific path, restore the context memory/register and generate another concrete value to go through another path then repeat this operation until the
 target function is covered.</em>
</li>
</ul>


## Cite Triton

```latex
@inproceedings{SSTIC2015-Saudel-Salwan,
  author    = {Saudel, Florent and Salwan, Jonathan},
  title     = {Triton: A Dynamic Symbolic Execution Framework},
  booktitle = {Symposium sur la s{\'{e}}curit{\'{e}} des technologies de l'information
               et des communications},
  series    = {SSTIC},
  pages     = {31--54},
  address   = {Rennes, France},
  month     = jun,
  year      = {2015},
}
```
