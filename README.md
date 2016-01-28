<p align="center"><img width="50%" src="http://triton.quarkslab.com/files/triton2.png"/></p>

**Triton** is a dynamic binary analysis (DBA) framework. It provides internal components like a Dynamic Symbolic Execution (DSE)
engine, a Taint Engine, an intermediate representation based on SMT2-Lib of the x86 and x86-64 instructions set, SMT simplification
passes, an SMT Solver Interface and, the last but not least, Python bindings.

<p align="center"><img src="http://triton.quarkslab.com/files/triton_v03_architecture.svg"/></p>

Based on these components, you are able to build program analysis tools, automate reverse engineering and perform software verification.
As **Triton** is still a young project, please, **don't blame us** if it is not yet reliable. [Open issues](https://github.com/JonathanSalwan/Triton/issues) or
[pull requests](https://github.com/JonathanSalwan/Triton/pulls) are always better than troll =).

A full documentation is available on our [doxygen page](http://triton.quarkslab.com/documentation/doxygen).

### Quick start

* [Description](http://triton.quarkslab.com/documentation/doxygen/#description_sec)
* [Installation](http://triton.quarkslab.com/documentation/doxygen/#install_sec)
* [Examples](http://triton.quarkslab.com/documentation/doxygen/Tracer_page.html#Tracer_pintool)
* [Presentations and Publications](http://triton.quarkslab.com/documentation/doxygen/#publications_sec)

### Internal documentation

* [Dynamic Symbolic Execution](http://triton.quarkslab.com/documentation/doxygen/engine_DSE_page.html)
* [Symbolic Execution Optimizations](http://triton.quarkslab.com/documentation/doxygen/py_OPTIMIZATION_page.html)
* [SMT2-Lib Representation](http://triton.quarkslab.com/documentation/doxygen/py_smt2lib_page.html)
* [SMT Semantics Supported](http://triton.quarkslab.com/documentation/doxygen/SMT_Semantics_Supported_page.html)
* [SMT Solver Interface](http://triton.quarkslab.com/documentation/doxygen/solver_interface_page.html)
* [SMT Simplification Passes](http://triton.quarkslab.com/documentation/doxygen/SMT_simplification_page.html)
* [Spread Taint](http://triton.quarkslab.com/documentation/doxygen/engine_Taint_page.html)
* [Replay Trace via Snapshot](http://triton.quarkslab.com/documentation/doxygen/Snapshot_page.html)
* [Tracer Independent](http://triton.quarkslab.com/documentation/doxygen/Tracer_page.html)
* [Python Bindings](http://triton.quarkslab.com/documentation/doxygen/py_triton_page.html)
