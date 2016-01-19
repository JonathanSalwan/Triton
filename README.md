<p align="center"><img width="50%" src="http://triton.quarkslab.com/files/triton2.png"/></p>

**Triton** is a dynamic binary analysis (DBA) framework. It provides internal components like a Dynamic Symbolic Exuction (DSE)
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
* [Presentations and Publications](http://triton.quarkslab.com/documentation/doxygen/#publications_sec)

### Internal documentation

* [Dynamic Symbolic Execution](http://triton.quarkslab.com/documentation/doxygen/engine_DSE_page.html)
* [SMT2-Lib](http://triton.quarkslab.com/documentation/doxygen/py_smt2lib_page.html)
* [SMT Semantics Supported](http://triton.quarkslab.com/documentation/doxygen/SMT_Semantics_Supported_page.html)
* [SMT Solver Interface](http://triton.quarkslab.com/documentation/doxygen/solver_interface_page.html)
* [SMT simplification passes](http://triton.quarkslab.com/documentation/doxygen/SMT_simplification_page.html)
* [Taint Engine](http://triton.quarkslab.com/documentation/doxygen/engine_Taint_page.html)
* [Python bindings](http://triton.quarkslab.com/documentation/doxygen/py_triton_page.html)

### Windows compilation instructions

* Need to install VS14 to fix https://connect.microsoft.com/VisualStudio/feedback/details/792161/constructor-initializer-list-does-not-support-braced-init-list-form
* http://stackoverflow.com/questions/30760889/unknown-compiler-version-while-compiling-boost-with-msvc-14-0-vs-2015
* python27_d.lib is not shipped with the default python installer so we need to build it if we want a debug version. If we just want the release version it should work fine (python27.lib does exist)
* We need to build capstone with VS2015 to get the .lib file that we will use. get the source code from the oficial website and follow: https://github.com/aquynh/capstone/blob/master/COMPILE_MSVC.TXT
* Capstone library for x64 and x86 for VS14 are in the capstone_libs folder