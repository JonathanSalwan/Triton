<p align="center"><img width="50%" src="http://triton.quarkslab.com/files/triton2.png"/></p>

**Triton** is a dynamic binary analysis (DBA) framework. It provides internal components like a Dynamic Symbolic Execution (DSE)
engine, a Taint Engine, AST representations of the x86 and the x86-64 instructions set semantics, SMT simplification
passes, an SMT Solver Interface and, the last but not least, Python bindings.

<p align="center">
    <img src="http://triton.quarkslab.com/files/triton_v03_architecture.svg"/></br>
    <img src="http://triton.quarkslab.com/files/triton_multi_os.png"/>
</p>

Based on these components, you are able to build program analysis tools, automate reverse engineering and perform software verification.
As **Triton** is still a young project, please, **don't blame us** if it is not yet reliable. [Open issues](https://github.com/JonathanSalwan/Triton/issues) or
[pull requests](https://github.com/JonathanSalwan/Triton/pulls) are always better than troll =).

A full documentation is available on our [doxygen page](http://triton.quarkslab.com/documentation/doxygen).</p>

<p>
  <a href="https://travis-ci.org/JonathanSalwan/Triton/branches">
    <img src="https://img.shields.io/travis/JonathanSalwan/Triton/master.svg?style=flat-square&label=unix%20build">
  </a>
  &nbsp;
  <a href="https://ci.appveyor.com/project/JonathanSalwan/triton">
    <img src="https://img.shields.io/appveyor/ci/JonathanSalwan/triton/master.svg?style=flat-square&label=windows%20build">
  </a>
  &nbsp;
  <a href="https://codecov.io/gh/JonathanSalwan/Triton">
    <img src="https://codecov.io/gh/JonathanSalwan/Triton/branch/master/graph/badge.svg" alt="Codecov" />
  </a>
</p>

### Quick start

* [Description](http://triton.quarkslab.com/documentation/doxygen/#description_sec)
* [Installation](http://triton.quarkslab.com/documentation/doxygen/#install_sec)
* [Examples](https://github.com/JonathanSalwan/Triton/tree/master/src/examples)
* [Presentations and Publications](http://triton.quarkslab.com/documentation/doxygen/#publications_sec)

### Internal documentation

* [Dynamic Symbolic Execution](http://triton.quarkslab.com/documentation/doxygen/engine_DSE_page.html)
* [Symbolic Execution Optimizations](http://triton.quarkslab.com/documentation/doxygen/py_MODE_page.html)
* [AST Representations of Semantics](http://triton.quarkslab.com/documentation/doxygen/py_ast_page.html)
* [SMT Semantics Supported](http://triton.quarkslab.com/documentation/doxygen/SMT_Semantics_Supported_page.html)
* [SMT Solver Interface](http://triton.quarkslab.com/documentation/doxygen/solver_interface_page.html)
* [SMT Simplification Passes](http://triton.quarkslab.com/documentation/doxygen/SMT_simplification_page.html)
* [Spread Taint](http://triton.quarkslab.com/documentation/doxygen/engine_Taint_page.html)
* [Tracer Independent](http://triton.quarkslab.com/documentation/doxygen/Tracer_page.html)
* [Python Bindings](http://triton.quarkslab.com/documentation/doxygen/py_triton_page.html)

### News

A [blog](http://triton.quarkslab.com/blog/) is available and you can follow us on twitter [@qb_triton](https://twitter.com/qb_triton) or via our [RSS](http://triton.quarkslab.com/rss.xml) feed.

### Support

* **IRC**: #qb_triton@freenode
* **Mail**: triton at quarkslab com

### Authors

* **Jonathan Salwan** - Lead dev, Quarkslab
* **Pierrick Brunet** - Core dev, Quarkslab
* **Florent Saudel** - Core dev, Bordeaux University
* **Romain Thomas** - Core dev, Quarkslab

### Cite Triton

    @inproceedings{SSTIC2015-Saudel-Salwan,
      author    = {Florent Saudel and Jonathan Salwan},
      title     = {Triton: A Dynamic Symbolic Execution Framework},
      booktitle = {Symposium sur la s{\'{e}}curit{\'{e}} des technologies de l'information
                   et des communications, SSTIC, France, Rennes, June 3-5 2015},
      publisher = {SSTIC},
      pages     = {31--54},
      year      = {2015},
    }

