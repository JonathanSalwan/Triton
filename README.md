<p align="center"><img width="50%" src="http://triton.quarkslab.com/files/triton2.png"/></p>

**Triton** is a dynamic binary analysis (DBA) framework. It provides internal components like a **Dynamic Symbolic Execution** (DSE) engine,
a **dynamic taint** engine, **AST representations** of the **x86**, **x86-64**, **ARM32** and **AArch64** Instructions Set Architecture (ISA),
**SMT simplification** passes, an **SMT solver** interface and, the last but not least, **Python bindings**. Based on these components,
you are able to build program analysis tools, automate reverse engineering and perform software verification.

<p align="center">
    <img src="http://triton.quarkslab.com/files/triton_v06_architecture.svg" width="80%"/></br>
    <img src="http://triton.quarkslab.com/files/triton_multi_os.png"/>
</p>


As **Triton** is still a young project, please, **don't blame us** if it is not yet reliable. [Open issues](https://github.com/JonathanSalwan/Triton/issues) or
[pull requests](https://github.com/JonathanSalwan/Triton/pulls) are always better than troll =).

Full documentation is available on our [doxygen page](http://triton.quarkslab.com/documentation/doxygen).</p>

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
    <img src="https://codecov.io/gh/JonathanSalwan/Triton/branch/dev-v0.7/graph/badge.svg" alt="Codecov" />
  </a>
</p>

### Quick start

* [Description](http://triton.quarkslab.com/documentation/doxygen/#description_sec)
* [Installation](http://triton.quarkslab.com/documentation/doxygen/#install_sec)
* [Examples](https://github.com/JonathanSalwan/Triton/tree/master/src/examples)
* [Python Bindings](http://triton.quarkslab.com/documentation/doxygen/py_triton_page.html)
* [Presentations and Publications](http://triton.quarkslab.com/documentation/doxygen/#publications_sec)

### News

A [blog](http://triton.quarkslab.com/blog/) is available and you can follow us on twitter [@qb_triton](https://twitter.com/qb_triton) or via our [RSS](http://triton.quarkslab.com/rss.xml) feed.

### Support

* **IRC**: #qb_triton@freenode
* **Mail**: triton at quarkslab com

### Authors

* **Jonathan Salwan** - Lead dev, Quarkslab
* **Christian Heitman** - Core dev, Quarkslab
* **Pierrick Brunet** - Core dev, Quarkslab
* **Romain Thomas** - Core dev, Quarkslab
* **Florent Saudel** - Core dev, Bordeaux University

### Cite Triton

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
