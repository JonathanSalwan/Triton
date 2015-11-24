<p align="center"><img width="50%" src="http://triton.quarkslab.com/files/triton2.png"/></p>

**Triton** is a Pin-based dynamic symbolic execution (DSE) execution framework. Although Triton is a DSE framework, it also
provides internal components like a
[taint engine](http://triton.quarkslab.com/documentation/taintEngine/), a
[dynamic symbolic execution engine](http://triton.quarkslab.com/documentation/symbolicEngine/), a
[snapshot engine](http://triton.quarkslab.com/documentation/snapshotEngine/), translation of x64
instructions into the [SMT2-LIB representation](http://triton.quarkslab.com/documentation/smt2lib-representation/),
a [Z3 interface](http://triton.quarkslab.com/documentation/solverEngine/) to solve constraints 
and, the last but not least, [Python bindings](http://triton.quarkslab.com/documentation/api/triton-methods/).

<p align="center"><img src="http://shell-storm.org/files/triton_archi_3.svg"/></p>

Based on these components, you are able to build program analysis tools, automate reverse engineering
or perform software verification.

The [wiki](http://triton.quarkslab.com/documentation/) describes **Triton** and its components under the hood. As **Triton** is a young project,
please, **don't blame us** if it is not yet reliable. [Open issues](https://github.com/JonathanSalwan/Triton/issues) or
[pull requests](https://github.com/JonathanSalwan/Triton/pulls) are always better than troll =).

### Quick start

* [Installation](http://triton.quarkslab.com/documentation/installation/)
* [Examples](http://triton.quarkslab.com/documentation/examples/)
* [Tools](http://triton.quarkslab.com/documentation/tools/)

### Internal documentation

* [Symbolic Engine](http://triton.quarkslab.com/documentation/symbolicEngine/)
* [Taint Engine](http://triton.quarkslab.com/documentation/taintEngine/)
* [Snapshot Engine](http://triton.quarkslab.com/documentation/snapshotEngine/)
* [SMT2-LIB Representation](http://triton.quarkslab.com/documentation/smt2lib-representation/)
* [Solver Engine - Z3](http://triton.quarkslab.com/documentation/solverEngine/)
* [SMT Semantics Supported](http://triton.quarkslab.com/documentation/smt-semantics-supported/)
* [Python Bindings](http://triton.quarkslab.com/documentation/api/triton-methods/)

### Blog post

* [Code coverage using dynamic symbolic execution](http://triton.quarkslab.com/blog/Code-coverage-using-dynamic-symbolic-execution/)
* [Triton under the hood - First approach with the framework](http://triton.quarkslab.com/blog/first-approach-with-the-framework/)

### Extra information

* [Publications](http://triton.quarkslab.com/documentation/#presentations)
* [About us](http://triton.quarkslab.com/about/)

