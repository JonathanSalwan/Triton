<p align="center"><img src="http://shell-storm.org/files/triton_logo_1.png"/></p>

**Triton** is a concolic execution framework based on Pin. It provides components like a
[taint engine](https://github.com/JonathanSalwan/Triton/wiki/Taint-Engine), a
[dynamic symbolic execution engine](https://github.com/JonathanSalwan/Triton/wiki/Symbolic-Engine), a
[snapshot engine](https://github.com/JonathanSalwan/Triton/wiki/Snapshot-Engine), translation of x64
instruction into the [SMT2-LIB representation](https://github.com/JonathanSalwan/Triton/wiki/SMT2-LIB-Representation),
a [Z3 interface](https://github.com/JonathanSalwan/Triton/wiki/Solver-Engine-Z3) to solve constraints 
and [Python bindings](https://github.com/JonathanSalwan/Triton/wiki/Python-Bindings).

<p align="center"><img src="http://shell-storm.org/files/triton_archi_3.svg"/></p>

Based on these components, **Triton** offers the possibility to build tools for vulnerabilities 
research and can provide some reverse engineering assistance.

The [wiki](https://github.com/JonathanSalwan/Triton/wiki) describes **Triton** under the hood. As **Triton** is a young project,
please, **don't blame us** if it is not yet reliable. [Open issues](https://github.com/JonathanSalwan/Triton/issues) or
[pull requests](https://github.com/JonathanSalwan/Triton/pulls) are always better than troll =).

### Quick start

* [Installation](https://github.com/JonathanSalwan/Triton/wiki/Installation)
* [Examples](https://github.com/JonathanSalwan/Triton/wiki/Examples)
* [Tools](https://github.com/JonathanSalwan/Triton/wiki/Tools)

### Internal documentation

* [Symbolic Engine](https://github.com/JonathanSalwan/Triton/wiki/Symbolic-Engine)
* [Taint Engine](https://github.com/JonathanSalwan/Triton/wiki/Taint-Engine)
* [Snapshot Engine](https://github.com/JonathanSalwan/Triton/wiki/Snapshot-Engine)
* [SMT2-LIB Representation](https://github.com/JonathanSalwan/Triton/wiki/SMT2-LIB-Representation)
* [Solver Engine - Z3](https://github.com/JonathanSalwan/Triton/wiki/Solver-Engine-Z3)
* [SMT Semantics Supported](https://github.com/JonathanSalwan/Triton/wiki/SMT-Semantics-Supported)
* [Python Bindings](https://github.com/JonathanSalwan/Triton/wiki/Python-Bindings)

### Blog post

* [Triton hunder the hood - First approach with the framework](http://blog.quarkslab.com/triton-under-the-hood.html)

### Extra information

* [Publications](https://github.com/JonathanSalwan/Triton/wiki/Publications)
* [Authors and Acknowledgements](https://github.com/JonathanSalwan/Triton/wiki/Authors-and-Acknowledgements)


