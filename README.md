<p align="center"><img width="50%" src="http://triton.quarkslab.com/files/triton2.png"/></p>

**Triton** is a dynamic binary analysis (DBA) framework. It provides internal components like a **Dynamic Symbolic Execution** (DSE) engine,
a **dynamic taint** engine, **AST representations** of the **x86**, **x86-64**, **ARM32** and **AArch64** Instructions Set Architecture (ISA),
**SMT simplification** passes, an **SMT solver** interface and, the last but not least, **Python bindings**. Based on these components,
you are able to build program analysis tools, automate reverse engineering and perform software verification.

<p align="center">
    <img src="http://triton.quarkslab.com/files/triton_v06_architecture.svg" width="80%"/></br>
    <img src="http://triton.quarkslab.com/files/triton_multi_os.png"/>
</p>


As **Triton** is a kind of a part-time project, please, **don't blame us** if it is not fully reliable. [Open issues](https://github.com/JonathanSalwan/Triton/issues) or
[pull requests](https://github.com/JonathanSalwan/Triton/pulls) are always better than trolling =). However, you can follow the development on twitter
[@qb_triton](https://twitter.com/qb_triton).

<p align="center">
  <a href="https://github.com/JonathanSalwan/Triton/actions/workflows/linux.yml/">
    <img src="https://github.com/JonathanSalwan/Triton/actions/workflows/linux.yml/badge.svg">
  </a>
  &nbsp;
  <a href="https://github.com/JonathanSalwan/Triton/actions/workflows/osx.yml/">
    <img src="https://github.com/JonathanSalwan/Triton/actions/workflows/osx.yml/badge.svg">
  </a>
  &nbsp;
  <a href="https://ci.appveyor.com/project/JonathanSalwan/triton">
    <img src="https://img.shields.io/appveyor/ci/JonathanSalwan/triton/master.svg?label=Tests%20on%20Windows&logo=appveyor">
  </a>
  &nbsp;
  <a href="https://codecov.io/gh/JonathanSalwan/Triton">
    <img src="https://codecov.io/gh/JonathanSalwan/Triton/branch/master/graph/badge.svg" alt="Codecov" />
  </a>
  &nbsp;
  <a href="https://github.com/JonathanSalwan/Triton/releases">
    <img src="https://img.shields.io/github/v/release/JonathanSalwan/Triton">
  </a>
  &nbsp;
  <a href="https://twitter.com/qb_triton">
   <img src="https://img.shields.io/twitter/follow/qb_triton?color=1da1f2&label=Follow&logo=twitter&logoColor=white&style=square">
  </a>
</p>

## Quick start

* [Installation](http://triton.quarkslab.com/documentation/doxygen/#install_sec)
* [Python API](http://triton.quarkslab.com/documentation/doxygen/py_triton_page.html)
* [C++ API](https://triton.quarkslab.com/documentation/doxygen/annotated.html)
* [Python Examples](https://github.com/JonathanSalwan/Triton/tree/master/src/examples/python)
* [Presentations and Publications](http://triton.quarkslab.com/documentation/doxygen/#publications_sec)

### Getting started

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
>>> ctx.processing(Instruction(b"\x48\x89\xc1")) # xor rcx, rax

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

## Authors

* **Jonathan Salwan** - Lead dev, Quarkslab
* **Christian Heitman** - Core dev, Quarkslab
* **Pierrick Brunet** - Core dev, Quarkslab
* **Romain Thomas** - Core dev, Quarkslab
* **Florent Saudel** - Core dev, Bordeaux University

### Cite Triton

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
