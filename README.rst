**Triton** is a concolic execution framework based on Pin. It provides these following components:

* `Taint engine <https://github.com/JonathanSalwan/Triton/wiki/Taint-Engine>`_
* `Dynamic symbolic execution engine <https://github.com/JonathanSalwan/Triton/wiki/Symbolic-Engine>`__
* `Snapshot engine <https://github.com/JonathanSalwan/Triton/wiki/Snapshot-Engine>`___
* Translation of x64 instruction into `SMT2-LIB representation <https://github.com/JonathanSalwan/Triton/wiki/SMT2-LIB-Representation>`____
* `Z3 interface <https://github.com/JonathanSalwan/Triton/wiki/Solver-Engine-Z3>`_____ to solve constraints
* `Python bindings <https://github.com/JonathanSalwan/Triton/wiki/Python-Bindings>`______. 

Based on these components, Triton provides `runtime behavior analysis <https://github.com/JonathanSalwan/Triton/wiki/Runtime-Behavior-Analysis>`______ 
for vulnerabilities research and can provide some reverse engineering assistance.

All information and examples about **Triton** are published on the `wiki <https://github.com/JonathanSalwan/Triton/wiki>`________.

As Triton is a young project, please, **don't blame us** if it is not yet reliable. `Pull requests <https://github.com/JonathanSalwan/Triton/issues>`_________.
are always better than troll =).

