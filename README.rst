Triton
======

**Table of Contents**

- `Description <#description>`_
- `Symbolic Engine <#symbolic-engine>`_
- `Taint Engine <#taint-engine>`_
- `Snapshot engine <#snapshot-engine>`_
- `Intermediate Representation (SMT2-LIB) <#intermediate-representation-smt2-lib>`_
- `Z3 - Solver engine <#z3---solver-engine>`_
- `Multi-threading <#multi-threading>`_
- `Runtime behavior analysis <#runtime-behavior-analysis>`_
- `Install <#install>`_
- `SMT Semantics supported <#smt-semantics-supported>`_
- `Related presentations <#related-presentations>`_
- `Auhtors and acknowledgement <#authors-and-acknowledgement>`_

Description
-----------

Triton is a project which provides more components to the framework Pin in order to improve the instrumentation and to apply some program analysis oriented for vulnerabilities research. Basically, these components are a taint engine, a dynamic symbolic engine, a memory snapshot engine, a translation of x64 instruction to the SMT2-LIB language and a Z3 interface to solve constraints. Based on these components, Triton provides runtime behavior analysis to find some kind of bugs.

Symbolic Engine
---------------

TODO

Taint Engine
------------

TODO

Snapshot engine
---------------

TODO

Intermediate Representation (SMT2-LIB)
--------------------------------------

TODO

Z3 - Solver engine
------------------

TODO

Multi-threading
---------------

TODO

Runtime behavior analysis
-------------------------

TODO

Install
-------

Below, the install's command line::
  
  $ cd pin-2.14-71313-gcc.4.4.7-linux/source/tools/
  $ git clone git@github.com:JonathanSalwan/Triton.git
  $ cd Triton
  $ make
  $ ./triton -startAnalysis check ./samples/crackmes/crackme_xor elite


SMT Semantics supported
-----------------------

Short view of what Triton supports.

+----------+----------------------------------------------------------+
| Mnemonic | Description                                              |
+----------+----------------------------------------------------------+
| ADD      | Add                                                      |
+----------+----------------------------------------------------------+
| CMP      | Compare Two Operands                                     |
+----------+----------------------------------------------------------+
| MOV      | Move                                                     |
+----------+----------------------------------------------------------+
| MOVSX    | Move with Sign-Extension                                 |
+----------+----------------------------------------------------------+
| MOVZX    | Move with Zero-Extend                                    |
+----------+----------------------------------------------------------+
| POP      | Pop a Value from the Stack                               |
+----------+----------------------------------------------------------+
| PUSH     | Push a Value onto the Stack                              |
+----------+----------------------------------------------------------+
| SUB      | Subtract                                                 |
+----------+----------------------------------------------------------+
| XOR      | Logical Exclusive OR                                     |
+----------+----------------------------------------------------------+

+-------+----------------------------------------------------------+
| Flags | Description                                              |
+-------+----------------------------------------------------------+
| AF    | Adjust flag                                              |
+-------+----------------------------------------------------------+
| CF    | Carry flag                                               |
+-------+----------------------------------------------------------+
| OF    | Overflow flag                                            |
+-------+----------------------------------------------------------+
| PF    | Parity flag                                              |
+-------+----------------------------------------------------------+
| SF    | Sign flag                                                |
+-------+----------------------------------------------------------+
| ZF    | Zero flag                                                |
+-------+----------------------------------------------------------+

Related presentations
---------------------

| **Dynamic Behavior Analysis Using Binary Instrumentation**
| St'Hack, Bordeaux, 2015. [`slide <http://shell-storm.org/talks/StHack2015_Dynamic_Behavior_Analysis_using_Binary_Instrumentation_Jonathan_Salwan.pdf>`_] 
| `Description`: *This talk can be considered like the part 2 of my talk at SecurityDay. In the previous part, I talked about how it was possible to cover a targeted function in memory using the DSE (Dynamic Symbolic Execution) approach. Cover a function (or its states) doesn't mean find all vulnerabilities, some vulnerability doesn't crashes the program. That's why we must implement specific analysis to find specific bugs. These analysis are based on the binary instrumentation and the runtime behavior analysis of the program. In this talk, we will see how it's possible to find these following kind of bugs : off-by-one, stack / heap overflow, use-after-free, format string and {write, read}-what-where.*
|
| **Covering a function using a Dynamic Symbolic Execution approach**
| Security Day, Lille, 2015. [`slide <http://shell-storm.org/talks/SecurityDay2015_dynamic_symbolic_execution_Jonathan_Salwan.pdf>`_] 
| `Description`: *This talk is about binary analysis and instrumentation. We will see how it's possible to target a specific function, snapshot the context memory/registers before the function, translate the instrumentation into an intermediate representation, apply a taint analysis based on this IR, build/keep formulas for a Dynamic Symbolic Execution (DSE), generate a concrete value to go through a specific path, restore the context memory/register and generate another concrete value to go through another path then repeat this operation until the target function is covered.*


Authors and acknowledgement
---------------------------

* Florent Saudel (core dev)
* Jonathan Salwan (core dev)
* Emmanuel Fleury (feedbacks, ideas, design)

