Triton
======

**Table of Contents**

- `Description <#description>`_
- `Symbolic Engine <#symbolic-engine>`_
- `Taint Engine <#taint-engine>`_
- `Z3 - Solver engine <#z3---solver-engine>`_
- `Intermediate Representation (SMT2-LIB) <#intermediate-representation-smt2-lib>`_
- `Snapshot engine <#snapshot-engine>`_
- `Behavior analysis <#behavior-analysis>`_
- `Install <#install>`_
- `SMT Semantics supported <#smt-semantics-supported>`_
- `Related presentations <#related-presentations>`_
- `Acknowledgement <#acknowledgement>`_

Description
-----------

TODO

Symbolic Engine
---------------

TODO

Taint Engine
------------

TODO

Z3 - Solver engine
------------------

TODO

Intermediate Representation (SMT2-LIB)
--------------------------------------

TODO

Snapshot engine
---------------

TODO

Behavior analysis
-----------------

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

| **Covering a function using a Dynamic Symbolic Execution approach**
| Security Day, Lille, 2015. [`slide <http://shell-storm.org/talks/SecurityDay2015_dynamic_symbolic_execution_Jonathan_Salwan.pdf>`_] 
| `Description`: *This talk is about binary analysis and instrumentation. We will see how it's possible to target a specific function, snapshot the context memory/registers before the function, translate the instrumentation into an intermediate representation, apply a taint analysis based on this IR, build/keep formulas for a Dynamic Symbolic Execution (DSE), generate a concrete value to go through a specific path, restore the context memory/register and generate another concrete value to go through another path then repeat this operation until the target function is covered.*


Acknowledgement
---------------

* Florent Saudel
* Emmanuel Fleury
* Jonathan Salwan

