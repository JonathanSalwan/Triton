Triton
======

**Table of Contents**

- [Description](#Description)
- [Symbolic Engine](#Symbolic-Engine)
- [Taint Engine](#Taint-Engine)
- [Z3 - Solver engine](#Z3---Solver-engine)
- [Intermediate Representation (SMT2-LIB)](#)
- [Snapshot engine](#Snapshot-engine)
- [Behavior analysis](#Behavior-analysis)
- [Install](#Install)
- [SMT Semantics supported](#SMT-Semantics-supported)
- [Acknowledgement](#Acknowledgement)

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

Acknowledgement
---------------

* Florent Saudel
* Emmanuel Fleury
* Jonathan Salwan

