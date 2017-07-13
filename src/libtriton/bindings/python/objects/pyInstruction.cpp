//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/exceptions.hpp>
#include <triton/instruction.hpp>



/*! \page py_Instruction_page Instruction
    \brief [**python api**] All information about the Instruction python object.

\tableofcontents

\section py_Instruction_description Description
<hr>

This object is used to represent an Instruction.

~~~~~~~~~~~~~{.py}
>>> from triton import TritonContext, ARCH, Instruction, OPERAND

>>> trace = [
...     (0x400000, "\x48\x8b\x05\xb8\x13\x00\x00"), # mov        rax, QWORD PTR [rip+0x13b8]
...     (0x400007, "\x48\x8d\x34\xc3"),             # lea        rsi, [rbx+rax*8]
...     (0x40000b, "\x67\x48\x8D\x74\xC3\x0A"),     # lea        rsi, [ebx+eax*8+0xa]
...     (0x400011, "\x66\x0F\xD7\xD1"),             # pmovmskb   edx, xmm1
...     (0x400015, "\x89\xd0"),                     # mov        eax, edx
...     (0x400017, "\x80\xf4\x99"),                 # xor        ah, 0x99
... ]

>>> ctxt = TritonContext()

# Set the arch
>>> ctxt.setArchitecture(ARCH.X86_64)

>>> for (addr, opcode) in trace:
...
...     # Build an instruction
...     inst = Instruction()
...
...     # Setup opcode
...     inst.setOpcode(opcode)
...
...     # Setup Address
...     inst.setAddress(addr)
...
...     # Process everything
...     if not ctxt.processing(inst):
...         print "Fail an instruction"
...
...     print inst
...     for op in inst.getOperands():
...         print '   ', op
...         if op.getType() == OPERAND.MEM:
...             print '         base  : ', op.getBaseRegister()
...             print '         index : ', op.getIndexRegister()
...             print '         disp  : ', op.getDisplacement()
...             print '         scale : ', op.getScale()
...     print
0x400000: mov rax, qword ptr [rip + 0x13b8]
    rax:64 bv[63..0]
    [@0x4013bf]:64 bv[63..0]
         base  :  rip:64 bv[63..0]
         index :  unknown:1 bv[0..0]
         disp  :  0x13b8:64 bv[63..0]
         scale :  0x1:64 bv[63..0]
<BLANKLINE>
0x400007: lea rsi, qword ptr [rbx + rax*8]
    rsi:64 bv[63..0]
    [@0x0]:64 bv[63..0]
         base  :  rbx:64 bv[63..0]
         index :  rax:64 bv[63..0]
         disp  :  0x0:64 bv[63..0]
         scale :  0x8:64 bv[63..0]
<BLANKLINE>
0x40000b: lea rsi, dword ptr [ebx + eax*8 + 0xa]
    rsi:64 bv[63..0]
    [@0xa]:32 bv[31..0]
         base  :  ebx:32 bv[31..0]
         index :  eax:32 bv[31..0]
         disp  :  0xa:32 bv[31..0]
         scale :  0x8:32 bv[31..0]
<BLANKLINE>
0x400011: pmovmskb edx, xmm1
    edx:32 bv[31..0]
    xmm1:128 bv[127..0]
<BLANKLINE>
0x400015: mov eax, edx
    eax:32 bv[31..0]
    edx:32 bv[31..0]
<BLANKLINE>
0x400017: xor ah, 0x99
    ah:8 bv[15..8]
    0x99:8 bv[7..0]
<BLANKLINE>

~~~~~~~~~~~~~

\subsection py_Instruction_constructor Constructor

~~~~~~~~~~~~~{.py}
>>> inst = Instruction("\x48\xC7\xC0\x01\x00\x00\x00")
>>> inst.setAddress(0x40000)
>>> ctxt.processing(inst)
True
>>> print inst
0x40000: mov rax, 1

~~~~~~~~~~~~~

~~~~~~~~~~~~~{.py}
>>> inst = Instruction()
>>> inst.setAddress(0x40000)
>>> inst.setOpcode("\x48\xC7\xC0\x01\x00\x00\x00")
>>> ctxt.processing(inst)
True
>>> print inst
0x40000: mov rax, 1

~~~~~~~~~~~~~

\section Instruction_py_api Python API - Methods of the Instruction class
<hr>

- <b>integer getAddress(void)</b><br>
Returns the address of the instruction.

- <b>string getDisassembly(void)</b><br>
Returns the disassembly of the instruction.

- <b>[tuple, ...] getLoadAccess(void)</b><br>
Returns the list of all implicit and explicit LOAD access as list of tuple <\ref py_MemoryAccess_page, \ref py_AstNode_page>.

- <b>integer getNextAddress(void)</b><br>
Returns the next address of the instruction.

- <b>bytes getOpcode(void)</b><br>
Returns the opcode of the instruction.

- <b>[\ref py_Immediate_page, \ref py_MemoryAccess_page, \ref py_Register_page, ...] getOperands(void)</b><br>
Returns the operands of the instruction as list of \ref py_Immediate_page, \ref py_MemoryAccess_page or \ref py_Register_page.

- <b>\ref py_PREFIX_page getPrefix(void)</b><br>
Returns the instruction prefix.

- <b>[tuple, ...] getReadImmediates(void)</b><br>
Returns a list of tuple <\ref py_Immediate_page, \ref py_AstNode_page> which represents all implicit and explicit immediate inputs.

- <b>[tuple, ...] getReadRegisters(void)</b><br>
Returns a list of tuple <\ref py_Register_page, \ref py_AstNode_page> which represents all implicit and explicit register (flags includes) inputs.

- <b>integer getSize(void)</b><br>
Returns the size of the instruction.

- <b>[tuple, ...] getStoreAccess(void)</b><br>
Returns the list of all implicit and explicit STORE access as list of tuple <\ref py_MemoryAccess_page, \ref py_AstNode_page>.

- <b>[\ref py_SymbolicExpression_page, ...] getSymbolicExpressions(void)</b><br>
Returns the list of symbolic expressions of the instruction.

- <b>integer getThreadId(void)</b><br>
Returns the thread id of the instruction.

- <b>\ref py_OPCODE_page getType(void)</b><br>
Returns the type of the instruction.

- <b>[tuple, ...] getWrittenRegisters(void)</b><br>
Returns a list of tuple <\ref py_Register_page, \ref py_AstNode_page> which represents all implicit and explicit register (flags includes) outputs.

- <b>bool isBranch(void)</b><br>
Returns true if the instruction is a branch (i.e x86: JUMP, JCC).

- <b>bool isConditionTaken(void)</b><br>
Returns true if the condition is taken (i.e x86: JCC, CMOVCC, SETCC, ...).

- <b>bool isControlFlow(void)</b><br>
Returns true if the instruction modifies the control flow (i.e x86: JUMP, JCC, CALL, RET).

- <b>bool isMemoryRead(void)</b><br>
Returns true if the instruction contains an expression which reads the memory.

- <b>bool isMemoryWrite(void)</b><br>
Returns true if the instruction contains an expression which writes into the memory.

- <b>bool isPrefixed(void)</b><br>
Returns true if the instruction has a prefix.

- <b>bool isSymbolized(void)</b><br>
Returns true if at least one of its \ref py_SymbolicExpression_page contains a symbolic variable.

- <b>bool isTainted(void)</b><br>
Returns true if at least one of its \ref py_SymbolicExpression_page is tainted.

- <b>void setAddress(integer addr)</b><br>
Sets the address of the instruction.

- <b>void setOpcode(bytes opcode)</b><br>
Sets the opcode of the instruction.

- <b>void setThreadId(integer tid)</b><br>
Sets the thread id of the instruction.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! Instruction destructor.
      void Instruction_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyInstruction_AsInstruction(self);
        Py_DECREF(self);
      }


      static PyObject* Instruction_getAddress(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyInstruction_AsInstruction(self)->getAddress());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Instruction_getDisassembly(PyObject* self, PyObject* noarg) {
        try {
          return PyString_FromFormat("%s", PyInstruction_AsInstruction(self)->getDisassembly().c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Instruction_getLoadAccess(PyObject* self, PyObject* noarg) {
        try {
          PyObject* ret;
          triton::uint32 index = 0;
          const auto& loadAccess = PyInstruction_AsInstruction(self)->getLoadAccess();

          ret = xPyList_New(loadAccess.size());
          for (auto it = loadAccess.cbegin(); it != loadAccess.cend(); it++) {
            PyObject* item = xPyTuple_New(2);
            PyTuple_SetItem(item, 0, PyMemoryAccess(std::get<0>(*it)));
            PyTuple_SetItem(item, 1, PyAstNode(std::get<1>(*it)));
            PyList_SetItem(ret, index++, item);
          }

          return ret;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Instruction_getNextAddress(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyInstruction_AsInstruction(self)->getNextAddress());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Instruction_getOpcode(PyObject* self, PyObject* noarg) {
        try {
          const triton::uint8* opcode = PyInstruction_AsInstruction(self)->getOpcode();
          triton::uint32 size         = PyInstruction_AsInstruction(self)->getSize();
          return PyBytes_FromStringAndSize(reinterpret_cast<const char*>(opcode), size);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Instruction_getSize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyInstruction_AsInstruction(self)->getSize());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Instruction_getStoreAccess(PyObject* self, PyObject* noarg) {
        try {
          PyObject* ret;
          triton::uint32 index = 0;
          const auto& storeAccess = PyInstruction_AsInstruction(self)->getStoreAccess();

          ret = xPyList_New(storeAccess.size());
          for (auto it = storeAccess.cbegin(); it != storeAccess.cend(); it++) {
            PyObject* item = xPyTuple_New(2);
            PyTuple_SetItem(item, 0, PyMemoryAccess(std::get<0>(*it)));
            PyTuple_SetItem(item, 1, PyAstNode(std::get<1>(*it)));
            PyList_SetItem(ret, index++, item);
          }

          return ret;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Instruction_getOperands(PyObject* self, PyObject* noarg) {
        try {
          triton::arch::Instruction* inst;
          triton::usize opSize;
          PyObject* operands;

          inst     = PyInstruction_AsInstruction(self);
          opSize   = inst->operands.size();
          operands = xPyList_New(opSize);

          for (triton::usize index = 0; index < opSize; index++) {
            PyObject* obj = nullptr;

            if (inst->operands[index].getType() == triton::arch::OP_IMM) {
              const triton::arch::Immediate& imm = inst->operands[index].getConstImmediate();
              obj = PyImmediate(imm);
            }
            else if (inst->operands[index].getType() == triton::arch::OP_MEM) {
              const triton::arch::MemoryAccess& mem = inst->operands[index].getConstMemory();
              obj = PyMemoryAccess(mem);
            }
            else if (inst->operands[index].getType() == triton::arch::OP_REG) {
              const triton::arch::Register& reg = inst->operands[index].getConstRegister();
              obj = PyRegister(reg);
            }
            else
              continue;

            PyList_SetItem(operands, index, obj);
          }

          return operands;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Instruction_getPrefix(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyInstruction_AsInstruction(self)->getPrefix());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Instruction_getReadImmediates(PyObject* self, PyObject* noarg) {
        try {
          PyObject* ret;
          triton::uint32 index = 0;
          const auto& readImmediates = PyInstruction_AsInstruction(self)->getReadImmediates();

          ret = xPyList_New(readImmediates.size());
          for (auto it = readImmediates.cbegin(); it != readImmediates.cend(); it++) {
            PyObject* item = xPyTuple_New(2);
            PyTuple_SetItem(item, 0, PyImmediate(std::get<0>(*it)));
            PyTuple_SetItem(item, 1, PyAstNode(std::get<1>(*it)));
            PyList_SetItem(ret, index++, item);
          }

          return ret;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Instruction_getReadRegisters(PyObject* self, PyObject* noarg) {
        try {
          PyObject* ret;
          triton::uint32 index = 0;
          const auto& readRegisters = PyInstruction_AsInstruction(self)->getReadRegisters();

          ret = xPyList_New(readRegisters.size());
          for (auto it = readRegisters.cbegin(); it != readRegisters.cend(); it++) {
            PyObject* item = xPyTuple_New(2);
            PyTuple_SetItem(item, 0, PyRegister(std::get<0>(*it)));
            PyTuple_SetItem(item, 1, PyAstNode(std::get<1>(*it)));
            PyList_SetItem(ret, index++, item);
          }

          return ret;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Instruction_getSymbolicExpressions(PyObject* self, PyObject* noarg) {
        try {
          triton::arch::Instruction*  inst;
          triton::usize               exprSize;
          PyObject*                   symExprs;

          inst     = PyInstruction_AsInstruction(self);
          exprSize = inst->symbolicExpressions.size();
          symExprs = xPyList_New(exprSize);

          for (triton::usize index = 0; index < exprSize; index++) {
            PyObject* obj = nullptr;
            obj = PySymbolicExpression(inst->symbolicExpressions[index]);
            PyList_SetItem(symExprs, index, obj);
          }

          return symExprs;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Instruction_getThreadId(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyInstruction_AsInstruction(self)->getThreadId());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Instruction_getType(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyInstruction_AsInstruction(self)->getType());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Instruction_getWrittenRegisters(PyObject* self, PyObject* noarg) {
        try {
          PyObject* ret;
          triton::uint32 index = 0;
          const auto& writtenRegisters = PyInstruction_AsInstruction(self)->getWrittenRegisters();

          ret = xPyList_New(writtenRegisters.size());
          for (auto it = writtenRegisters.cbegin(); it != writtenRegisters.cend(); it++) {
            PyObject* item = xPyTuple_New(2);
            PyTuple_SetItem(item, 0, PyRegister(std::get<0>(*it)));
            PyTuple_SetItem(item, 1, PyAstNode(std::get<1>(*it)));
            PyList_SetItem(ret, index++, item);
          }

          return ret;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Instruction_isBranch(PyObject* self, PyObject* noarg) {
        try {
          if (PyInstruction_AsInstruction(self)->isBranch() == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Instruction_isConditionTaken(PyObject* self, PyObject* noarg) {
        try {
          if (PyInstruction_AsInstruction(self)->isConditionTaken() == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Instruction_isControlFlow(PyObject* self, PyObject* noarg) {
        try {
          if (PyInstruction_AsInstruction(self)->isControlFlow() == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Instruction_isMemoryRead(PyObject* self, PyObject* noarg) {
        try {
          if (PyInstruction_AsInstruction(self)->isMemoryRead() == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Instruction_isMemoryWrite(PyObject* self, PyObject* noarg) {
        try {
          if (PyInstruction_AsInstruction(self)->isMemoryWrite() == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Instruction_isPrefixed(PyObject* self, PyObject* noarg) {
        try {
          if (PyInstruction_AsInstruction(self)->isPrefixed() == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Instruction_isSymbolized(PyObject* self, PyObject* noarg) {
        try {
          if (PyInstruction_AsInstruction(self)->isSymbolized() == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Instruction_isTainted(PyObject* self, PyObject* noarg) {
        try {
          if (PyInstruction_AsInstruction(self)->isTainted() == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Instruction_setAddress(PyObject* self, PyObject* addr) {
        try {
          if (!PyLong_Check(addr) && !PyInt_Check(addr))
            return PyErr_Format(PyExc_TypeError, "Instruction::setAddress(): Expected an integer as argument.");
          PyInstruction_AsInstruction(self)->setAddress(PyLong_AsUint64(addr));
          Py_INCREF(Py_None);
          return Py_None;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Instruction_setOpcode(PyObject* self, PyObject* opc) {
        try {
          if (!PyBytes_Check(opc))
            return PyErr_Format(PyExc_TypeError, "Instruction::setOpcode(): Expected bytes as argument.");

          triton::uint8* opcode = reinterpret_cast<triton::uint8*>(PyBytes_AsString(opc));
          triton::uint32 size   = static_cast<triton::uint32>(PyBytes_Size(opc));

          PyInstruction_AsInstruction(self)->setOpcode(opcode, size);
          Py_INCREF(Py_None);
          return Py_None;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Instruction_setThreadId(PyObject* self, PyObject* tid) {
        try {
          if (!PyLong_Check(tid) && !PyInt_Check(tid))
            return PyErr_Format(PyExc_TypeError, "Instruction::setThreadId(): Expected an integer as argument.");

          PyInstruction_AsInstruction(self)->setThreadId(PyLong_AsUint32(tid));
          Py_INCREF(Py_None);
          return Py_None;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static int Instruction_print(PyObject* self) {
        std::cout << PyInstruction_AsInstruction(self);
        return 0;
      }


      static PyObject* Instruction_str(PyObject* self) {
        try {
          std::stringstream str;
          str << PyInstruction_AsInstruction(self);
          return PyString_FromFormat("%s", str.str().c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      //! Instruction methods.
      PyMethodDef Instruction_callbacks[] = {
        {"getAddress",                Instruction_getAddress,               METH_NOARGS,     ""},
        {"getDisassembly",            Instruction_getDisassembly,           METH_NOARGS,     ""},
        {"getLoadAccess",             Instruction_getLoadAccess,            METH_NOARGS,     ""},
        {"getNextAddress",            Instruction_getNextAddress,           METH_NOARGS,     ""},
        {"getOpcode",                 Instruction_getOpcode,                METH_NOARGS,     ""},
        {"getOperands",               Instruction_getOperands,              METH_NOARGS,     ""},
        {"getPrefix",                 Instruction_getPrefix,                METH_NOARGS,     ""},
        {"getReadImmediates",         Instruction_getReadImmediates,        METH_NOARGS,     ""},
        {"getReadRegisters",          Instruction_getReadRegisters,         METH_NOARGS,     ""},
        {"getSize",                   Instruction_getSize,                  METH_NOARGS,     ""},
        {"getStoreAccess",            Instruction_getStoreAccess,           METH_NOARGS,     ""},
        {"getSymbolicExpressions",    Instruction_getSymbolicExpressions,   METH_NOARGS,     ""},
        {"getThreadId",               Instruction_getThreadId,              METH_NOARGS,     ""},
        {"getType",                   Instruction_getType,                  METH_NOARGS,     ""},
        {"getWrittenRegisters",       Instruction_getWrittenRegisters,      METH_NOARGS,     ""},
        {"isBranch",                  Instruction_isBranch,                 METH_NOARGS,     ""},
        {"isConditionTaken",          Instruction_isConditionTaken,         METH_NOARGS,     ""},
        {"isControlFlow",             Instruction_isControlFlow,            METH_NOARGS,     ""},
        {"isMemoryRead",              Instruction_isMemoryRead,             METH_NOARGS,     ""},
        {"isMemoryWrite",             Instruction_isMemoryWrite,            METH_NOARGS,     ""},
        {"isPrefixed",                Instruction_isPrefixed,               METH_NOARGS,     ""},
        {"isSymbolized",              Instruction_isSymbolized,             METH_NOARGS,     ""},
        {"isTainted",                 Instruction_isTainted,                METH_NOARGS,     ""},
        {"setAddress",                Instruction_setAddress,               METH_O,          ""},
        {"setOpcode",                 Instruction_setOpcode,                METH_O,          ""},
        {"setThreadId",               Instruction_setThreadId,              METH_O,          ""},
        {nullptr,                     nullptr,                              0,               nullptr}
      };


      PyTypeObject Instruction_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "Instruction",                              /* tp_name */
        sizeof(Instruction_Object),                 /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)Instruction_dealloc,            /* tp_dealloc */
        (printfunc)Instruction_print,               /* tp_print */
        0,                                          /* tp_getattr */
        0,                                          /* tp_setattr */
        0,                                          /* tp_compare */
        0,                                          /* tp_repr */
        0,                                          /* tp_as_number */
        0,                                          /* tp_as_sequence */
        0,                                          /* tp_as_mapping */
        0,                                          /* tp_hash */
        0,                                          /* tp_call */
        (reprfunc)Instruction_str,                  /* tp_str */
        0,                                          /* tp_getattro */
        0,                                          /* tp_setattro */
        0,                                          /* tp_as_buffer */
        Py_TPFLAGS_DEFAULT,                         /* tp_flags */
        "Instruction objects",                      /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        Instruction_callbacks,                      /* tp_methods */
        0,                                          /* tp_members */
        0,                                          /* tp_getset */
        0,                                          /* tp_base */
        0,                                          /* tp_dict */
        0,                                          /* tp_descr_get */
        0,                                          /* tp_descr_set */
        0,                                          /* tp_dictoffset */
        0,                                          /* tp_init */
        0,                                          /* tp_alloc */
        0,                                          /* tp_new */
        0,                                          /* tp_free */
        0,                                          /* tp_is_gc */
        0,                                          /* tp_bases */
        0,                                          /* tp_mro */
        0,                                          /* tp_cache */
        0,                                          /* tp_subclasses */
        0,                                          /* tp_weaklist */
        0,                                          /* tp_del */
        0                                           /* tp_version_tag */
      };


      PyObject* PyInstruction(void) {
        Instruction_Object* object;

        PyType_Ready(&Instruction_Type);
        object = PyObject_NEW(Instruction_Object, &Instruction_Type);
        if (object != NULL)
          object->inst = new triton::arch::Instruction();

        return (PyObject*)object;
      }


      PyObject* PyInstruction(const triton::uint8* opcode, triton::uint32 opSize) {
        Instruction_Object* object;

        PyType_Ready(&Instruction_Type);
        object = PyObject_NEW(Instruction_Object, &Instruction_Type);
        if (object != NULL)
          object->inst = new triton::arch::Instruction(opcode, opSize);

        return (PyObject*)object;
      }


      PyObject* PyInstruction(const triton::arch::Instruction& inst) {
        Instruction_Object* object;

        PyType_Ready(&Instruction_Type);
        object = PyObject_NEW(Instruction_Object, &Instruction_Type);
        if (object != NULL)
          object->inst = new triton::arch::Instruction(inst);

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
