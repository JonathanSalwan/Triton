//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/exceptions.hpp>
#include <triton/pathConstraint.hpp>
#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>



/*! \page py_PathConstraint_page PathConstraint
    \brief [**python api**] All information about the PathConstraint python object.

\tableofcontents

\section py_PathConstraint_description Description
<hr>

This object is used to represent a path constraint.

~~~~~~~~~~~~~{.py}
>>> pcl = getPathConstraints()
>>> for pc in pcl:
...     if pc.isMultipleBranches():
...         b1   =  pc.getBranchConstraints()[0]['constraint']
...         b2   =  pc.getBranchConstraints()[1]['constraint']
...
...         print 'Constraint branch 1:', b1
...         print 'Constraint branch 2:', b2
...
...         seed = list()
...
...         # Branch 1, we assume that the path constraint contains a symbolic variable
...         models  = getModel(assert_(b1))
...         for k, v in models.items():
...             seed.append(v)
...
...         # Branch 2, we assume that the path constraint contains a symbolic variable.
...         models  = getModel(assert_(b2))
...         for k, v in models.items():
...             seed.append(v)
...
...         if seed:
...             print 'B1: %s (%c)  |  B2: %s (%c)' %(seed[0], chr(seed[0].getValue()), seed[1], chr(seed[1].getValue())
...
Constraint branch 1: (not (= (ite (= ((_ extract 0 0) ref!179) (_ bv1 1)) (_ bv4195769 64) (_ bv4195762 64)) (_ bv4195762 64)))
Constraint branch 2: (= (ite (= ((_ extract 0 0) ref!179) (_ bv1 1)) (_ bv4195769 64) (_ bv4195762 64)) (_ bv4195762 64))
B1: SymVar_0 = 65 (e)  |  B2: SymVar_0 = 0 ()
[...]
>>>
~~~~~~~~~~~~~

\section PathConstraint_py_api Python API - Methods of the PathConstraint class
<hr>

- <b>dict getBranchConstraints(void)</b><br>
Returns the branch constraints as list of dictionary `{isTaken, srcAddr, dstAddr, constraint}`. The source address is the location
of the branch instruction and the destination address is the destination of the jump. E.g: `"0x11223344: jne 0x55667788"`, 0x11223344
is the source address and 0x55667788 is the destination if and only if the branch is taken, otherwise the destination is the next
instruction address.

- <b>integer getTakenAddress(void)</b><br>
Returns the address of the taken branch.

- <b>\ref py_AstNode_page getTakenPathConstraintAst(void)</b><br>
Returns the path constraint AST of the taken branch.

- <b>bool isMultipleBranches(void)</b><br>
Returns true if it is not a direct jump.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! PathConstraint destructor.
      void PathConstraint_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyPathConstraint_AsPathConstraint(self);
        Py_DECREF(self);
      }


      static PyObject* PathConstraint_getBranchConstraints(PyObject* self, PyObject* noarg) {
        try {
          PyObject* ret = nullptr;
          const auto& branches = PyPathConstraint_AsPathConstraint(self)->getBranchConstraints();

          ret = xPyList_New(branches.size());
          for (triton::usize index = 0; index != branches.size(); index++) {
            PyObject* dict = xPyDict_New();
            PyDict_SetItem(dict, PyString_FromString("isTaken"),    PyBool_FromLong(std::get<0>(branches[index])));
            PyDict_SetItem(dict, PyString_FromString("srcAddr"),    PyLong_FromUint64(std::get<1>(branches[index])));
            PyDict_SetItem(dict, PyString_FromString("dstAddr"),    PyLong_FromUint64(std::get<2>(branches[index])));
            PyDict_SetItem(dict, PyString_FromString("constraint"), PyAstNode(std::get<3>(branches[index])));
            PyList_SetItem(ret, index, dict);
          }

          return ret;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* PathConstraint_getTakenAddress(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyPathConstraint_AsPathConstraint(self)->getTakenAddress());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* PathConstraint_getTakenPathConstraintAst(PyObject* self, PyObject* noarg) {
        try {
          return PyAstNode(PyPathConstraint_AsPathConstraint(self)->getTakenPathConstraintAst());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* PathConstraint_isMultipleBranches(PyObject* self, PyObject* noarg) {
        try {
          if (PyPathConstraint_AsPathConstraint(self)->isMultipleBranches())
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      //! PathConstraint methods.
      PyMethodDef PathConstraint_callbacks[] = {
        {"getBranchConstraints",        PathConstraint_getBranchConstraints,      METH_NOARGS,    ""},
        {"getTakenAddress",             PathConstraint_getTakenAddress,           METH_NOARGS,    ""},
        {"getTakenPathConstraintAst",   PathConstraint_getTakenPathConstraintAst, METH_NOARGS,    ""},
        {"isMultipleBranches",          PathConstraint_isMultipleBranches,        METH_NOARGS,    ""},
        {nullptr,                       nullptr,                                  0,              nullptr}
      };


      PyTypeObject PathConstraint_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "PathConstraint",                           /* tp_name */
        sizeof(PathConstraint_Object),              /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)PathConstraint_dealloc,         /* tp_dealloc */
        0,                                          /* tp_print */
        0,                                          /* tp_getattr */
        0,                                          /* tp_setattr */
        0,                                          /* tp_compare */
        0,                                          /* tp_repr */
        0,                                          /* tp_as_number */
        0,                                          /* tp_as_sequence */
        0,                                          /* tp_as_mapping */
        0,                                          /* tp_hash */
        0,                                          /* tp_call */
        0,                                          /* tp_str */
        0,                                          /* tp_getattro */
        0,                                          /* tp_setattro */
        0,                                          /* tp_as_buffer */
        Py_TPFLAGS_DEFAULT,                         /* tp_flags */
        "PathConstraint objects",                   /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        PathConstraint_callbacks,                   /* tp_methods */
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


      PyObject* PyPathConstraint(const triton::engines::symbolic::PathConstraint& pc) {
        PathConstraint_Object* object;

        PyType_Ready(&PathConstraint_Type);
        object = PyObject_NEW(PathConstraint_Object, &PathConstraint_Type);
        if (object != NULL)
          object->pc = new triton::engines::symbolic::PathConstraint(pc);

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
