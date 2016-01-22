//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#include <api.hpp>
#include <pythonObjects.hpp>
#include <pythonUtils.hpp>
#include <pythonXFunctions.hpp>
#include <solverModel.hpp>



/*! \page py_SolverModel_page SolverModel
    \brief [**python api**] All information about the SolverModel python object.

\tableofcontents

\section py_SolverModel_description Description
<hr>

This object is used to represent a model from a SMT solver.

~~~~~~~~~~~~~{.py}
>>> from triton import *
>>> from smt2lib import *
>>>
>>> setArchitecture(ARCH.X86_64)
>>> inst = Instruction()
>>> inst.setOpcodes("\x48\x35\x44\x33\x22\x11") # xor rax, 0x11223344
>>>
>>> symvar = convertRegToSymVar(REG.RAX)
>>> print symvar
SymVar_0:64
>>>
>>> processing(inst)
>>> print inst
0: xor rax, 0x11223344
>>>
>>> raxAst = getFullAstFromId(getSymbolicRegisterId(REG.RAX))
>>> print raxAst
(bvxor ((_ extract 63 0) SymVar_0) (_ bv287454020 64))
>>>
>>> constraint = smtAssert(equal(raxAst, bv(0, raxAst.getBitvectorSize())))
>>> print constraint
(assert (= (bvxor ((_ extract 63 0) SymVar_0) (_ bv287454020 64)) (_ bv0 64)))
>>>
>>> model = getModel(constraint)
>>> print model
{0L: <SolverModel object at 0x7f30ac870b58>}
>>>
>>> symvarModel =  model[symvar.getId()] # Model from the symvar's id
>>> print symvarModel
SymVar_0 = 287454020
>>> hex(symvarModel.getValue())
'0x11223344L'
~~~~~~~~~~~~~

\section SolverModel_py_api Python API - Methods of the SolverModel class
<hr>

- **getId()**<br>
Returns the model's id. This id is the same that the variable id.

- **getName()**<br>
Returns the model's name. This name is the same that the variable name.

- **getValue()**<br>
Returns the model's value.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! SolverModel's Destructor.
      void SolverModel_dealloc(PyObject* self) {
        delete PySolverModel_AsSolverModel(self);
        Py_DECREF(self);
      }


      static PyObject* SolverModel_getId(PyObject* self, PyObject* noarg) {
        return Py_BuildValue("k", PySolverModel_AsSolverModel(self)->getId());
      }


      static PyObject* SolverModel_getName(PyObject* self, PyObject* noarg) {
        return Py_BuildValue("s", PySolverModel_AsSolverModel(self)->getName().c_str());
      }


      static PyObject* SolverModel_getValue(PyObject* self, PyObject* noarg) {
        return PyLong_FromUint512(PySolverModel_AsSolverModel(self)->getValue());
      }


      static PyObject* SolverModel_str(SolverModel_Object *obj) {
        std::stringstream str;
        str << *(obj->model);
        return PyString_FromFormat("%s", str.str().c_str());
      }


      //! SolverModel's methods.
      PyMethodDef SolverModel_callbacks[] = {
        {"getId",     SolverModel_getId,      METH_NOARGS,    ""},
        {"getName",   SolverModel_getName,    METH_NOARGS,    ""},
        {"getValue",  SolverModel_getValue,   METH_NOARGS,    ""},
        {nullptr,     nullptr,                0,              nullptr}
      };


      PyTypeObject SolverModel_Type = {
          PyObject_HEAD_INIT(&PyType_Type)
          0,                                          /* ob_size*/
          "SolverModel",                              /* tp_name*/
          sizeof(SolverModel_Object),                 /* tp_basicsize*/
          0,                                          /* tp_itemsize*/
          (destructor)SolverModel_dealloc,            /* tp_dealloc*/
          0,                                          /* tp_print*/
          0,                                          /* tp_getattr*/
          0,                                          /* tp_setattr*/
          0,                                          /* tp_compare*/
          0,                                          /* tp_repr*/
          0,                                          /* tp_as_number*/
          0,                                          /* tp_as_sequence*/
          0,                                          /* tp_as_mapping*/
          0,                                          /* tp_hash */
          0,                                          /* tp_call*/
          (reprfunc)SolverModel_str,                  /* tp_str*/
          0,                                          /* tp_getattro*/
          0,                                          /* tp_setattro*/
          0,                                          /* tp_as_buffer*/
          Py_TPFLAGS_DEFAULT,                         /* tp_flags*/
          "SolverModel objects",                      /* tp_doc */
          0,                                          /* tp_traverse */
          0,                                          /* tp_clear */
          0,                                          /* tp_richcompare */
          0,                                          /* tp_weaklistoffset */
          0,                                          /* tp_iter */
          0,                                          /* tp_iternext */
          SolverModel_callbacks,                      /* tp_methods */
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
      };


      PyObject* PySolverModel(triton::engines::solver::SolverModel &model) {
        SolverModel_Object *object;

        PyType_Ready(&SolverModel_Type);
        object = PyObject_NEW(SolverModel_Object, &SolverModel_Type);
        if (object != NULL)
          object->model = new triton::engines::solver::SolverModel(model);

        return (PyObject* )object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
