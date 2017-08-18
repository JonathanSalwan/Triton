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
#include <triton/covTag.hpp>


namespace triton {
  namespace bindings {
    namespace python {

      //! CovTag destructor.
      void CovTag_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyCovTag_AsCovTag(self);
        Py_DECREF(self);
      }


      static PyObject* CovTag_getAddress(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyCovTag_AsCovTag(self)->getAddress());
        } catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* CovTag_getTruthValue(PyObject* self, PyObject* noarg) {
        try {
          long truth = PyCovTag_AsCovTag(self)->getTruthValue() ? 1 : 0;
          return PyBool_FromLong(truth);
        } catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static int CovTag_print(PyObject* self) {
        std::cout << PyCovTag_AsCovTag(self);
        return 0;
      }


      static long CovTag_hash(PyObject* self) {
        return PyCovTag_AsCovTag(self)->getHash();
      }


      static PyObject* CovTag_str(PyObject* self) {
        try {
          std::stringstream str;
          str << PyCovTag_AsCovTag(self);
          return PyString_FromFormat("%s", str.str().c_str());
        } catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* CovTag_richcompare(PyObject* self, PyObject* other, int op) {
        PyObject* result    = nullptr;
        triton::uint64 id1  = 0;
        triton::uint64 id2  = 0;

        if (!PyCovTag_Check(other)) {
          result = Py_NotImplemented;
        }

        else {
          id1 = PyCovTag_AsCovTag(self)->getAddress();
          id2 = PyCovTag_AsCovTag(other)->getAddress();

          switch (op) {
            case Py_LT:
                result = (id1 <  id2) ? Py_True : Py_False;
                break;
            case Py_LE:
                result = (id1 <= id2) ? Py_True : Py_False;
                break;
            case Py_EQ:
                result = (id1 == id2) ? Py_True : Py_False;
                break;
            case Py_NE:
                result = (id1 != id2) ? Py_True : Py_False;
                break;
            case Py_GT:
                result = (id1 >  id2) ? Py_True : Py_False;
                break;
            case Py_GE:
                result = (id1 >= id2) ? Py_True : Py_False;
                break;
          }
        }

        Py_INCREF(result);
        return result;
      }


      //! CovTag methods.
      PyMethodDef CovTag_callbacks[] = {
        {"getAddress",        CovTag_getAddress,         METH_NOARGS,    ""},
        {"getTruthValue",     CovTag_getTruthValue,      METH_NOARGS,    ""},
        {nullptr,             nullptr,                   0,              nullptr}
      };


      PyTypeObject CovTag_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "CovTag",                                   /* tp_name */
        sizeof(CovTag_Object),                      /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)CovTag_dealloc,                 /* tp_dealloc */
        (printfunc)CovTag_print,                    /* tp_print */
        0,                                          /* tp_getattr */
        0,                                          /* tp_setattr */
        0,                                          /* tp_compare */
        0,                                          /* tp_repr */
        0,                                          /* tp_as_number */
        0,                                          /* tp_as_sequence */
        0,                                          /* tp_as_mapping */
        (hashfunc)CovTag_hash,                      /* tp_hash */
        0,                                          /* tp_call */
        (reprfunc)CovTag_str,                       /* tp_str */
        0,                                          /* tp_getattro */
        0,                                          /* tp_setattro */
        0,                                          /* tp_as_buffer */
        Py_TPFLAGS_DEFAULT,                         /* tp_flags */
        "CovTag objects",                           /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        (richcmpfunc)CovTag_richcompare,            /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        CovTag_callbacks,                           /* tp_methods */
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


      PyObject* PyCovTag(const triton::engines::taint::CovTag& tag) {
        CovTag_Object* object;

        PyType_Ready(&CovTag_Type);
        object = PyObject_NEW(CovTag_Object, &CovTag_Type);
        if (object != NULL)
          object->tag = new triton::engines::taint::CovTag(tag);

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
