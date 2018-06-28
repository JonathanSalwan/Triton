//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/api.hpp>
#include <triton/callbacks.hpp>
#include <triton/exceptions.hpp>



namespace triton {
  namespace callbacks {

    Callbacks::Callbacks(triton::API& api) : api(api) {
      this->isDefined = false;
    }


    void Callbacks::addCallback(triton::callbacks::getConcreteMemoryValueCallback cb) {
      this->getConcreteMemoryValueCallbacks.push_back(cb);
      this->isDefined = true;
    }


    void Callbacks::addCallback(triton::callbacks::getConcreteRegisterValueCallback cb) {
      this->getConcreteRegisterValueCallbacks.push_back(cb);
      this->isDefined = true;
    }


    void Callbacks::addCallback(triton::callbacks::setConcreteMemoryValueCallback cb) {
      this->setConcreteMemoryValueCallbacks.push_back(cb);
      this->isDefined = true;
    }


    void Callbacks::addCallback(triton::callbacks::setConcreteRegisterValueCallback cb) {
      this->setConcreteRegisterValueCallbacks.push_back(cb);
      this->isDefined = true;
    }


    void Callbacks::addCallback(triton::callbacks::symbolicSimplificationCallback cb) {
      this->symbolicSimplificationCallbacks.push_back(cb);
      this->isDefined = true;
    }


    void Callbacks::removeAllCallbacks(void) {
      this->getConcreteMemoryValueCallbacks.clear();
      this->getConcreteRegisterValueCallbacks.clear();
      this->setConcreteMemoryValueCallbacks.clear();
      this->setConcreteRegisterValueCallbacks.clear();
      this->symbolicSimplificationCallbacks.clear();
    }


    void Callbacks::removeCallback(triton::callbacks::getConcreteMemoryValueCallback cb) {
      this->getConcreteMemoryValueCallbacks.remove(cb);
      if (this->countCallbacks() == 0)
        this->isDefined = false;
    }


    void Callbacks::removeCallback(triton::callbacks::getConcreteRegisterValueCallback cb) {
      this->getConcreteRegisterValueCallbacks.remove(cb);
      if (this->countCallbacks() == 0)
        this->isDefined = false;
    }


    void Callbacks::removeCallback(triton::callbacks::setConcreteMemoryValueCallback cb) {
      this->setConcreteMemoryValueCallbacks.remove(cb);
      if (this->countCallbacks() == 0)
        this->isDefined = false;
    }


    void Callbacks::removeCallback(triton::callbacks::setConcreteRegisterValueCallback cb) {
      this->setConcreteRegisterValueCallbacks.remove(cb);
      if (this->countCallbacks() == 0)
        this->isDefined = false;
    }


    void Callbacks::removeCallback(triton::callbacks::symbolicSimplificationCallback cb) {
      this->symbolicSimplificationCallbacks.remove(cb);
      if (this->countCallbacks() == 0)
        this->isDefined = false;
    }


    triton::ast::SharedAbstractNode Callbacks::processCallbacks(triton::callbacks::callback_e kind, triton::ast::SharedAbstractNode node) const {
      switch (kind) {
        case triton::callbacks::SYMBOLIC_SIMPLIFICATION: {
          for (auto& function: this->symbolicSimplificationCallbacks) {
            // Reinject node in next callback
            node = function(this->api, node);
            if (node == nullptr)
              throw triton::exceptions::Callbacks("Callbacks::processCallbacks(SYMBOLIC_SIMPLIFICATION): You cannot return a nullptr node.");
          }
          break;
        }
        default:
          throw triton::exceptions::Callbacks("Callbacks::processCallbacks(): Invalid kind of callback for this C++ polymorphism.");
      };

      return node;
    }


    void Callbacks::processCallbacks(triton::callbacks::callback_e kind, const triton::arch::MemoryAccess& mem) const {
      switch (kind) {
        case triton::callbacks::GET_CONCRETE_MEMORY_VALUE: {
           for (auto& function: this->getConcreteMemoryValueCallbacks) {
             function(this->api, mem);
             if (mem.getLeaAst() != nullptr)
                 this->api.getSymbolicEngine()->initLeaAst(const_cast<triton::arch::MemoryAccess&>(mem), true);
           }
          break;
        }

        default:
          throw triton::exceptions::Callbacks("Callbacks::processCallbacks(): Invalid kind of callback for this C++ polymorphism.");
      };
    }


    void Callbacks::processCallbacks(triton::callbacks::callback_e kind, const triton::arch::Register& reg) const {
      switch (kind) {
        case triton::callbacks::GET_CONCRETE_REGISTER_VALUE: {
           for (auto& function: this->getConcreteRegisterValueCallbacks) {
             function(this->api, reg);
           }
          break;
        }

        default:
          throw triton::exceptions::Callbacks("Callbacks::processCallbacks(): Invalid kind of callback for this C++ polymorphism.");
      };
    }


    void Callbacks::processCallbacks(triton::callbacks::callback_e kind, const triton::arch::MemoryAccess& mem, const triton::uint512& value) const {
      switch (kind) {
        case triton::callbacks::SET_CONCRETE_MEMORY_VALUE: {
           for (auto& function: this->setConcreteMemoryValueCallbacks) {
             function(this->api, mem, value);
           }
          break;
        }

        default:
          throw triton::exceptions::Callbacks("Callbacks::processCallbacks(): Invalid kind of callback for this C++ polymorphism.");
      };
    }


    void Callbacks::processCallbacks(triton::callbacks::callback_e kind, const triton::arch::Register& reg, const triton::uint512& value) const {
      switch (kind) {
        case triton::callbacks::SET_CONCRETE_REGISTER_VALUE: {
           for (auto& function: this->setConcreteRegisterValueCallbacks) {
             function(this->api, reg, value);
           }
          break;
        }

        default:
          throw triton::exceptions::Callbacks("Callbacks::processCallbacks(): Invalid kind of callback for this C++ polymorphism.");
      };
    }


    triton::usize Callbacks::countCallbacks(void) const {
      triton::usize count = 0;

      count += this->getConcreteMemoryValueCallbacks.size();
      count += this->getConcreteRegisterValueCallbacks.size();
      count += this->setConcreteMemoryValueCallbacks.size();
      count += this->setConcreteRegisterValueCallbacks.size();
      count += this->symbolicSimplificationCallbacks.size();

      return count;
    }

  }; /* callbacks namespace */
}; /* triton namespace */
