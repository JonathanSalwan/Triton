//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/callbacks.hpp>
#include <triton/exceptions.hpp>


namespace triton {
  namespace callbacks {

    Callbacks::Callbacks() {
      this->isDefined = false;
    }


    Callbacks::Callbacks(const Callbacks& copy) {
      this->getConcreteMemoryValueCallbacks     = copy.getConcreteMemoryValueCallbacks;
      this->getConcreteRegisterValueCallbacks   = copy.getConcreteRegisterValueCallbacks;
      this->symbolicSimplificationCallbacks     = copy.symbolicSimplificationCallbacks;
      this->isDefined                           = copy.isDefined;
    }


    Callbacks::~Callbacks() {
    }


    void Callbacks::operator=(const Callbacks& copy) {
      this->getConcreteMemoryValueCallbacks     = copy.getConcreteMemoryValueCallbacks;
      this->getConcreteRegisterValueCallbacks   = copy.getConcreteRegisterValueCallbacks;
      this->symbolicSimplificationCallbacks     = copy.symbolicSimplificationCallbacks;
      this->isDefined                           = copy.isDefined;
    }


    void Callbacks::addCallback(triton::callbacks::getConcreteMemoryValueCallback cb) {
      this->getConcreteMemoryValueCallbacks.push_back(cb);
      this->isDefined = true;
    }


    void Callbacks::addCallback(triton::callbacks::getConcreteRegisterValueCallback cb) {
      this->getConcreteRegisterValueCallbacks.push_back(cb);
      this->isDefined = true;
    }


    void Callbacks::addCallback(triton::callbacks::symbolicSimplificationCallback cb) {
      this->symbolicSimplificationCallbacks.push_back(cb);
      this->isDefined = true;
    }


    void Callbacks::removeAllCallbacks(void) {
      this->getConcreteMemoryValueCallbacks.clear();
      this->getConcreteRegisterValueCallbacks.clear();
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


    void Callbacks::removeCallback(triton::callbacks::symbolicSimplificationCallback cb) {
      this->symbolicSimplificationCallbacks.remove(cb);
      if (this->countCallbacks() == 0)
        this->isDefined = false;
    }


    triton::ast::AbstractNode* Callbacks::processCallbacks(triton::callbacks::callback_e kind, triton::ast::AbstractNode* node) const {
      // FIXME : Most of callback node are ignored. May be we should return a list of nodes?
      switch (kind) {
        case triton::callbacks::SYMBOLIC_SIMPLIFICATION: {
          for (auto& function: this->symbolicSimplificationCallbacks) {
            node = function(node);
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
           for(auto& function: this->getConcreteMemoryValueCallbacks) {
             // FIXME Const_cast is certainly bad
             function(const_cast<triton::arch::MemoryAccess&>(mem));
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
           for(auto& function: this->getConcreteRegisterValueCallbacks) {
             // FIXME Const_cast is certainly bad
             function(const_cast<triton::arch::Register&>(reg));
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
      count += this->symbolicSimplificationCallbacks.size();

      return count;
    }

  }; /* callbacks namespace */
}; /* triton namespace */
