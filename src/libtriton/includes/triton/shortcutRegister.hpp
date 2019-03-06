//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_SHORTCUTREGISTER_HPP
#define TRITON_SHORTCUTREGISTER_HPP

#include <triton/archEnums.hpp>
#include <triton/exceptions.hpp>
#include <triton/register.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Triton namespace
  namespace arch {
  /*!
   *  \ingroup triton
   *  \addtogroup arch
   *  @{
   */

    /*! \class ShortcutRegister
     *  \brief This is used as a shortcut to access to registers */
    class ShortcutRegister {
      public:
        #define REG_SPEC(_0, LOWER_NAME, _2, _3, _4, _5, _6, _7, _8) \
        triton::arch::Register x86_##LOWER_NAME;
        #define REG_SPEC_NO_CAPSTONE REG_SPEC
        #include "triton/x86.spec"

        #define REG_SPEC(_0, LOWER_NAME, _2, _3, _4, _5) \
        triton::arch::Register aarch64_##LOWER_NAME;
        #define REG_SPEC_NO_CAPSTONE REG_SPEC
        #include "triton/aarch64.spec"

        /*! Constructor */
        ShortcutRegister() {};

        /*! Clears the shortcut */
        void clear(void) {
          #define REG_SPEC(_0, LOWER_NAME, _2, _3, _4, _5, _6, _7, _8) \
          this->x86_##LOWER_NAME = triton::arch::Register();
          #define REG_SPEC_NO_CAPSTONE REG_SPEC
          #include "triton/x86.spec"

          #define REG_SPEC(_0, LOWER_NAME, _2, _3, _4, _5) \
          this->aarch64_##LOWER_NAME = triton::arch::Register();
          #define REG_SPEC_NO_CAPSTONE REG_SPEC
          #include "triton/aarch64.spec"
        };

        /*! Inits the shortcut */
        void init(triton::arch::architecture_e arch) {
          this->clear();

          switch (arch) {
            case triton::arch::ARCH_AARCH64: {
              #define REG_SPEC(UPPER_NAME, LOWER_NAME, AARCH64_UPPER, AARCH64_LOWER, AARCH64_PARENT, MUTABLE)    \
              this->aarch64_##LOWER_NAME = triton::arch::Register(triton::arch::ID_REG_AARCH64_##UPPER_NAME,     \
                                                                  #LOWER_NAME,                                   \
                                                                  triton::arch::ID_REG_AARCH64_##AARCH64_PARENT, \
                                                                  AARCH64_UPPER,                                 \
                                                                  AARCH64_LOWER,                                 \
                                                                  MUTABLE);
              #define REG_SPEC_NO_CAPSTONE REG_SPEC
              #include "triton/aarch64.spec"
              }
              break;

            case triton::arch::ARCH_X86: {
              #define REG_SPEC(UPPER_NAME, LOWER_NAME, _1, _2, _3, X86_UPPER, X86_LOWER, X86_PARENT, X86_AVAIL) \
              if (X86_AVAIL)                                                                                    \
                this->x86_##LOWER_NAME = triton::arch::Register(triton::arch::ID_REG_X86_##UPPER_NAME,          \
                                                                #LOWER_NAME,                                    \
                                                                triton::arch::ID_REG_X86_##X86_PARENT,          \
                                                                X86_UPPER,                                      \
                                                                X86_LOWER,                                      \
                                                                true);
              #define REG_SPEC_NO_CAPSTONE REG_SPEC
              #include "triton/x86.spec"
              }
              break;

            case triton::arch::ARCH_X86_64: {
              #define REG_SPEC(UPPER_NAME, LOWER_NAME, X86_64_UPPER, X86_64_LOWER, X86_64_PARENT, X86_UPPER, X86_LOWER, X86_PARENT, X86_AVAIL)  \
              this->x86_##LOWER_NAME = triton::arch::Register(triton::arch::ID_REG_X86_##UPPER_NAME,                                            \
                                                              #LOWER_NAME,                                                                      \
                                                              triton::arch::ID_REG_X86_##X86_64_PARENT,                                         \
                                                              X86_64_UPPER,                                                                     \
                                                              X86_64_LOWER,                                                                     \
                                                              true);
              #define REG_SPEC_NO_CAPSTONE REG_SPEC
              #include "triton/x86.spec"
              }
              break;

            default:
              throw triton::exceptions::Architecture("ShortcutRegister::init(): Invalid architecture.");
          }
        };
    };

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SHORTCUTREGISTER_HPP */
