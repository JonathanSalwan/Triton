/* @file
 *
 *  Copyright (C) - Triton
 *
 *  This program is under the terms of the BSD License.
 */

#include <triton/architecture.hpp>
#include <triton/cpuSize.hpp>
#include <triton/exceptions.hpp>
#include <triton/externalLibs.hpp>
#include <triton/armv7Specifications.hpp>

namespace triton {
  namespace arch {
    namespace armv7 {

      armv7Specifications::armv7Specifications(triton::arch::architectures_e arch) {
        if (arch != triton::arch::ARCH_ARMV7M && arch != triton::arch::ARCH_ARMV7AR)
          throw triton::exceptions::Architecture("armv7mSpecifications::armv7mSpecifications(): Invalid architecture.");

        if (arch == triton::arch::ARCH_ARMV7AR) {
        //Fill registers with those available in armv7
            #define REG_SPEC(UPPER_NAME, LOWER_NAME, ARCH, ARMV7AR_UPPER, ARMV7AR_LOWER, ARMV7AR_PARENT, ARMV7M_UPPER, ARMV7M_LOWER, ARMV7M_PARENT, ARMV7M_AVAIL)       \
            registers_.emplace(ID_REG_##ARCH##_##UPPER_NAME,                                                                                                            \
                               triton::arch::Register(triton::arch::ID_REG_##ARCH##_##UPPER_NAME,                                                                       \
                                                      #LOWER_NAME,                                                                                                      \
                                                      triton::arch::ID_REG_##ARCH##_##ARMV7AR_PARENT,                                                                   \
                                                      ARMV7AR_UPPER,                                                                                                    \
                                                      ARMV7AR_LOWER)                                                                                                    \
                              );
          // Handle register not available in capstone as normal registers
          #define REG_SPEC_NO_CAPSTONE REG_SPEC
          #include "triton/armv7.spec"
        }
        else {
          assert(arch == triton::arch::ARCH_ARMV7M);
          // Fill registers_ with those available in ARMV7M from spec
          #define REG_SPEC(UPPER_NAME, LOWER_NAME, ARCH, ARMV7AR_UPPER, ARMV7AR_LOWER, ARMV7AR_PARENT, ARMV7M_UPPER, ARMV7M_LOWER, ARMV7M_PARENT, ARMV7M_AVAIL)         \
          if (ARMV7M_AVAIL)                                                                                                                                             \
            registers_.emplace(ID_REG_##ARCH##_##UPPER_NAME,                                                                                                            \
                               triton::arch::Register(triton::arch::ID_REG_##ARCH##_##UPPER_NAME,                                                                       \
                                                      #LOWER_NAME,                                                                                                      \
                                                      triton::arch::ID_REG_##ARCH##_##ARMV7M_PARENT,                                                                    \
                                                      ARMV7M_UPPER,                                                                                                     \
                                                      ARMV7M_LOWER)                                                                                                     \
                              );
          // Handle register not available in capstone as normal registers
          #define REG_SPEC_NO_CAPSTONE REG_SPEC
          #include "triton/armv7.spec"
        }
      }
    }
  }
}
