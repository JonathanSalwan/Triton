//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_STUBS_HPP
#define TRITON_STUBS_HPP

#include <map>
#include <vector>

#include <triton/tritonTypes.hpp>



namespace triton {
  namespace stubs {
    namespace x8664 {
      namespace systemv {
        namespace libc {
          /*! Symbols mapping. Each entry points on its position in `systemv::libc::code`. */
          extern std::map<std::string, triton::uint64> symbols;
          /*! Position independent code of some libc functions */
          extern std::vector<triton::uint8> code;
        };
      };
      namespace ms {
        namespace libc {
          /*! Symbols mapping. Each entry points on its position in `ms::libc::code`. */
          extern std::map<std::string, triton::uint64> symbols;
          /*! Position independent code of some libc functions */
          extern std::vector<triton::uint8> code;
        };
      };
    };
    namespace i386 {
      namespace systemv {
        namespace libc {
          /*! Symbols mapping. Each entry points on its position in `systemv::libc::code`. */
          extern std::map<std::string, triton::uint64> symbols;
          /*! Position independent code of some libc functions */
          extern std::vector<triton::uint8> code;
        };
      };
    };
    namespace aarch64 {
      namespace libc {
        /*! Symbols mapping. Each entry points on its position in `systemv::libc::code`. */
        extern std::map<std::string, triton::uint64> symbols;
        /*! Position independent code of some libc functions */
        extern std::vector<triton::uint8> code;
      };
    };
  };
};

#endif /* TRITON_STUBS_HPP */
