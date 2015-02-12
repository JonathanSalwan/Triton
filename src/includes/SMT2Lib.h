
#ifndef  __SMT2LIB_UTILS__
#define  __SMT2LIB_UTILS__

#include <sstream>
#include <cstdint>
#include <string>

namespace smt2lib {
  std::string bv(uint64_t value, uint64_t size);
  std::string declare(uint64_t idSymVar, uint64_t BitVecSize);
  std::string extract(uint64_t regSize);
}

#endif  /* !__SMTLIB2_UTILS__ */

