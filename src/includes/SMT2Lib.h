
#ifndef  __SMT2LIB_UTILS__
#define  __SMT2LIB_UTILS__

#include <sstream>
#include <cstdint>
#include <string>

namespace smt2lib {
  /* Returns the 'bv' syntax based on a value and a size. */
  std::string bv(uint64_t value, uint64_t size);

  /* Returns a sign extended version to size bits of the expression. */
  std::string sx(std::string expr, uint64_t size);

  /* Returns a zero extendend version to size bits of the expression. */
  std::string zx(std::string expr, uint64_t size);

  /* Returns the 'extract' syntax based on a value and a size. */
  std::string declare(uint64_t idSymVar, uint64_t BitVecSize);

  /* Returns the 'declare' syntax based on a value and a size. */
  std::string extract(uint64_t regSize);
}

#endif  /* !__SMTLIB2_UTILS__ */

