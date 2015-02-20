
#ifndef  __SMT2LIB_UTILS__
#define  __SMT2LIB_UTILS__

#include <sstream>
#include <cstdint>
#include <string>

namespace smt2lib {

  /* Returns the 'bv' syntax based on a value and a size. */
  std::string bv(uint64_t value, uint64_t size);

  /* Returns the 'bvadd' syntax. */
  std::string bvadd(std::string op1, std::string op2);

  /* Returns a sign extended version to size bits of the expression. */
  std::string sx(std::string expr, uint64_t size);

  /* Returns a zero extendend version to size bits of the expression. */
  std::string zx(std::string expr, uint64_t size);

  /* Returns the 'declare' syntax based on a value and a size. */
  std::string declare(uint64_t idSymVar, uint64_t BitVecSize);

  /* Returns the 'extract' syntax based on a value and a size. */
  std::string extractFromRegister(uint64_t regSize);

  /* Returns the 'assert' syntax. */
  std::string smtAssert(std::string expr);

  /* Returns the 'equal' syntax. */
  std::string equal(std::string op1, std::string op2);

  /* Returns the 'bvult' syntax. */
  std::string bvult(std::string op1, std::string op2);
}

#endif  /* !__SMTLIB2_UTILS__ */

