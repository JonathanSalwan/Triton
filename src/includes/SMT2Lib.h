
#ifndef  __SMT2LIB_UTILS__
#define  __SMT2LIB_UTILS__

#include <sstream>
#include <cstdint>
#include <string>


namespace smt2lib {

  /* Returns a string which defines the default logic and */
  /* utilies function used by the others functions (parity for example). */
  std::string init();

  /* Returns the 'bv' syntax based on a value and a size. */
  /* (_ bv<value> <size>) */
  std::string bv(uint64_t value, uint64_t regSize);

  /* Returns the 'bvadd' syntax. */
  /* (bvadd <op1> <op2>) */
  std::string bvadd(std::string op1, std::string op2);

  /* Returns a sign extended version to size bits of the expression. */
  std::string sx(std::string expr, uint64_t size);

  /* Returns a zero extendend version to size bits of the expression. */
  std::string zx(std::string expr, uint64_t size);

  /* Returns the 'declare' syntax based on a id symbolic variable and a bit victor. */
  std::string declare(uint64_t idSymVar, uint64_t BitVecSize);

  /* Returns the 'extract' syntax based on a reg size. */
  std::string extract(uint64_t regSize);

  /* Returns the 'extract' syntax based on a high and low bit. */
  /* (extract <high> <low>) */
  std::string extract(uint64_t high, uint64_t low);

  /* Returns the 'extract' syntax based on a high, low bit and an expression. */
  /* ((extract <high> <low>)<expr>) */
  std::string extract(uint64_t high, uint64_t low, std::string expr);

  /* Returns the 'assert' syntax. */
  std::string smtAssert(std::string expr);

  /* Returns the 'equal' syntax. */
  /* (= <op1> <op2>) */
  std::string equal(std::string op1, std::string op2);

  /* Returns the 'bvult' syntax. */
  /* (bvult <op1> <op2>) */
  std::string bvult(std::string op1, std::string op2);

  /* Returns the 'bvxor' syntax. */
  /* (bvxor <op1> <op2>) */
  std::string bvxor(std::string op1, std::string op2);

  /* Returns the 'bvand' syntax. */
  /* (bvand <op1> <op2>) */
  std::string bvand(std::string op1, std::string op2);

  /* Returns the 'bvnot' syntax. */
  /* (bvnot <op1>) */
  std::string bvnot(std::string op1);

 /* Return a call to the parity_flag function.
  * Returns the parity flag of one byte. If the number of bits set to 1 is even,
  * it returns (_ bv0 1) and (_ bv1 1) otherwise. */
  std::string parityFlag(std::string expr);
}

#endif  /* !__SMTLIB2_UTILS__ */

