
#ifndef  SMT2LIB_UTILS
#define  SMT2LIB_UTILS

#include <sstream>
#include "TritonTypes.h"
#include <string>
#include <vector>
#include <list>


namespace smt2lib {

  /* Returns a string which defines the default logic and */
  /* utilies function used by the others functions (parity for example). */
  std::string init();

  /* Returns the 'concat' syntax */
  /* (concat expr1 expr2) */
  std::string concat(std::string expr1, std::string expr2);
  std::string concat(std::vector<std::string> exprs);
  std::string concat(std::list<std::string> exprs);

  /* Returns the 'bv' syntax based on a value and a size. */
  /* (_ bv<value> <size>) */
  std::string bv(uint64 value, uint64 regSize);

  /* This is an alias on (_ bv1 1) */
  std::string bvtrue(void);

  /* This is an alias on (_ bv0 1) */
  std::string bvfalse(void);

  /* Returns the 'bvadd' syntax. */
  /* (bvadd <op1> <op2>) */
  std::string bvadd(std::string op1, std::string op2);

  /* Returns a sign extended version to size bits of the expression. */
  std::string sx(std::string expr, uint64 size);

  /* Returns a zero extendend version to size bits of the expression. */
  std::string zx(std::string expr, uint64 size);

  /* Returns the 'declare' syntax based on the symbolic variable name and its size. */
  std::string declare(std::string symVarName, uint64 symVarSize);

  /* Returns the 'extract' syntax based on a reg size. */
  std::string extract(uint64 regSize);

  /* Returns the 'extract' syntax based on a reg size. */
  std::string extract(uint64 regSize, std::string expr);

  /* Returns the 'extract' syntax based on a high and low bit. */
  /* (extract <high> <low>) */
  std::string extract(uint64 high, uint64 low);

  /* Returns the 'extract' syntax based on a high, low bit and an expression. */
  /* ((extract <high> <low>)<expr>) */
  std::string extract(uint64 high, uint64 low, std::string expr);

  /* Returns the 'assert' syntax. */
  std::string smtAssert(std::string expr);

  /* Returns the 'ite' syntax. */
  std::string ite(std::string expr, std::string thenExpr, std::string elseExpr);

  /* Returns the 'equal' syntax. */
  /* (= <op1> <op2>) */
  std::string equal(std::string op1, std::string op2);

  /* returns the 'bvsge' syntax. */
  /* (bvsge <op1> <op2>) */
  std::string bvsge(std::string op1, std::string op2);

  /* returns the 'bvsgt' syntax. */
  /* (bvsgt <op1> <op2>) */
  std::string bvsgt(std::string op1, std::string op2);

  /* returns the 'bvsle' syntax. */
  /* (bvsle <op1> <op2>) */
  std::string bvsle(std::string op1, std::string op2);

  /* returns the 'bvslt' syntax. */
  /* (bvslt <op1> <op2>) */
  std::string bvslt(std::string op1, std::string op2);

  /* returns the 'bvuge' syntax. */
  /* (bvuge <op1> <op2>) */
  std::string bvuge(std::string op1, std::string op2);

  /* returns the 'bvugt' syntax. */
  /* (bvugt <op1> <op2>) */
  std::string bvugt(std::string op1, std::string op2);

  /* returns the 'bvule' syntax. */
  /* (bvule <op1> <op2>) */
  std::string bvule(std::string op1, std::string op2);

  /* Returns the 'bvult' syntax. */
  /* (bvult <op1> <op2>) */
  std::string bvult(std::string op1, std::string op2);

  /* Returns the 'bvxor' syntax. */
  /* (bvxor <op1> <op2>) */
  std::string bvxor(std::string op1, std::string op2);

  /* Returns the 'bvor' syntax. */
  /* (bvor <op1> <op2>) */
  std::string bvor(std::string op1, std::string op2);

  /* Returns the 'bvror' syntax. */
  /* ((_ rotate_right <op2>) <op1>) */
  std::string bvror(std::string op1, std::string op2);

  /* Returns the 'bvrol' syntax. */
  /* ((_ rotate_left <op2>) <op1>) */
  std::string bvrol(std::string op1, std::string op2);

  /* returns the 'bvsub' syntax. */
  /* (bvsub <op1> <op2>) */
  std::string bvsub(std::string op1, std::string op2);

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

  /* Returns the simplify syntax */
  std::string simplify(std::string expr);

  /* Returns the display syntax */
  std::string display(std::string expr);

  /* Returns the 'bvneg' syntax */
  std::string bvneg(std::string expr);

  /* Returns the 'bvmul' syntax */
  std::string bvmul(std::string op1, std::string op2);

  /* Returns the 'bvurem' syntax - unsigned remainder */
  std::string bvurem(std::string op1, std::string op2);

  /* Returns the 'bvsrem' syntax - signed remainder */
  std::string bvsrem(std::string op1, std::string op2);

  /* Returns the 'bvsmod' syntax */
  std::string bvsmod(std::string op1, std::string op2);

  /* Returns the 'bvshl' syntax */
  std::string bvshl(std::string op1, std::string op2);

  /* Returns the 'bvlshr' syntax - unsigned (logical) shift right*/
  std::string bvlshr(std::string op1, std::string op2);

  /* Returns the 'bvashr' syntax - signed (arithmetical) shift right*/
  std::string bvashr(std::string op1, std::string op2);

  /* Returns the 'bvnand' syntax */
  std::string bvnand(std::string op1, std::string op2);

  /* Returns the 'bvnor' syntax */
  std::string bvnor(std::string op1, std::string op2);

  /* Returns the 'bvxnor' syntax */
  std::string bvxnor(std::string op1, std::string op2);

  /* Returns the 'bvudiv' syntax */
  std::string bvudiv(std::string op1, std::string op2);

  /* Returns the 'bvsdiv' syntax */
  std::string bvsdiv(std::string op1, std::string op2);
}

#endif  /* !SMTLIB2_UTILS */

