#include <string>
#include <stdexcept>

#include <CpuSize.h>
#include <SMT2Lib.h>


static const std::string parityDef =
  "(define-fun parity_flag ((x!1 (_ BitVec 8))) (_ BitVec 1) "
  "((_ extract 0 0) "
    "(bvlshr "
       "(_ bv27030 16) "
       "((_ zero_extend 8) "
        "(bvand "
          "(bvxor "
            "x!1 "
            "(bvlshr x!1 (_ bv4 8))) "
          "(_ bv15 8))))))";


std::string smt2lib::init()
{
  return "(set-logic QF_AUFBV)\n" + parityDef + "\n";
}


/* Returns the 'concat' syntax. */
std::string smt2lib::concat(std::string expr1, std::string expr2)
{
  return "(concat " + expr1 + " " + expr2 + ")";
}


/* Returns the 'concat' syntax. */
std::string smt2lib::concat(std::vector<std::string> exprs)
{
  std::stringstream   expr;
  uint64            index;

  if (exprs.size() <= 1)
    throw std::runtime_error("Error: smt2lib::concat invalid vector size");

  index = 0;
  expr << "(concat";
  while (index != exprs.size()){
    expr << " " << exprs[index];
    index++;
  }
  expr << ")";

  return expr.str();
}


/* Returns the 'concat' syntax. */
std::string smt2lib::concat(std::list<std::string> exprs)
{
  std::list<std::string>::const_iterator it;
  std::stringstream                      expr;

  if (exprs.size() <= 1)
    throw std::runtime_error("Error: smt2lib::concat invalid list size");

  expr << "(concat";
  for (it = exprs.begin(); it != exprs.end(); it++)
    expr << " " << *it;
  expr << ")";

  return expr.str();
}


/* Returns the 'bv' syntax based on a value and a size.
 * Mainly used for the SMT translation */
std::string smt2lib::bv(uint64 value, uint64 size)
{
  return "(_ bv" + std::to_string(value) + " " + std::to_string(size) + ")";
}


/* Returns the 'bv' syntax with sign extension applied to it. */
std::string smt2lib::sx(std::string expr, uint64 size)
{
  return "((_ sign_extend " + std::to_string(size) + ") " + expr + ")";
}


/* Returns the 'bv' syntax with zero extension applied to it. */
std::string smt2lib::zx(std::string expr, uint64 size)
{
  return "((_ zero_extend " + std::to_string(size) + ") " + expr + ")";;
}


/* Returns the 'bvadd' syntax. */
std::string smt2lib::bvadd(std::string op1, std::string op2)
{
  return "(bvadd " + op1 + " " + op2 + ")";
}


/* Returns the 'bvxor' syntax. */
std::string smt2lib::bvxor(std::string op1, std::string op2)
{
  return "(bvxor " + op1 + " " + op2 + ")";
}


/* Returns the 'bvsub' syntax. */
std::string smt2lib::bvsub(std::string op1, std::string op2)
{
  return "(bvsub " + op1 + " " + op2 + ")";
}


/* Returns the 'bvand' syntax. */
std::string smt2lib::bvand(std::string op1, std::string op2)
{
  return "(bvand " + op1 + " " + op2 + ")";
}


/* Returns the 'bvor' syntax. */
std::string smt2lib::bvor(std::string op1, std::string op2)
{
  return "(bvor " + op1 + " " + op2 + ")";
}


/* Returns the 'bvror' syntax. */
/* op2 must be a concretization constant */
std::string smt2lib::bvror(std::string op1, std::string op2)
{
  /* Check if op1 is a concretization constant */
  std::string::const_iterator it = op2.begin();
  while (it != op2.end()) {
    if (std::isdigit(*it) == false)
      throw std::runtime_error("Error: invalid smt2lib::ror - op2 must be a concretization constant");
    it++;
  }

  return "((_ rotate_right " + op2 + ") " + op1 + ")";
}


/* Returns the 'bvrol' syntax. */
/* op2 must be a concretization constant */
std::string smt2lib::bvrol(std::string op1, std::string op2)
{
  /* Check if op1 is a concretization constant */
  std::string::const_iterator it = op2.begin();
  while (it != op2.end()) {
    if (std::isdigit(*it) == false)
      throw std::runtime_error("Error: invalid smt2lib::rol - op2 must be a concretization constant");
    it++;
  }

  return "((_ rotate_left " + op2 + ") " + op1 + ")";
}


/* Returns the 'bvnot' syntax. */
std::string smt2lib::bvnot(std::string op1)
{
  return "(bvnot " + op1 + ")";
}


/*
 * Returns the 'bvsge' syntax.
 * bvsge: signed greater or equal
 */
std::string smt2lib::bvsge(std::string op1, std::string op2)
{
  return "(bvsge " + op1 + " " + op2 + ")";
}


/*
 * Returns the 'bvsgt' syntax.
 * bvsgt: signed greater than
 */
std::string smt2lib::bvsgt(std::string op1, std::string op2)
{
  return "(bvsgt " + op1 + " " + op2 + ")";
}


/*
 * Returns the 'bvsle' syntax.
 * bvsle: signed less or equal
 */
std::string smt2lib::bvsle(std::string op1, std::string op2)
{
  return "(bvsle " + op1 + " " + op2 + ")";
}


/*
 * Returns the 'bvslt' syntax.
 * bvsle: signed less than
 */
std::string smt2lib::bvslt(std::string op1, std::string op2)
{
  return "(bvslt " + op1 + " " + op2 + ")";
}


/*
 * Returns the 'bvuge' syntax.
 * bvuge: unsigned greater or equal
 */
std::string smt2lib::bvuge(std::string op1, std::string op2)
{
  return "(bvuge " + op1 + " " + op2 + ")";
}


/*
 * Returns the 'bvugt' syntax.
 * bvugt: unsigned greater than
 */
std::string smt2lib::bvugt(std::string op1, std::string op2)
{
  return "(bvugt " + op1 + " " + op2 + ")";
}


/*
 * Returns the 'bvule' syntax.
 * bvule: unsigned less or equal
 */
std::string smt2lib::bvule(std::string op1, std::string op2)
{
  return "(bvule " + op1 + " " + op2 + ")";
}


/*
 * Returns the 'bvult' syntax.
 * bvult: unsigned less than
 */
std::string smt2lib::bvult(std::string op1, std::string op2)
{
  return "(bvult " + op1 + " " + op2 + ")";
}


/* Returns the 'extract' syntax based on a regSize.
 * Mainly used for the SMT translation */
std::string smt2lib::extract(uint64 regSize)
{
  std::stringstream stream;

  switch(regSize){
    case BYTE_SIZE:
      stream << "(_ extract 7 0)";
      break;
    case WORD_SIZE:
      stream << "(_ extract 15 0)";
      break;
    case DWORD_SIZE:
      stream << "(_ extract 31 0)";
      break;
    case QWORD_SIZE:
      stream << "(_ extract 63 0)";
      break;
    case DQWORD_SIZE:
      stream << "(_ extract 127 0)";
      break;
    default:
      throw std::runtime_error("Error: invalid smt2lib::extract regSize");
  }

  return stream.str();
}


/* Returns the 'extract' syntax based on a regSize and expression */
std::string smt2lib::extract(uint64 regSize, std::string expr)
{
  return "(" + smt2lib::extract(regSize) + " " + expr + ")";
}


/* Returns the 'extract' syntax. */
std::string smt2lib::extract(uint64 high, uint64 low)
{
  return "(_ extract " + std::to_string(high) + " " + std::to_string(low) + ")";
}


/* Returns the 'extract' syntax. */
std::string smt2lib::extract(uint64 high, uint64 low, std::string expr)
{
  return "(" + smt2lib::extract(high, low) + " " + expr + ")";
}


/* Returns the 'declare' syntax is symbolic variable and a bit vector.
 * Mainly used for the SMT translation */
std::string smt2lib::declare(std::string symVarName, uint64 symVarSize)
{
  std::stringstream stream;

  switch(symVarSize){
    case BYTE_SIZE:
      stream << "(declare-fun " << symVarName << " () (_ BitVec 8))";
      break;
    case WORD_SIZE:
      stream << "(declare-fun " << symVarName << " () (_ BitVec 16))";
      break;
    case DWORD_SIZE:
      stream << "(declare-fun " << symVarName << " () (_ BitVec 32))";
      break;
    case QWORD_SIZE:
      stream << "(declare-fun " << symVarName << " () (_ BitVec 64))";
      break;
    case DQWORD_SIZE:
      stream << "(declare-fun " << symVarName << " () (_ BitVec 128))";
      break;
  }

  return stream.str();
}


/* Returns the 'assert' syntax. */
std::string smt2lib::smtAssert(std::string expr)
{
  return "(assert " + expr + ")";
}


/* Returns the 'ite' syntax. */
std::string smt2lib::ite(std::string expr, std::string thenExpr, std::string elseExpr)
{
  return "(ite " + expr + " " + thenExpr + " " + elseExpr + ")";
}


/* Returns the 'equal' syntax. */
std::string smt2lib::equal(std::string op1, std::string op2)
{
  return "(= " + op1 + " " + op2 + ")";
}


/* Returns a call to the parity function.
 * Returns the parity flag of one byte. If the number of bits set to 1 is even,
 * it returns (_ bv0 1) and (_ bv1 1) otherwise. */
std::string smt2lib::parityFlag(std::string expr)
{
  return "(parity_flag " + expr + ")";
}


/* This is an alias on (_ bv1 1) */
std::string smt2lib::bvtrue(void)
{
  return smt2lib::bv(1, 1);
}


/* This is an alias on (_ bv0 1) */
std::string smt2lib::bvfalse(void)
{
  return smt2lib::bv(0, 1);
}


/* Returns the simplify syntax */
std::string smt2lib::simplify(std::string expr)
{
  return "(simplify " + expr + ")";
}


/* Returns the display syntax */
std::string smt2lib::display(std::string expr)
{
  return "(display " + expr + ")";
}


/* Returns the 'bvneg' syntax */
std::string smt2lib::bvneg(std::string expr)
{
  return "(bvneg " + expr + ")";
}


/* Returns the 'bvmul' syntax */
std::string smt2lib::bvmul(std::string op1, std::string op2)
{
  return "(bvmul " + op1 + " " + op2 + ")";
}


/* Returns the 'bvurem' syntax - unsigned remainder */
std::string smt2lib::bvurem(std::string op1, std::string op2)
{
  return "(bvurem " + op1 + " " + op2 + ")";
}


/* Returns the 'bvsrem' syntax - signed remainder */
std::string smt2lib::bvsrem(std::string op1, std::string op2)
{
  return "(bvsrem " + op1 + " " + op2 + ")";
}


/* Returns the 'bvsmod' syntax */
std::string smt2lib::bvsmod(std::string op1, std::string op2)
{
  return "(bvsmod " + op1 + " " + op2 + ")";
}


/* Returns the 'bvshl' syntax */
std::string smt2lib::bvshl(std::string op1, std::string op2)
{
  return "(bvshl " + op1 + " " + op2 + ")";
}


/* Returns the 'bvlshr' syntax - unsigned (logical) shift right*/
std::string smt2lib::bvlshr(std::string op1, std::string op2)
{
  return "(bvlshr " + op1 + " " + op2 + ")";
}


/* Returns the 'bvashr' syntax - signed (arithmetical) shift right*/
std::string smt2lib::bvashr(std::string op1, std::string op2)
{
  return "(bvashr " + op1 + " " + op2 + ")";
}


/* Returns the 'bvnand' syntax */
std::string smt2lib::bvnand(std::string op1, std::string op2)
{
  return "(bvnand " + op1 + " " + op2 + ")";
}


/* Returns the 'bvnor' syntax */
std::string smt2lib::bvnor(std::string op1, std::string op2)
{
  return "(bvnor " + op1 + " " + op2 + ")";
}


/* Returns the 'bvxnor' syntax */
std::string smt2lib::bvxnor(std::string op1, std::string op2)
{
  return "(bvxnor " + op1 + " " + op2 + ")";
}


/* Returns the 'bvsdiv' syntax */
std::string smt2lib::bvsdiv(std::string op1, std::string op2)
{
  return "(bvsdiv " + op1 + " " + op2 + ")";
}


/* Returns the 'bvudiv' syntax */
std::string smt2lib::bvudiv(std::string op1, std::string op2)
{
  return "(bvudiv " + op1 + " " + op2 + ")";
}

