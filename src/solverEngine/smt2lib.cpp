#include <string>
#include <stdexcept>

#include "SMT2Lib.h"

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

/* Returns the 'bv' syntax based on a value and a size.
 * Mainly used for the SMT translation */
std::string smt2lib::bv(uint64_t value, uint64_t size)
{
  return "(_ bv" + std::to_string(value) + " " + std::to_string(size) + ")";
}


/* Returns the 'bv' syntax with sign extension applied to it. */
std::string smt2lib::sx(std::string expr, uint64_t size)
{
  return "((_ sign_extend " + std::to_string(size) + ") " + expr + ")";
}


/* Returns the 'bv' syntax with zero extension applied to it. */
std::string smt2lib::zx(std::string expr, uint64_t size)
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


/* Returns the 'bvnot' syntax. */
std::string smt2lib::bvnot(std::string op1)
{
  return "(bvnot " + op1 + ")";
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
std::string smt2lib::extract(uint64_t regSize)
{
  std::stringstream stream;

  switch(regSize){
    case 1:
      stream << "(_ extract 7 0)";
      break;
    case 2:
      stream << "(_ extract 15 0)";
      break;
    case 4:
      stream << "(_ extract 31 0)";
      break;
    case 8:
      stream << "(_ extract 63 0)";
      break;
    default:
      throw std::runtime_error("Error: invalid smt2lib::extract regSize");
  }

  return stream.str();
}


/* Returns the 'extract' syntax based on a regSize and expression */
std::string smt2lib::extract(uint64_t regSize, std::string expr)
{
  return "(" + smt2lib::extract(regSize) + " " + expr + ")";
}


/* Returns the 'extract' syntax. */
std::string smt2lib::extract(uint64_t high, uint64_t low)
{
  return "(_ extract " + std::to_string(high) + " " + std::to_string(low) + ")";
}


/* Returns the 'extract' syntax. */
std::string smt2lib::extract(uint64_t high, uint64_t low, std::string expr)
{
  return "(" + smt2lib::extract(high, low) + " " + expr + ")";
}


/* Returns the 'declare' syntax is symbolic variable and a bit vector.
 * Mainly used for the SMT translation */
std::string smt2lib::declare(uint64_t idSymVar, uint64_t BitVecSize)
{
  std::stringstream stream;

  switch(BitVecSize){
    case 1:
      stream << "(declare-fun SymVar_" << idSymVar << " () (_ BitVec 8))";
      break;
    case 2:
      stream << "(declare-fun SymVar_" << idSymVar << " () (_ BitVec 16))";
      break;
    case 4:
      stream << "(declare-fun SymVar_" << idSymVar << " () (_ BitVec 32))";
      break;
    case 8:
      stream << "(declare-fun SymVar_" << idSymVar << " () (_ BitVec 64))";
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


