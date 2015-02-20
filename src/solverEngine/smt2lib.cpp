#include <string>

#include "SMT2Lib.h"



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
  }

  return stream.str();
}


/* Returns the 'extract' syntax. */
std::string smt2lib::extract(uint64_t high, uint64_t low)
{
  return "(_ extract " + std::to_string(high) + " " + std::to_string(low) + ")";
}


/* Returns the 'extract' syntax. */
std::string smt2lib::extract(uint64_t high, uint64_t low, std::string expr)
{
  return "(" + smt2lib::extract(high, low) + expr + ")";
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
  return "(assert (" + expr + "))";
}


/* Returns the 'equal' syntax. */
std::string smt2lib::equal(std::string op1, std::string op2)
{
  return "(= " + op1 + " " + op2 + ")";
}


