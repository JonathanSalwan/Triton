
#include <EflagsExpressions.h>
#include <Registers.h>



std::string EflagsExpressions::af(SymbolicExpression *parent,
                                  uint32 bvSize,
                                  std::stringstream &op1,
                                  std::stringstream &op2)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * af = 0x10 == (0x10 & (regDst ^ op1 ^ op2))
   */
  expr << smt2lib::ite(
            smt2lib::equal(
              smt2lib::bv(0x10, bvSize),
              smt2lib::bvand(
                smt2lib::bv(0x10, bvSize),
                smt2lib::bvxor(
                  parent->getID2Str(),
                  smt2lib::bvxor(op1.str(), op2.str())
                )
              )
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  return expr.str();
}


std::string EflagsExpressions::afNeg(SymbolicExpression *parent,
                                     uint32 bvSize,
                                     std::stringstream &op1)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * af = 0x10 == (0x10 & (op1 ^ regDst))
   */
  expr << smt2lib::ite(
            smt2lib::equal(
              smt2lib::bv(0x10, bvSize),
              smt2lib::bvand(
                smt2lib::bv(0x10, bvSize),
                smt2lib::bvxor(
                  op1.str(),
                  parent->getID2Str()
                )
              )
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  return expr.str();
}


std::string EflagsExpressions::cfAdd(SymbolicExpression *parent,
                                     std::stringstream &op1)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * cf = regDst < op1
   */
  expr << smt2lib::ite(
            smt2lib::bvult(
              parent->getID2Str(),
              op1.str()
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  return expr.str();
}


std::string EflagsExpressions::cfImul(SymbolicExpression *parent,
                                     std::stringstream &op1)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * cf = 0 if res == op1 else 1
   */
  expr << smt2lib::ite(
            smt2lib::equal(
              parent->getID2Str(),
              op1.str()
            ),
            smt2lib::bv(0, 1),
            smt2lib::bv(1, 1));

  return expr.str();
}


std::string EflagsExpressions::cfMul(uint32 bvSize,
                                     std::stringstream &up)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * cf = 0 if up == 0 else 1
   */
  expr << smt2lib::ite(
            smt2lib::equal(
              up.str(),
              smt2lib::bv(0, bvSize)
            ),
            smt2lib::bv(0, 1),
            smt2lib::bv(1, 1));

  return expr.str();
}


std::string EflagsExpressions::cfNeg(uint32 bvSize,
                                     std::stringstream &op1)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * cf = 0 if op1 == 0 else 1
   */
  expr << smt2lib::ite(
            smt2lib::equal(
              op1.str(),
              smt2lib::bv(0, bvSize)
            ),
            smt2lib::bv(0, 1),
            smt2lib::bv(1, 1));

  return expr.str();
}


std::string EflagsExpressions::cfRcl(SymbolicExpression *parent,
                                     AnalysisProcessor &ap,
                                     uint32 bvSize,
                                     std::stringstream &op2)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * cf = (res & 1) if op2 != 0 else undefined
   * As the second operand can't be symbolized, there is
   * no symbolic expression available. So, we must use the
   * op2's concretization.
   */
  if (std::stoi(op2.str()) != 0)
    expr << smt2lib::extract(bvSize, bvSize, parent->getID2Str());
  else
    expr << ap.buildSymbolicFlagOperand(ID_CF);

  return expr.str();
}


std::string EflagsExpressions::cfRol(SymbolicExpression *parent,
                                     AnalysisProcessor &ap,
                                     std::stringstream &op2)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * cf = (res & 1) if op2 != 0 else undefined
   * As the second operand can't be symbolized, there is
   * no symbolic expression available. So, we must use the
   * op2's concretization.
   */
  if (std::stoi(op2.str()) != 0)
    expr << smt2lib::extract(0, 0, parent->getID2Str());
  else
    expr << ap.buildSymbolicFlagOperand(ID_CF);

  return expr.str();
}


std::string EflagsExpressions::cfRor(SymbolicExpression *parent,
                                     AnalysisProcessor &ap,
                                     uint32 bvSize,
                                     std::stringstream &op2)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * cf = (res >> bvSize - 1) & 1 if op2 != 0 else undefined
   * As the second operand can't be symbolized, there is
   * no symbolic expression available. So, we must use the
   * op2's concretization.
   */
  if (std::stoi(op2.str()) != 0) {
    expr << smt2lib::extract(0, 0,
      smt2lib::bvlshr(
        parent->getID2Str(),
        smt2lib::bvsub(
          smt2lib::bv(bvSize, bvSize),
          smt2lib::bv(1, bvSize)
        )
      )
    );
  }
  else {
    expr << ap.buildSymbolicFlagOperand(ID_CF);
  }

  return expr.str();
}


std::string EflagsExpressions::cfSar(SymbolicExpression *parent,
                                     AnalysisProcessor &ap,
                                     uint32 bvSize,
                                     std::stringstream &op1,
                                     std::stringstream &op2)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * if op2 != 0:
   *   if op2 > bvSize:
   *     cf.id = ((op1 >> (bvSize - 1)) & 1)
   *   else:
   *     cf.id = ((op1 >> (op2 - 1)) & 1)
   */
  expr << smt2lib::ite(
            smt2lib::equal(op2.str(), smt2lib::bv(0, bvSize)),
            ap.buildSymbolicFlagOperand(ID_CF),
            smt2lib::ite(
              smt2lib::bvugt(op2.str(), smt2lib::bv(bvSize, bvSize)),
              smt2lib::extract(0, 0, smt2lib::bvlshr(op1.str(), smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), smt2lib::bv(1, bvSize)))),
              smt2lib::extract(0, 0, smt2lib::bvlshr(op1.str(), smt2lib::bvsub(op2.str(), smt2lib::bv(1, bvSize))))
            )
          );

  return expr.str();
}


std::string EflagsExpressions::cfShl(SymbolicExpression *parent,
                                     AnalysisProcessor &ap,
                                     uint32 bvSize,
                                     std::stringstream &op1,
                                     std::stringstream &op2)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * cf = (op1 >> (bvSize - op2) & 1) if op2 != 0
   */
  expr << smt2lib::ite(
            smt2lib::equal(op2.str(), smt2lib::bv(0, bvSize)),
            ap.buildSymbolicFlagOperand(ID_CF),
            smt2lib::extract(0, 0, smt2lib::bvlshr(op1.str(), smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), op2.str())))
          );

  return expr.str();
}


std::string EflagsExpressions::cfShr(SymbolicExpression *parent,
                                     AnalysisProcessor &ap,
                                     uint32 bvSize,
                                     std::stringstream &op1,
                                     std::stringstream &op2)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * cf = ((op1 >> (op2 - 1)) & 1) if op2 != 0
   */
  expr << smt2lib::ite(
            smt2lib::equal(op2.str(), smt2lib::bv(0, bvSize)),
            ap.buildSymbolicFlagOperand(ID_CF),
            smt2lib::extract(0, 0, smt2lib::bvlshr(op1.str(), smt2lib::bvsub(op2.str(), smt2lib::bv(1, bvSize))))
          );

  return expr.str();
}


std::string EflagsExpressions::cfSub(std::stringstream &op1,
                                     std::stringstream &op2)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * cf = op1 < op2
   */
  expr << smt2lib::ite(
            smt2lib::bvult(
              op1.str(),
              op2.str()
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  return expr.str();
}


std::string EflagsExpressions::clearFlag(void)
{
  std::stringstream expr;

  expr << smt2lib::bv(0, 1);

  return expr.str();
}


std::string EflagsExpressions::ofAdd(SymbolicExpression *parent,
                                     uint32 extractSize,
                                     std::stringstream &op1,
                                     std::stringstream &op2)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * of = high:bool((op1 ^ ~op2) & (op1 ^ regDst))
   */
  expr << smt2lib::ite(
            smt2lib::equal(
              smt2lib::extract(extractSize, extractSize,
                smt2lib::bvand(
                  smt2lib::bvxor(op1.str(), smt2lib::bvnot(op2.str())),
                  smt2lib::bvxor(op1.str(), parent->getID2Str())
                )
              ),
              smt2lib::bv(1, 1)
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  return expr.str();
}


std::string EflagsExpressions::ofImul(SymbolicExpression *parent,
                                     std::stringstream &op1)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * of = 0 if res == op1 else 1
   */
  expr << smt2lib::ite(
            smt2lib::equal(
              parent->getID2Str(),
              op1.str()
            ),
            smt2lib::bv(0, 1),
            smt2lib::bv(1, 1));

  return expr.str();
}


std::string EflagsExpressions::ofMul(uint32 bvSize,
                                     std::stringstream &up)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * of = 0 if up == 0 else 1
   */
  expr << smt2lib::ite(
            smt2lib::equal(
              up.str(),
              smt2lib::bv(0, bvSize)
            ),
            smt2lib::bv(0, 1),
            smt2lib::bv(1, 1));

  return expr.str();
}


std::string EflagsExpressions::ofNeg(SymbolicExpression *parent,
                                     uint32 bvSize,
                                     std::stringstream &op1)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * of = bit_cast((res & op1) >> (bvSize - 1), int1(1));
   */
  expr << smt2lib::ite(
            smt2lib::equal(
              smt2lib::extract(0, 0,
                smt2lib::bvshl(
                  smt2lib::bvand(parent->getID2Str(), op1.str()),
                  smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), smt2lib::bv(1, bvSize))
                )
              ),
              smt2lib::bv(1, 1)
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  return expr.str();
}


std::string EflagsExpressions::ofRol(SymbolicExpression *parent,
                                     AnalysisProcessor &ap,
                                     uint32 bvSize,
                                     std::stringstream &op2)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * of = ((cf ^ (res >> (bvsize - 1))) & 1) if op2 == 1 else undefined
   * As the second operand can't be symbolized, there is
   * no symbolic expression available. So, we must use the
   * op2's concretization.
   */
  if (std::stoi(op2.str()) == 1) {
    expr << smt2lib::extract(0, 0,
              smt2lib::bvxor(
                ap.buildSymbolicFlagOperand(ID_CF),
                smt2lib::bvshl(
                  parent->getID2Str(),
                  smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), smt2lib::bv(1, bvSize))
                )
              )
            );
  }
  else {
    expr << ap.buildSymbolicFlagOperand(ID_OF);
  }

  return expr.str();
}


std::string EflagsExpressions::ofRor(SymbolicExpression *parent,
                                     AnalysisProcessor &ap,
                                     uint32 bvSize,
                                     std::stringstream &op2)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * of = (((res >> (bvSize - 1)) ^ (res >> (bvSize - 2))) & 1) if op2 == 1 else undefined
   * As the second operand can't be symbolized, there is
   * no symbolic expression available. So, we must use the
   * op2's concretization.
   */
  if (std::stoi(op2.str()) == 1) {
    expr << smt2lib::extract(0, 0,
              smt2lib::bvxor(
                smt2lib::bvshl(
                  parent->getID2Str(),
                  smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), smt2lib::bv(1, bvSize))
                ),
                smt2lib::bvshl(
                  parent->getID2Str(),
                  smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), smt2lib::bv(2, bvSize))
                )
              )
            );
  }
  else {
    expr << ap.buildSymbolicFlagOperand(ID_OF);
  }

  return expr.str();
}


std::string EflagsExpressions::ofSar(SymbolicExpression *parent,
                                     AnalysisProcessor &ap,
                                     uint32 bvSize,
                                     std::stringstream &op2)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * of = 0 if op2 == 1
   */
  expr << smt2lib::ite(
            smt2lib::equal(op2.str(), smt2lib::bv(1, bvSize)),
            smt2lib::bv(0, 1),
            ap.buildSymbolicFlagOperand(ID_OF)
          );

  return expr.str();
}


std::string EflagsExpressions::ofShl(SymbolicExpression *parent,
                                     AnalysisProcessor &ap,
                                     uint32 bvSize,
                                     std::stringstream &op1,
                                     std::stringstream &op2)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * of = bit_cast((op1 >> (bvSize - 1)) ^ (op1 >> (bvSize - 2)), int1(1)); if op2 == 1
   */
  expr << smt2lib::ite(
            smt2lib::equal(op2.str(), smt2lib::bv(1, bvSize)),
            smt2lib::extract(0, 0,
              smt2lib::bvxor(
                smt2lib::bvlshr(op1.str(), smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), smt2lib::bv(1, bvSize))),
                smt2lib::bvlshr(op1.str(), smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), smt2lib::bv(2, bvSize)))
              )
            ),
            ap.buildSymbolicFlagOperand(ID_OF)
          );

  return expr.str();
}


std::string EflagsExpressions::ofShr(SymbolicExpression *parent,
                                     AnalysisProcessor &ap,
                                     uint32 bvSize,
                                     std::stringstream &op1,
                                     std::stringstream &op2)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * of = (op1 >> (bvSize - 1) & 1) if op2 == 1
   */
  expr << smt2lib::ite(
            smt2lib::equal(op2.str(), smt2lib::bv(1, bvSize)),
            smt2lib::extract(0, 0,
                smt2lib::bvlshr(op1.str(), smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), smt2lib::bv(1, bvSize)))
            ),
            ap.buildSymbolicFlagOperand(ID_OF)
          );

  return expr.str();
}


std::string EflagsExpressions::ofSub(SymbolicExpression *parent,
                                     uint32 extractSize,
                                     std::stringstream &op1,
                                     std::stringstream &op2)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * of = high:bool((op1 ^ op2) & (op1 ^ regDst))
   */
  expr << smt2lib::ite(
            smt2lib::equal(
              smt2lib::extract(extractSize, extractSize,
                smt2lib::bvand(
                  smt2lib::bvxor(op1.str(), op2.str()),
                  smt2lib::bvxor(op1.str(), parent->getID2Str())
                )
              ),
              smt2lib::bv(1, 1)
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  return expr.str();
}


std::string EflagsExpressions::pf(SymbolicExpression *parent)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   *
   * pf is set to one if there is a even number of bit set to 1 in the least
   * significant byte of the result.
   */
  expr << smt2lib::ite(
            smt2lib::equal(
              smt2lib::parityFlag(
                smt2lib::extract(7, 0, parent->getID2Str())),
              smt2lib::bv(0, 1)
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  return expr.str();
}


std::string EflagsExpressions::pfShl(SymbolicExpression *parent,
                                     AnalysisProcessor &ap,
                                     uint32 bvSize,
                                     std::stringstream &op2)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * pf if op2 != 0
   */
  expr << smt2lib::ite(
            smt2lib::equal(op2.str(), smt2lib::bv(0, bvSize)),
            ap.buildSymbolicFlagOperand(ID_PF),
            EflagsExpressions::pf(parent)
          );

  return expr.str();
}


std::string EflagsExpressions::setFlag(void)
{
  std::stringstream expr;

  expr << smt2lib::bv(1, 1);

  return expr.str();
}


std::string EflagsExpressions::sf(SymbolicExpression *parent,
                                  uint32 extractSize)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * sf = high:bool(regDst)
   */
  expr << smt2lib::ite(
            smt2lib::equal(
              smt2lib::extract(extractSize, extractSize, parent->getID2Str()),
              smt2lib::bv(1, 1)
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  return expr.str();
}


std::string EflagsExpressions::sfShl(SymbolicExpression *parent,
                                     AnalysisProcessor &ap,
                                     uint32 bvSize,
                                     uint32 extractSize,
                                     std::stringstream &op2)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * sf if op2 != 0
   */
  expr << smt2lib::ite(
            smt2lib::equal(op2.str(), smt2lib::bv(0, bvSize)),
            ap.buildSymbolicFlagOperand(ID_SF),
            EflagsExpressions::sf(parent, extractSize)
          );

  return expr.str();
}


std::string EflagsExpressions::zf(SymbolicExpression *parent,
                                  uint32 bvSize)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * zf = 0 == regDst
   */
  expr << smt2lib::ite(
            smt2lib::equal(
              parent->getID2Str(),
              smt2lib::bv(0, bvSize)
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  return expr.str();
}


std::string EflagsExpressions::zfShl(SymbolicExpression *parent,
                                     AnalysisProcessor &ap,
                                     uint32 bvSize,
                                     std::stringstream &op2)
{
  std::stringstream expr;

  /*
   * Create the SMT semantic.
   * zf if op2 != 0
   */
  expr << smt2lib::ite(
            smt2lib::equal(op2.str(), smt2lib::bv(0, bvSize)),
            ap.buildSymbolicFlagOperand(ID_ZF),
            EflagsExpressions::zf(parent, bvSize)
          );

  return expr.str();
}

