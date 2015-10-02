/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION


#include <EflagsExpressions.h>
#include <Registers.h>



smt2lib::smtAstAbstractNode *EflagsExpressions::af(SymbolicExpression *parent,
                                                   uint32 bvSize,
                                                   smt2lib::smtAstAbstractNode *op1,
                                                   smt2lib::smtAstAbstractNode *op2)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * af = 0x10 == (0x10 & (regDst ^ op1 ^ op2))
   */
  expr = smt2lib::ite(
            smt2lib::equal(
              smt2lib::bv(0x10, bvSize),
              smt2lib::bvand(
                smt2lib::bv(0x10, bvSize),
                smt2lib::bvxor(
                  smt2lib::extract(bvSize-1, 0, smt2lib::reference(parent->getID())),
                  smt2lib::bvxor(op1, op2)
                )
              )
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::afNeg(SymbolicExpression *parent,
                                                      uint32 bvSize,
                                                      smt2lib::smtAstAbstractNode *op1)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * af = 0x10 == (0x10 & (op1 ^ regDst))
   */
  expr = smt2lib::ite(
            smt2lib::equal(
              smt2lib::bv(0x10, bvSize),
              smt2lib::bvand(
                smt2lib::bv(0x10, bvSize),
                smt2lib::bvxor(
                  op1,
                  smt2lib::extract(bvSize-1, 0, smt2lib::reference(parent->getID()))
                )
              )
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::cfAdd(SymbolicExpression *parent,
                                                      uint32 bvSize,
                                                      smt2lib::smtAstAbstractNode *op1)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * cf = regDst < op1
   */
  expr = smt2lib::ite(
            smt2lib::bvult(
              smt2lib::extract(bvSize-1, 0, smt2lib::reference(parent->getID())),
              op1
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::cfImul(SymbolicExpression *parent,
                                                       uint32 bvSize,
                                                       smt2lib::smtAstAbstractNode *mulRes)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * cf = 0 if sx(parent) == mulRes else 1
   */
  expr = smt2lib::ite(
            smt2lib::equal(
              smt2lib::sx(bvSize, smt2lib::extract(bvSize-1, 0, smt2lib::reference(parent->getID()))),
              mulRes
            ),
            smt2lib::bv(0, 1),
            smt2lib::bv(1, 1));

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::cfMul(uint32 bvSize,
                                                      smt2lib::smtAstAbstractNode *up)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * cf = 0 if up == 0 else 1
   */
  expr = smt2lib::ite(
            smt2lib::equal(
              up,
              smt2lib::bv(0, bvSize)
            ),
            smt2lib::bv(0, 1),
            smt2lib::bv(1, 1));

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::cfNeg(uint32 bvSize,
                                                      smt2lib::smtAstAbstractNode *op1)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * cf = 0 if op1 == 0 else 1
   */
  expr = smt2lib::ite(
            smt2lib::equal(
              op1,
              smt2lib::bv(0, bvSize)
            ),
            smt2lib::bv(0, 1),
            smt2lib::bv(1, 1));

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::cfRcl(SymbolicExpression *parent,
                                                      AnalysisProcessor &ap,
                                                      uint32 bvSize,
                                                      smt2lib::smtAstAbstractNode *op2)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * cf = (res & 1) if op2 != 0 else undefined
   * As the second operand can't be symbolized, there is
   * no symbolic expression available. So, we must use the
   * op2's concretization.
   */
  if (op2->getKind() != smt2lib::DECIMAL_NODE)
    throw std::runtime_error("EflagsExpressions::cfRcl() - op2 must be a smtAstDecimalNode node");

  if (reinterpret_cast<smt2lib::smtAstDecimalNode *>(op2)->getValue() != 0)
    expr = smt2lib::extract(bvSize, bvSize, smt2lib::reference(parent->getID()));
  else
    expr = ap.buildSymbolicFlagOperand(ID_TMP_CF);

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::cfRol(SymbolicExpression *parent,
                                                      AnalysisProcessor &ap,
                                                      smt2lib::smtAstAbstractNode *op2)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * cf = (res & 1) if op2 != 0 else undefined
   * As the second operand can't be symbolized, there is
   * no symbolic expression available. So, we must use the
   * op2's concretization.
   */
  if (op2->getKind() != smt2lib::DECIMAL_NODE)
    throw std::runtime_error("EflagsExpressions::cfRol() - op2 must be a smtAstDecimalNode node");

  if (reinterpret_cast<smt2lib::smtAstDecimalNode *>(op2)->getValue() != 0)
    expr = smt2lib::extract(0, 0, smt2lib::reference(parent->getID()));
  else
    expr = ap.buildSymbolicFlagOperand(ID_TMP_CF);

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::cfRor(SymbolicExpression *parent,
                                                      AnalysisProcessor &ap,
                                                      uint32 bvSize,
                                                      smt2lib::smtAstAbstractNode *op2)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * cf = (res >> bvSize - 1) & 1 if op2 != 0 else undefined
   * As the second operand can't be symbolized, there is
   * no symbolic expression available. So, we must use the
   * op2's concretization.
   */
  if (op2->getKind() != smt2lib::DECIMAL_NODE)
    throw std::runtime_error("EflagsExpressions::cfRor() - op2 must be a smtAstDecimalNode node");

  if (reinterpret_cast<smt2lib::smtAstDecimalNode *>(op2)->getValue() != 0) {
    expr = smt2lib::extract(0, 0,
      smt2lib::bvlshr(
        smt2lib::extract(bvSize-1, 0, smt2lib::reference(parent->getID())),
        smt2lib::bvsub(
          smt2lib::bv(bvSize, bvSize),
          smt2lib::bv(1, bvSize)
        )
      )
    );
  }
  else {
    expr = ap.buildSymbolicFlagOperand(ID_TMP_CF);
  }

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::cfSar(SymbolicExpression *parent,
                                                      AnalysisProcessor &ap,
                                                      uint32 bvSize,
                                                      smt2lib::smtAstAbstractNode *op1,
                                                      smt2lib::smtAstAbstractNode *op2)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * if op2 != 0:
   *   if op2 > bvSize:
   *     cf.id = ((op1 >> (bvSize - 1)) & 1)
   *   else:
   *     cf.id = ((op1 >> (op2 - 1)) & 1)
   */
  expr = smt2lib::ite(
            smt2lib::equal(op2, smt2lib::bv(0, bvSize)),
            ap.buildSymbolicFlagOperand(ID_TMP_CF),
            smt2lib::ite(
              smt2lib::bvugt(op2, smt2lib::bv(bvSize, bvSize)),
              smt2lib::extract(0, 0, smt2lib::bvlshr(op1, smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), smt2lib::bv(1, bvSize)))),
              smt2lib::extract(0, 0, smt2lib::bvlshr(op1, smt2lib::bvsub(op2, smt2lib::bv(1, bvSize))))
            )
          );

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::cfShl(SymbolicExpression *parent,
                                                      AnalysisProcessor &ap,
                                                      uint32 bvSize,
                                                      smt2lib::smtAstAbstractNode *op1,
                                                      smt2lib::smtAstAbstractNode *op2)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * cf = (op1 >> (bvSize - op2) & 1) if op2 != 0
   */
  expr = smt2lib::ite(
            smt2lib::equal(op2, smt2lib::bv(0, bvSize)),
            ap.buildSymbolicFlagOperand(ID_TMP_CF),
            smt2lib::extract(0, 0, smt2lib::bvlshr(op1, smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), op2)))
          );

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::cfShr(SymbolicExpression *parent,
                                                      AnalysisProcessor &ap,
                                                      uint32 bvSize,
                                                      smt2lib::smtAstAbstractNode *op1,
                                                      smt2lib::smtAstAbstractNode *op2)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * cf = ((op1 >> (bvSize - 1)) & 1) if op2 != 0
   */
  expr = smt2lib::ite(
            smt2lib::equal(op2, smt2lib::bv(0, bvSize)),
            ap.buildSymbolicFlagOperand(ID_TMP_CF),
            smt2lib::extract(0, 0, smt2lib::bvlshr(op1, smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), smt2lib::bv(1, bvSize))))
          );

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::cfSub(SymbolicExpression *parent,
                                                      uint32 bvSize,
                                                      smt2lib::smtAstAbstractNode *op1,
                                                      smt2lib::smtAstAbstractNode *op2)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * cf = extract(bvSize, bvSize (((op1 ^ op2 ^ res) ^ ((op1 ^ res) & (op1 ^ op2)))))
   */
  expr = smt2lib::extract(bvSize-1, bvSize-1,
              smt2lib::bvxor(
                smt2lib::bvxor(op1, smt2lib::bvxor(op2, smt2lib::extract(bvSize-1, 0, smt2lib::reference(parent->getID())))),
                smt2lib::bvand(
                  smt2lib::bvxor(op1, smt2lib::extract(bvSize-1, 0, smt2lib::reference(parent->getID()))),
                  smt2lib::bvxor(op1, op2)
                )
              )
            );

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::clearFlag(void)
{
  smt2lib::smtAstAbstractNode *expr;

  expr = smt2lib::bv(0, 1);

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::ofAdd(SymbolicExpression *parent,
                                                      uint32 extractSize,
                                                      smt2lib::smtAstAbstractNode *op1,
                                                      smt2lib::smtAstAbstractNode *op2)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * of = high:bool((op1 ^ ~op2) & (op1 ^ regDst))
   */
  expr = smt2lib::ite(
            smt2lib::equal(
              smt2lib::extract(extractSize, extractSize,
                smt2lib::bvand(
                  smt2lib::bvxor(op1, smt2lib::bvnot(op2)),
                  smt2lib::bvxor(op1, smt2lib::extract(extractSize, 0, smt2lib::reference(parent->getID())))
                )
              ),
              smt2lib::bv(1, 1)
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::ofImul(SymbolicExpression *parent,
                                                       uint32 bvSize,
                                                       smt2lib::smtAstAbstractNode *mulRes)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * of = 0 if sx(parent) == mulRes else 1
   */
  expr = smt2lib::ite(
            smt2lib::equal(
              smt2lib::sx(bvSize, smt2lib::extract(bvSize-1, 0, smt2lib::reference(parent->getID()))),
              mulRes
            ),
            smt2lib::bv(0, 1),
            smt2lib::bv(1, 1));

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::ofMul(uint32 bvSize,
                                                      smt2lib::smtAstAbstractNode *up)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * of = 0 if up == 0 else 1
   */
  expr = smt2lib::ite(
            smt2lib::equal(
              up,
              smt2lib::bv(0, bvSize)
            ),
            smt2lib::bv(0, 1),
            smt2lib::bv(1, 1));

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::ofNeg(SymbolicExpression *parent,
                                                      uint32 bvSize,
                                                      smt2lib::smtAstAbstractNode *op1)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * of = bit_cast((res & op1) >> (bvSize - 1), int1(1));
   */
  expr = smt2lib::ite(
            smt2lib::equal(
              smt2lib::extract(0, 0,
                smt2lib::bvshl(
                  smt2lib::bvand(smt2lib::extract(bvSize-1, 0, smt2lib::reference(parent->getID())), op1),
                  smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), smt2lib::bv(1, bvSize))
                )
              ),
              smt2lib::bv(1, 1)
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::ofRol(SymbolicExpression *parent,
                                                      AnalysisProcessor &ap,
                                                      uint32 bvSize,
                                                      smt2lib::smtAstAbstractNode *op2)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * of = ((cf ^ (res >> (bvsize - 1))) & 1) if op2 == 1 else undefined
   * As the second operand can't be symbolized, there is
   * no symbolic expression available. So, we must use the
   * op2's concretization.
   */
  if (op2->getKind() != smt2lib::DECIMAL_NODE)
    throw std::runtime_error("EflagsExpressions::ofRol() - op2 must be a smtAstDecimalNode node");

  if (reinterpret_cast<smt2lib::smtAstDecimalNode *>(op2)->getValue() == 1) {
    expr = smt2lib::extract(0, 0,
              smt2lib::bvxor(
                smt2lib::zx(bvSize-1, ap.buildSymbolicFlagOperand(ID_TMP_CF)),
                smt2lib::bvshl(
                  smt2lib::extract(bvSize-1, 0, smt2lib::reference(parent->getID())),
                  smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), smt2lib::bv(1, bvSize))
                )
              )
            );
  }
  else {
    expr = ap.buildSymbolicFlagOperand(ID_TMP_OF);
  }

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::ofRor(SymbolicExpression *parent,
                                                      AnalysisProcessor &ap,
                                                      uint32 bvSize,
                                                      smt2lib::smtAstAbstractNode *op2)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * of = (((res >> (bvSize - 1)) ^ (res >> (bvSize - 2))) & 1) if op2 == 1 else undefined
   * As the second operand can't be symbolized, there is
   * no symbolic expression available. So, we must use the
   * op2's concretization.
   */
  if (op2->getKind() != smt2lib::DECIMAL_NODE)
    throw std::runtime_error("EflagsExpressions::ofRor() - op2 must be a smtAstDecimalNode node");

  if (reinterpret_cast<smt2lib::smtAstDecimalNode *>(op2)->getValue() == 1) {
    expr = smt2lib::extract(0, 0,
              smt2lib::bvxor(
                smt2lib::bvshl(
                  smt2lib::extract(bvSize-1, 0, smt2lib::reference(parent->getID())),
                  smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), smt2lib::bv(1, bvSize))
                ),
                smt2lib::bvshl(
                  smt2lib::extract(bvSize-1, 0, smt2lib::reference(parent->getID())),
                  smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), smt2lib::bv(2, bvSize))
                )
              )
            );
  }
  else {
    expr = ap.buildSymbolicFlagOperand(ID_TMP_OF);
  }

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::ofSar(SymbolicExpression *parent,
                                                      AnalysisProcessor &ap,
                                                      uint32 bvSize,
                                                      smt2lib::smtAstAbstractNode *op2)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * of = 0 if op2 == 1
   */
  expr = smt2lib::ite(
            smt2lib::equal(op2, smt2lib::bv(1, bvSize)),
            smt2lib::bv(0, 1),
            ap.buildSymbolicFlagOperand(ID_TMP_OF)
          );

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::ofShl(SymbolicExpression *parent,
                                                      AnalysisProcessor &ap,
                                                      uint32 bvSize,
                                                      smt2lib::smtAstAbstractNode *op1,
                                                      smt2lib::smtAstAbstractNode *op2)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * of = bit_cast((op1 >> (bvSize - 1)) ^ (op1 >> (bvSize - 2)), int1(1)); if op2 == 1
   */
  expr = smt2lib::ite(
            smt2lib::equal(op2, smt2lib::bv(1, bvSize)),
            smt2lib::extract(0, 0,
              smt2lib::bvxor(
                smt2lib::bvlshr(op1, smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), smt2lib::bv(1, bvSize))),
                smt2lib::bvlshr(op1, smt2lib::bvsub(smt2lib::bv(bvSize, bvSize), smt2lib::bv(2, bvSize)))
              )
            ),
            ap.buildSymbolicFlagOperand(ID_TMP_OF)
          );

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::ofShr(SymbolicExpression *parent,
                                                      AnalysisProcessor &ap,
                                                      uint32 bvSize,
                                                      smt2lib::smtAstAbstractNode *op1,
                                                      smt2lib::smtAstAbstractNode *op2)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * of = (op1 >> (bvSize - 1) & 1) if op2 == 1
   */
  expr = smt2lib::ite(
            smt2lib::equal(op2, smt2lib::bv(1, bvSize)),
            smt2lib::extract(bvSize-1, bvSize-1, op1),
            ap.buildSymbolicFlagOperand(ID_TMP_OF)
          );

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::ofSub(SymbolicExpression *parent,
                                                      uint32 extractSize,
                                                      smt2lib::smtAstAbstractNode *op1,
                                                      smt2lib::smtAstAbstractNode *op2)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * of = high:bool((op1 ^ op2) & (op1 ^ regDst))
   */
  expr = smt2lib::ite(
            smt2lib::equal(
              smt2lib::extract(extractSize, extractSize,
                smt2lib::bvand(
                  smt2lib::bvxor(op1, op2),
                  smt2lib::bvxor(op1, smt2lib::extract(extractSize, 0, smt2lib::reference(parent->getID())))
                )
              ),
              smt2lib::bv(1, 1)
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::pf(SymbolicExpression *parent, uint32 bvSize)
{
  uint32 counter = 0;
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   *
   * pf is set to one if there is a even number of bit set to 1 in the least
   * significant byte of the result.
   */
  expr = smt2lib::bv(1, 1);
  for ( ; counter <= 7 ; counter++) {
    expr = smt2lib::bvxor(
             smt2lib::newInstance(expr),
             smt2lib::extract(0, 0,
               smt2lib::bvlshr(
                 smt2lib::extract(bvSize-1, 0, smt2lib::reference(parent->getID())),
                 smt2lib::bv(counter, bvSize)
               )
            )
          );
  }

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::pfShl(SymbolicExpression *parent,
                                                      AnalysisProcessor &ap,
                                                      uint32 bvSize,
                                                      smt2lib::smtAstAbstractNode *op2)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * pf if op2 != 0
   */
  expr = smt2lib::ite(
            smt2lib::equal(op2, smt2lib::bv(0, bvSize)),
            ap.buildSymbolicFlagOperand(ID_TMP_PF),
            EflagsExpressions::pf(parent, bvSize)
          );

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::setFlag(void)
{
  smt2lib::smtAstAbstractNode *expr;

  expr = smt2lib::bv(1, 1);

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::sf(SymbolicExpression *parent,
                                                   uint32 extractSize)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * sf = high:bool(regDst)
   */
  expr = smt2lib::ite(
            smt2lib::equal(
              smt2lib::extract(extractSize, extractSize, smt2lib::reference(parent->getID())),
              smt2lib::bv(1, 1)
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::sfShl(SymbolicExpression *parent,
                                                      AnalysisProcessor &ap,
                                                      uint32 bvSize,
                                                      uint32 extractSize,
                                                      smt2lib::smtAstAbstractNode *op2)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * sf if op2 != 0
   */
  expr = smt2lib::ite(
            smt2lib::equal(op2, smt2lib::bv(0, bvSize)),
            ap.buildSymbolicFlagOperand(ID_TMP_SF),
            EflagsExpressions::sf(parent, extractSize)
          );

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::zf(SymbolicExpression *parent,
                                                   uint32 bvSize)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * zf = 0 == regDst
   */
  expr = smt2lib::ite(
            smt2lib::equal(
              smt2lib::extract(bvSize-1, 0, smt2lib::reference(parent->getID())),
              smt2lib::bv(0, bvSize)
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  return expr;
}


smt2lib::smtAstAbstractNode *EflagsExpressions::zfShl(SymbolicExpression *parent,
                                                      AnalysisProcessor &ap,
                                                      uint32 bvSize,
                                                      smt2lib::smtAstAbstractNode *op2)
{
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * zf if op2 != 0
   */
  expr = smt2lib::ite(
            smt2lib::equal(op2, smt2lib::bv(0, bvSize)),
            ap.buildSymbolicFlagOperand(ID_TMP_ZF),
            EflagsExpressions::zf(parent, bvSize)
          );

  return expr;
}

#endif /* LIGHT_VERSION */

