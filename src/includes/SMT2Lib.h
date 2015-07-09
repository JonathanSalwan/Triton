
#ifndef   SMT2LIB_H
#define   SMT2LIB_H

#include <list>
#include <ostream>
#include <stdexcept>
#include <string>
#include <vector>

#include "TritonTypes.h"


namespace smt2lib {

  /* Enumerate all kinds of node */
  enum kind_e {
    ASSERT_NODE,
    BVADD_NODE,
    BVAND_NODE,
    BVASHR_NODE,
    BVLSHR_NODE,
    BVMUL_NODE,
    BVNAND_NODE,
    BVNEG_NODE,
    BVNOR_NODE,
    BVNOT_NODE,
    BVOR_NODE,
    BVROL_NODE,
    BVROR_NODE,
    BVSDIV_NODE,
    BVSGE_NODE,
    BVSGT_NODE,
    BVSHL_NODE,
    BVSLE_NODE,
    BVSLT_NODE,
    BVSMOD_NODE,
    BVSREM_NODE,
    BVSUB_NODE,
    BVUDIV_NODE,
    BVUGE_NODE,
    BVUGT_NODE,
    BVULE_NODE,
    BVULT_NODE,
    BVUREM_NODE,
    BVXNOR_NODE,
    BVXOR_NODE,
    BV_NODE,
    COMPOUND_NODE,
    CONCAT_NODE,
    DECIMAL_NODE,
    DECLARE_NODE,
    EQUAL_NODE,
    EXTRACT_NODE,
    ITE_NODE,
    REFERENCE_NODE,
    STRING_NODE,
    SX_NODE,
    UNDEFINED_NODE,
    ZX_NODE
  };


  /* Abstract node */
  class smtAstAbstractNode
  {
    protected:
      enum kind_e                         kind;
      std::vector<smtAstAbstractNode *>   childs;

    public:
      smtAstAbstractNode(enum kind_e kind);
      smtAstAbstractNode(const smtAstAbstractNode &copy);
      smtAstAbstractNode();
      ~smtAstAbstractNode();

      enum kind_e                         getKind(void);
      std::vector<smtAstAbstractNode *>   &getChilds(void);
      void                                addChild(smtAstAbstractNode *child);
  };


  /* (assert <expr1>) node */
  class smtAstAssertNode : public smtAstAbstractNode
  {
    public:
      smtAstAssertNode(smtAstAbstractNode *expr);
      smtAstAssertNode(const smtAstAssertNode &copy);
      ~smtAstAssertNode();
  };


  /* (bvadd <expr1> <expr2>) node */
  class smtAstBvaddNode : public smtAstAbstractNode
  {
    public:
      smtAstBvaddNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstBvaddNode(const smtAstBvaddNode &copy);
      ~smtAstBvaddNode();
  };


  /* (bvand <expr1> <expr2>) node */
  class smtAstBvandNode : public smtAstAbstractNode
  {
    public:
      smtAstBvandNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstBvandNode(const smtAstBvandNode &copy);
      ~smtAstBvandNode();
  };


  /* (bvashr <expr1> <expr2>) node */
  class smtAstBvashrNode : public smtAstAbstractNode
  {
    public:
      smtAstBvashrNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstBvashrNode(const smtAstBvashrNode &copy);
      ~smtAstBvashrNode();
  };


  /* (bvlshr <expr1> <expr2>) node */
  class smtAstBvlshrNode : public smtAstAbstractNode
  {
    public:
      smtAstBvlshrNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstBvlshrNode(const smtAstBvlshrNode &copy);
      ~smtAstBvlshrNode();
  };


  /* (bvmul <expr1> <expr2>) node */
  class smtAstBvmulNode : public smtAstAbstractNode
  {
    public:
      smtAstBvmulNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstBvmulNode(const smtAstBvmulNode &copy);
      ~smtAstBvmulNode();
  };


  /* (bvnand <expr1> <expr2>) node */
  class smtAstBvnandNode : public smtAstAbstractNode
  {
    public:
      smtAstBvnandNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstBvnandNode(const smtAstBvnandNode &copy);
      ~smtAstBvnandNode();
  };


  /* (bvneg <expr>) node */
  class smtAstBvnegNode : public smtAstAbstractNode
  {
    public:
      smtAstBvnegNode(smtAstAbstractNode *expr);
      smtAstBvnegNode(const smtAstBvnegNode &copy);
      ~smtAstBvnegNode();
  };


  /* (bvnor <expr1> <expr2>) node */
  class smtAstBvnorNode : public smtAstAbstractNode
  {
    public:
      smtAstBvnorNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstBvnorNode(const smtAstBvnorNode &copy);
      ~smtAstBvnorNode();
  };


  /* (bvnot <expr>) node */
  class smtAstBvnotNode : public smtAstAbstractNode
  {
    public:
      smtAstBvnotNode(smtAstAbstractNode *expr1);
      smtAstBvnotNode(const smtAstBvnotNode &copy);
      ~smtAstBvnotNode();
  };


  /* (bvor <expr1> <expr2>) node */
  class smtAstBvorNode : public smtAstAbstractNode
  {
    public:
      smtAstBvorNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstBvorNode(const smtAstBvorNode &copy);
      ~smtAstBvorNode();
  };


  /* ((_ rotate_left rot) expr) node */
  class smtAstBvrolNode : public smtAstAbstractNode
  {
    public:
      smtAstBvrolNode(uint64 rot, smtAstAbstractNode *expr);
      smtAstBvrolNode(smtAstAbstractNode *rot, smtAstAbstractNode *expr);
      smtAstBvrolNode(const smtAstBvrolNode &copy);
      ~smtAstBvrolNode();
  };


  /* ((_ rotate_right rot) expr) node */
  class smtAstBvrorNode : public smtAstAbstractNode
  {
    public:
      smtAstBvrorNode(uint64 rot, smtAstAbstractNode *expr);
      smtAstBvrorNode(smtAstAbstractNode *rot, smtAstAbstractNode *expr);
      smtAstBvrorNode(const smtAstBvrorNode &copy);
      ~smtAstBvrorNode();
  };


  /* (bvsdiv <expr1> <expr2>) node */
  class smtAstBvsdivNode : public smtAstAbstractNode
  {
    public:
      smtAstBvsdivNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstBvsdivNode(const smtAstBvsdivNode &copy);
      ~smtAstBvsdivNode();
  };


  /* (bvsge <expr1> <expr2>) node */
  class smtAstBvsgeNode : public smtAstAbstractNode
  {
    public:
      smtAstBvsgeNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstBvsgeNode(const smtAstBvsgeNode &copy);
      ~smtAstBvsgeNode();
  };


  /* (bvsgt <expr1> <expr2>) node */
  class smtAstBvsgtNode : public smtAstAbstractNode
  {
    public:
      smtAstBvsgtNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstBvsgtNode(const smtAstBvsgtNode &copy);
      ~smtAstBvsgtNode();
  };


  /* (bvshl <expr1> <expr2>) node */
  class smtAstBvshlNode : public smtAstAbstractNode
  {
    public:
      smtAstBvshlNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstBvshlNode(const smtAstBvshlNode &copy);
      ~smtAstBvshlNode();
  };


  /* (bvsle <expr1> <expr2>) node */
  class smtAstBvsleNode : public smtAstAbstractNode
  {
    public:
      smtAstBvsleNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstBvsleNode(const smtAstBvsleNode &copy);
      ~smtAstBvsleNode();
  };


  /* (bvslt <expr1> <expr2>) node */
  class smtAstBvsltNode : public smtAstAbstractNode
  {
    public:
      smtAstBvsltNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstBvsltNode(const smtAstBvsltNode &copy);
      ~smtAstBvsltNode();
  };


  /* (bvsmod <expr1> <expr2>) node */
  class smtAstBvsmodNode : public smtAstAbstractNode
  {
    public:
      smtAstBvsmodNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstBvsmodNode(const smtAstBvsmodNode &copy);
      ~smtAstBvsmodNode();
  };


  /* (bvsrem <expr1> <expr2>) node */
  class smtAstBvsremNode : public smtAstAbstractNode
  {
    public:
      smtAstBvsremNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstBvsremNode(const smtAstBvsremNode &copy);
      ~smtAstBvsremNode();
  };


  /* (bvsub <expr1> <expr2>) node */
  class smtAstBvsubNode : public smtAstAbstractNode
  {
    public:
      smtAstBvsubNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstBvsubNode(const smtAstBvsubNode &copy);
      ~smtAstBvsubNode();
  };


  /* (bvudiv <expr1> <expr2>) node */
  class smtAstBvudivNode : public smtAstAbstractNode
  {
    public:
      smtAstBvudivNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstBvudivNode(const smtAstBvudivNode &copy);
      ~smtAstBvudivNode();
  };


  /* (bvuge <expr1> <expr2>) node */
  class smtAstBvugeNode : public smtAstAbstractNode
  {
    public:
      smtAstBvugeNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstBvugeNode(const smtAstBvugeNode &copy);
      ~smtAstBvugeNode();
  };


  /* (bvugt <expr1> <expr2>) node */
  class smtAstBvugtNode : public smtAstAbstractNode
  {
    public:
      smtAstBvugtNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstBvugtNode(const smtAstBvugtNode &copy);
      ~smtAstBvugtNode();
  };


  /* (bvule <expr1> <expr2>) node */
  class smtAstBvuleNode : public smtAstAbstractNode
  {
    public:
      smtAstBvuleNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstBvuleNode(const smtAstBvuleNode &copy);
      ~smtAstBvuleNode();
  };


  /* (bvult <expr1> <expr2>) node */
  class smtAstBvultNode : public smtAstAbstractNode
  {
    public:
      smtAstBvultNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstBvultNode(const smtAstBvultNode &copy);
      ~smtAstBvultNode();
  };


  /* (bvurem <expr1> <expr2>) node */
  class smtAstBvuremNode : public smtAstAbstractNode
  {
    public:
      smtAstBvuremNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstBvuremNode(const smtAstBvuremNode &copy);
      ~smtAstBvuremNode();
  };


  /* (bvxnor <expr1> <expr2>) node */
  class smtAstBvxnorNode : public smtAstAbstractNode
  {
    public:
      smtAstBvxnorNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstBvxnorNode(const smtAstBvxnorNode &copy);
      ~smtAstBvxnorNode();
  };


  /* (bvxor <expr1> <expr2>) node */
  class smtAstBvxorNode : public smtAstAbstractNode
  {
    public:
      smtAstBvxorNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstBvxorNode(const smtAstBvxorNode &copy);
      ~smtAstBvxorNode();
  };


  /* (_ bv<value> <size>) node */
  class smtAstBvNode : public smtAstAbstractNode
  {
    public:
      smtAstBvNode(uint64 value, uint64 size);
      smtAstBvNode(const smtAstBvNode &copy);
      ~smtAstBvNode();
  };


  /* compound node */
  class smtAstCompoundNode : public smtAstAbstractNode
  {
    public:
      smtAstCompoundNode(std::vector<smtAstAbstractNode*> exprs);
      smtAstCompoundNode(const smtAstCompoundNode &copy);
      ~smtAstCompoundNode();
  };


  /* (concat <expr1> <expr2> ...) node */
  class smtAstConcatNode : public smtAstAbstractNode
  {
    public:
      smtAstConcatNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstConcatNode(std::vector<smtAstAbstractNode *> exprs);
      smtAstConcatNode(std::list<smtAstAbstractNode *> exprs);
      smtAstConcatNode(const smtAstConcatNode &copy);
      ~smtAstConcatNode();
  };


  /* Decimal node */
  class smtAstDecimalNode : public smtAstAbstractNode
  {
    protected:
      uint64 value;

    public:
      smtAstDecimalNode(uint64 value);
      smtAstDecimalNode(const smtAstDecimalNode &copy);
      ~smtAstDecimalNode();

      uint64 getValue(void);
  };


  /* (declare-fun <symVarName> () (_ BitVec <symVarSize>)) node */
  class smtAstDeclareNode : public smtAstAbstractNode
  {
    public:
      smtAstDeclareNode(std::string symVarName, uint64 symVarSize);
      smtAstDeclareNode(const smtAstDeclareNode &copy);
      ~smtAstDeclareNode();
  };


  /* (= <expr1> <expr2> ...) node */
  class smtAstEqualNode : public smtAstAbstractNode
  {
    public:
      smtAstEqualNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
      smtAstEqualNode(const smtAstEqualNode &copy);
      ~smtAstEqualNode();
  };


  /* ((_ extract <high> <low>) <expr>) node */
  class smtAstExtractNode : public smtAstAbstractNode
  {
    public:
      smtAstExtractNode(uint64 high, uint64 low, smtAstAbstractNode *expr);
      smtAstExtractNode(const smtAstExtractNode &copy);
      ~smtAstExtractNode();
  };


  /* (ite ifExpr thenExpr elseExpr) */
  class smtAstIteNode : public smtAstAbstractNode
  {
    public:
      smtAstIteNode(smtAstAbstractNode *ifExpr, smtAstAbstractNode *thenExpr, smtAstAbstractNode *elseExpr);
      smtAstIteNode(const smtAstIteNode &copy);
      ~smtAstIteNode();
  };


  /* Reference node */
  class smtAstReferenceNode : public smtAstAbstractNode
  {
    protected:
      uint64 value;

    public:
      smtAstReferenceNode(uint64 value);
      smtAstReferenceNode(const smtAstReferenceNode &copy);
      ~smtAstReferenceNode();

      uint64 getValue(void);
  };


  /* String node */
  class smtAstStringNode : public smtAstAbstractNode
  {
    protected:
      std::string value;

    public:
      smtAstStringNode(std::string value);
      smtAstStringNode(const smtAstStringNode &copy);
      ~smtAstStringNode();

      std::string getValue(void);
  };


  /* ((_ sign_extend sizeExt) <expr>) node */
  class smtAstSxNode : public smtAstAbstractNode
  {
    public:
      smtAstSxNode(uint64 sizeExt, smtAstAbstractNode *expr);
      smtAstSxNode(const smtAstSxNode &copy);
      ~smtAstSxNode();
  };


  /* ((_ zero_extend sizeExt) <expr>) node */
  class smtAstZxNode : public smtAstAbstractNode
  {
    public:
      smtAstZxNode(uint64 sizeExt, smtAstAbstractNode *expr);
      smtAstZxNode(const smtAstZxNode &copy);
      ~smtAstZxNode();
  };


  /* Operators */
  std::ostream &operator<<(std::ostream &stream, smtAstAbstractNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstAssertNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvaddNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvandNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvashrNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvlshrNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvmulNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvnandNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvnegNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvnorNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvnotNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvorNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvrolNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvrorNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvsdivNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvsgeNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvsgtNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvshlNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvsleNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvsltNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvsmodNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvsremNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvsubNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvudivNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvugeNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvugtNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvuleNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvultNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvuremNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvxnorNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstBvxorNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstCompoundNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstConcatNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstDecimalNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstDeclareNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstEqualNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstExtractNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstIteNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstReferenceNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstStringNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstSxNode *node);
  std::ostream &operator<<(std::ostream &stream, smtAstZxNode *node);


  /* Utils */
  void freeAllNodes(std::vector<smtAstAbstractNode *> childs);


  /* Node builders */
  smtAstAbstractNode *bv(uint64 value, uint64 size);
  smtAstAbstractNode *bvadd(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *bvand(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *bvashr(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *bvfalse(void);
  smtAstAbstractNode *bvlshr(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *bvmul(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *bvnand(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *bvneg(smtAstAbstractNode *expr);
  smtAstAbstractNode *bvnor(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *bvnot(smtAstAbstractNode *expr);
  smtAstAbstractNode *bvor(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *bvrol(uint64 rot, smtAstAbstractNode *expr);
  smtAstAbstractNode *bvrol(smtAstAbstractNode *rot, smtAstAbstractNode *expr);
  smtAstAbstractNode *bvror(uint64 rot, smtAstAbstractNode *expr);
  smtAstAbstractNode *bvror(smtAstAbstractNode *rot, smtAstAbstractNode *expr);
  smtAstAbstractNode *bvsdiv(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *bvsge(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *bvsgt(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *bvshl(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *bvsle(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *bvslt(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *bvsmod(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *bvsrem(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *bvsub(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *bvtrue(void);
  smtAstAbstractNode *bvudiv(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *bvuge(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *bvugt(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *bvule(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *bvult(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *bvurem(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *bvxnor(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *bvxor(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *compound(std::vector<smtAstAbstractNode *> exprs);
  smtAstAbstractNode *concat(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *concat(std::vector<smtAstAbstractNode *> exprs);
  smtAstAbstractNode *concat(std::list<smtAstAbstractNode *> exprs);
  smtAstAbstractNode *decimal(uint64 value);
  smtAstAbstractNode *declare(std::string symVarName, uint64 symVarSize);
  smtAstAbstractNode *equal(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2);
  smtAstAbstractNode *extract(uint64 high, uint64 low, smtAstAbstractNode *expr);
  smtAstAbstractNode *ite(smtAstAbstractNode *ifExpr, smtAstAbstractNode *thenExpr, smtAstAbstractNode *elseExpr);
  smtAstAbstractNode *reference(uint64 value);
  smtAstAbstractNode *smtAssert(smtAstAbstractNode *expr);
  smtAstAbstractNode *string(std::string value);
  smtAstAbstractNode *sx(uint64 sizeExt, smtAstAbstractNode *expr);
  smtAstAbstractNode *zx(uint64 sizeExt, smtAstAbstractNode *expr);
  smtAstAbstractNode *newInstance(smtAstAbstractNode *node);


} // smt2lib namespace

#endif     /* !SMT2LIB_H */
