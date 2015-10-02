/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef VISITOR_H
#define VISITOR_H


namespace smt2lib{
    class smtAstAssertNode;
    class smtAstBvaddNode;
    class smtAstBvandNode;
    class smtAstBvashrNode;
    class smtAstBvlshrNode;
    class smtAstBvmulNode;
    class smtAstBvnandNode;
    class smtAstBvnegNode;
    class smtAstBvnorNode;
    class smtAstBvnotNode;
    class smtAstBvorNode;
    class smtAstBvrolNode;
    class smtAstBvrorNode;
    class smtAstBvsdivNode;
    class smtAstBvsgeNode;
    class smtAstBvsgtNode;
    class smtAstBvshlNode;
    class smtAstBvsleNode;
    class smtAstBvsltNode;
    class smtAstBvsmodNode;
    class smtAstBvsremNode;
    class smtAstBvsubNode;
    class smtAstBvudivNode;
    class smtAstBvugeNode;
    class smtAstBvugtNode;
    class smtAstBvuleNode;
    class smtAstBvultNode;
    class smtAstBvuremNode;
    class smtAstBvxnorNode;
    class smtAstBvxorNode;
    class smtAstBvNode;
    class smtAstCompoundNode;
    class smtAstConcatNode;
    class smtAstDecimalNode;
    class smtAstDeclareNode;
    class smtAstDistinctNode;
    class smtAstEqualNode;
    class smtAstExtractNode;
    class smtAstIteNode;
    class smtAstReferenceNode;
    class smtAstStringNode;
    class smtAstSxNode;
    class smtAstVariableNode;
    class smtAstZxNode;
};

class Visitor {

    public:
      Visitor(){};
      virtual ~Visitor(){};

      virtual void operator()(smt2lib::smtAstAssertNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvaddNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvandNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvashrNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvlshrNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvmulNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvnandNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvnegNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvnorNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvnotNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvorNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvrolNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvrorNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvsdivNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvsgeNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvsgtNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvshlNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvsleNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvsltNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvsmodNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvsremNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvsubNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvudivNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvugeNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvugtNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvuleNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvultNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvuremNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvxnorNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvxorNode& e) = 0;
      virtual void operator()(smt2lib::smtAstBvNode& e) = 0;
      virtual void operator()(smt2lib::smtAstCompoundNode& e) = 0;
      virtual void operator()(smt2lib::smtAstConcatNode& e) = 0;
      virtual void operator()(smt2lib::smtAstDecimalNode& e) = 0;
      virtual void operator()(smt2lib::smtAstDeclareNode& e) = 0;
      virtual void operator()(smt2lib::smtAstDistinctNode& e) = 0;
      virtual void operator()(smt2lib::smtAstEqualNode& e) = 0;
      virtual void operator()(smt2lib::smtAstExtractNode& e) = 0;
      virtual void operator()(smt2lib::smtAstIteNode& e) = 0;
      virtual void operator()(smt2lib::smtAstReferenceNode& e) = 0;
      virtual void operator()(smt2lib::smtAstStringNode& e) = 0;
      virtual void operator()(smt2lib::smtAstSxNode& e) = 0;
      virtual void operator()(smt2lib::smtAstVariableNode& e) = 0;
      virtual void operator()(smt2lib::smtAstZxNode& e) = 0;


};

#endif
