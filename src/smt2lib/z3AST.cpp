#include <Z3ast.h>

Z3ast::Z3ast() {}

Z3ast::~Z3ast() {}

Z3Result& Z3ast::eval(smt2lib::smtAstAbstractNode& e)
{
    e.accept(*this);

    return this->result;
}

void Z3ast::operator()(smt2lib::smtAstAbstractNode& e)
{
    e.accept(*this);
}

void Z3ast::operator()(smt2lib::smtAstAssertNode& e)
{
    throw std::runtime_error("smtAstAssertNode not implemented");
}

void Z3ast::operator()(smt2lib::smtAstBvaddNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = op1.getExpr() + op2.getExpr();

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvandNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = op1.getExpr() & op2.getExpr();

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvashrNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvashr(this->result.getContext(), op1.getExpr(), op2.getExpr()));

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvlshrNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvlshr(this->result.getContext(), op1.getExpr(), op2.getExpr()));

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvmulNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = op1.getExpr() * op2.getExpr();

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvsmodNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvsmod(this->result.getContext(), op1.getExpr(), op2.getExpr()));

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvnandNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = ~(op1.getExpr() & op2.getExpr());

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvnegNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    z3::expr newexpr = -op1.getExpr();

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvnorNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = ~(op1.getExpr() | op2.getExpr());

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvnotNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    z3::expr newexpr = ~op1.getExpr();

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvorNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = op1.getExpr() | op2.getExpr();

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvrolNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_ext_rotate_left(this->result.getContext(), op1.getExpr(), op2.getExpr()));

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvrorNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_ext_rotate_right(this->result.getContext(), op1.getExpr(), op2.getExpr()));

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvsdivNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = op1.getExpr() / op2.getExpr();

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvsgeNode& e)
{

    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = op1.getExpr() >= op2.getExpr();

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvsgtNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = op1.getExpr() > op2.getExpr();

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvshlNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvshl(this->result.getContext(), op1.getExpr(), op2.getExpr()));

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvsleNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = op1.getExpr() <= op2.getExpr();

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvsltNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = op1.getExpr() < op2.getExpr();

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvsremNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvsrem(this->result.getContext(), op1.getExpr(), op2.getExpr()));

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvsubNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = op1.getExpr() - op2.getExpr();

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvudivNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = z3::udiv(op1.getExpr(), op2.getExpr());

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvugeNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = z3::uge(op1.getExpr(), op2.getExpr());

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvugtNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = z3::ugt(op1.getExpr(), op2.getExpr());

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvuleNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = z3::ule(op1.getExpr(), op2.getExpr());

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvultNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = z3::ult(op1.getExpr(), op2.getExpr());

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvuremNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_bvurem(this->result.getContext(), op1.getExpr(), op2.getExpr()));

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvxnorNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = ~(op1.getExpr() ^ op2.getExpr());

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstBvxorNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    z3::expr newexpr = op1.getExpr() ^ op2.getExpr();

    this->result.setExpr(newexpr);
}
void Z3ast::operator()(smt2lib::smtAstBvNode& e)
{

    Z3Result value = this->eval(*e.getChilds()[0]);
    Z3Result size = this->eval(*e.getChilds()[1]);

    z3::expr newexpr = this->result.getContext().bv_val(value.getUint64Value(), size.getUint64Value());

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstCompoundNode& e)
{
    throw std::runtime_error("smtAstCompoundNode not implemented");
}

void Z3ast::operator()(smt2lib::smtAstConcatNode& e)
{
    std::vector<smt2lib::smtAstAbstractNode*> childs = e.getChilds();

    uint64 idx;

    z3::expr nextValue(this->result.getContext());
    z3::expr currentValue = eval(*childs[0]).getExpr();

    //Child[0] is the LSB
    for (idx = 1; idx < childs.size(); idx++) {
        nextValue = eval(*childs[idx]).getExpr();
        currentValue = to_expr(this->result.getContext(), Z3_mk_concat(this->result.getContext(), currentValue, nextValue));
    }

    this->result.setExpr(currentValue);
}

void Z3ast::operator()(smt2lib::smtAstDecimalNode& e)
{
    z3::expr newexpr = this->result.getContext().int_val(e.getValue());
    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstDeclareNode& e)
{
    throw std::runtime_error("smtAstDeclareNode not implemented");
}

void Z3ast::operator()(smt2lib::smtAstEqualNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]);
    Z3Result op2 = this->eval(*e.getChilds()[1]);
    //z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_eq(this->result.getContext(), op1.getExpr(), op2.getExpr()));
    z3::expr newexpr = op1.getExpr() == op2.getExpr();

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstExtractNode& e)
{
    Z3Result high = this->eval(*e.getChilds()[0]);
    Z3Result low = this->eval(*e.getChilds()[1]);
    Z3Result value = this->eval(*e.getChilds()[2]);

    z3::expr newexpr = value.getExpr().extract(high.getUint64Value(), low.getUint64Value());
    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstIteNode& e)
{
    Z3Result op1 = this->eval(*e.getChilds()[0]); //condition
    Z3Result op2 = this->eval(*e.getChilds()[1]); //if true
    Z3Result op3 = this->eval(*e.getChilds()[2]); //if false

    z3::expr newexpr = z3::ite(op1.getExpr(), op2.getExpr(), op3.getExpr());

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstReferenceNode& e)
{
    throw std::runtime_error("smtAstReferenceNode not implemented");
}

void Z3ast::operator()(smt2lib::smtAstStringNode& e)
{
    throw std::runtime_error("smtAstStringNode not implemented");
}

void Z3ast::operator()(smt2lib::smtAstSxNode& e)
{
    Z3Result i = this->eval(*e.getChilds()[0]);
    Z3Result value = this->eval(*e.getChilds()[1]);

    z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_sign_ext(this->result.getContext(), i.getUint64Value(), value.getExpr()));

    this->result.setExpr(newexpr);
}

void Z3ast::operator()(smt2lib::smtAstZxNode& e)
{
    Z3Result i = this->eval(*e.getChilds()[0]);
    Z3Result value = this->eval(*e.getChilds()[1]);

    z3::expr newexpr = to_expr(this->result.getContext(), Z3_mk_zero_ext(this->result.getContext(), i.getUint64Value(), value.getExpr()));

    this->result.setExpr(newexpr);
}
