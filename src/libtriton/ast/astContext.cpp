//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <list>
#include <memory>
#include <vector>

#include <triton/ast.hpp>
#include <triton/astContext.hpp>
#include <triton/exceptions.hpp>
#include <triton/symbolicExpression.hpp>
#include <triton/symbolicVariable.hpp>



namespace triton {
  namespace ast {

    AstContext::AstContext(const triton::modes::SharedModes& modes)
      : modes(modes) {
    }


    AstContext::~AstContext() {
      this->valueMapping.clear();
      this->nodes.clear();
    }


    AstContext& AstContext::operator=(const AstContext& other) {
      std::enable_shared_from_this<AstContext>::operator=(other);

      this->astRepresentation = other.astRepresentation;
      this->modes             = other.modes;
      this->valueMapping      = other.valueMapping;
      this->nodes             = other.nodes;

      return *this;
    }


    SharedAbstractNode AstContext::collect(const SharedAbstractNode& node) {
      /*
       * We keep references to nodes which belong to a depth in the AST which is
       * a multiple of 10000. Thus, when the root node is destroyed, the stack recursivity
       * stops when the depth level of 10000 is reached, because the nodes there still
       * have a reference to them in the AST manager. The destruction will continue at the
       * next allocation of nodes and so on. So, it means that ASTs are destroyed by steps
       * of depth of 10000 which avoids the overflow while keeping a good scale.
       *
       * See: #753.
       */
      triton::uint32 lvl = node->getLevel();
      if (lvl != 0 && (lvl % 10000) == 0) {
        this->nodes.push_front(node);
      }
      return node;
    }


    void AstContext::garbage(void) {
      this->nodes.erase(std::remove_if(this->nodes.begin(), this->nodes.end(),
        [](const SharedAbstractNode& n) {
          return (n.use_count() == 1 ? true : false);
        }), this->nodes.end()
      );
    }


    SharedAbstractNode AstContext::assert_(const SharedAbstractNode& expr) {
      SharedAbstractNode node = std::make_shared<AssertNode>(expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::assert_(): Not enough memory.");
      node->init();
      return this->collect(node);
    }


    SharedAbstractNode AstContext::bv(const triton::uint512& value, triton::uint32 size) {
      SharedAbstractNode node = std::make_shared<BvNode>(value, size, this->shared_from_this());
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bv(): Not enough memory.");
      node->init();
      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvadd(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      if (this->modes->isModeEnabled(triton::modes::AST_OPTIMIZATIONS)) {
        /* Optimization: 0 + A = A */
        if (!expr1->isSymbolized() && expr1->evaluate() == 0)
          return expr2;

        /* Optimization: A + 0 = A */
        if (!expr2->isSymbolized() && expr2->evaluate() == 0)
          return expr1;
      }

      SharedAbstractNode node = std::make_shared<BvaddNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvadd(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvand(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      if (this->modes->isModeEnabled(triton::modes::AST_OPTIMIZATIONS)) {
        /* Optimization: 0 & A = 0 */
        if (!expr1->isSymbolized() && expr1->evaluate() == 0)
          return this->bv(0, expr1->getBitvectorSize());

        /* Optimization: A & 0 = 0 */
        if (!expr2->isSymbolized() && expr2->evaluate() == 0)
          return this->bv(0, expr1->getBitvectorSize());

        /* Optimization: A & -1 = A */
        if (!expr2->isSymbolized() && expr2->evaluate() == expr2->getBitvectorMask())
          return expr1;

        /* Optimization: -1 & A = A */
        if (!expr1->isSymbolized() && expr1->evaluate() == expr1->getBitvectorMask())
          return expr2;

        /* Optimization: A & A = A */
        if (!expr1->isSymbolized() && !expr2->isSymbolized() && expr1->equalTo(expr2))
          return expr1;
      }

      SharedAbstractNode node = std::make_shared<BvandNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvand(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvashr(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      if (this->modes->isModeEnabled(triton::modes::AST_OPTIMIZATIONS)) {
        /* Optimization: 0 >> A = 0 */
        if (!expr1->isSymbolized() && expr1->evaluate() == 0)
          return this->bv(0, expr1->getBitvectorSize());

        /* Optimization: A >> 0 = A */
        if (!expr2->isSymbolized() && expr2->evaluate() == 0)
          return expr1;
      }

      SharedAbstractNode node = std::make_shared<BvashrNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvashr(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvfalse(void) {
      SharedAbstractNode node = std::make_shared<BvNode>(0, 1, this->shared_from_this());
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvfalse(): Not enough memory.");
      node->init();
      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvlshr(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      if (this->modes->isModeEnabled(triton::modes::AST_OPTIMIZATIONS)) {
        /* Optimization: 0 >> A = 0 */
        if (!expr1->isSymbolized() && expr1->evaluate() == 0)
          return this->bv(0, expr1->getBitvectorSize());

        /* Optimization: A >> 0 = A */
        if (!expr2->isSymbolized() && expr2->evaluate() == 0)
          return expr1;

        /* Optimization: A >> B>=size(A) = 0 */
        if (!expr2->isSymbolized() && expr2->evaluate() >= expr1->getBitvectorSize())
          return this->bv(0, expr1->getBitvectorSize());
      }

      SharedAbstractNode node = std::make_shared<BvlshrNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvlshr(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvmul(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      if (this->modes->isModeEnabled(triton::modes::AST_OPTIMIZATIONS)) {
        /* Optimization: 0 * A = 0 */
        if (!expr1->isSymbolized() && expr1->evaluate() == 0)
          return this->bv(0, expr1->getBitvectorSize());

        /* Optimization: A * 0 = 0 */
        if (!expr2->isSymbolized() && expr2->evaluate() == 0)
          return this->bv(0, expr1->getBitvectorSize());
      }

      SharedAbstractNode node = std::make_shared<BvmulNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvmul(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvnand(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvnandNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvnand(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvneg(const SharedAbstractNode& expr) {
      SharedAbstractNode node = std::make_shared<BvnegNode>(expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvneg(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvnor(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvnorNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvnor(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvnot(const SharedAbstractNode& expr) {
      SharedAbstractNode node = std::make_shared<BvnotNode>(expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvnot(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvor(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      if (this->modes->isModeEnabled(triton::modes::AST_OPTIMIZATIONS)) {
        /* Optimization: 0 | A = A */
        if (!expr1->isSymbolized() && expr1->evaluate() == 0)
          return expr2;

        /* Optimization: A | 0 = A */
        if (!expr2->isSymbolized() && expr2->evaluate() == 0)
          return expr1;

        /* Optimization: -1 | A = -1 */
        if (!expr1->isSymbolized() && expr1->evaluate() == expr1->getBitvectorMask())
          return this->bv(expr1->getBitvectorMask(), expr1->getBitvectorSize());

        /* Optimization: A | -1 = -1 */
        if (!expr2->isSymbolized() && expr2->evaluate() == expr2->getBitvectorMask())
          return this->bv(expr2->getBitvectorMask(), expr2->getBitvectorSize());

        /* Optimization: A | A = A */
        if (expr1->equalTo(expr2))
          return expr1;
      }

      SharedAbstractNode node = std::make_shared<BvorNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvor(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvrol(const SharedAbstractNode& expr, triton::uint32 rot) {
      SharedAbstractNode node = std::make_shared<BvrolNode>(expr, rot);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvrol(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvrol(const SharedAbstractNode& expr, const SharedAbstractNode& rot) {
      /*
       * If the mode SYMBOLIZE_INDEX_ROTATION we apply a AST transformation
       * in order to make index rotation symbolic. Note that this mode increases the
       * complexity of solving.
       *
       * bvrol(rot, expr) = ((expr << (rot % size)) | (expr >> (size - (rot % size))))
       **/
      if (this->modes->isModeEnabled(triton::modes::SYMBOLIZE_INDEX_ROTATION)) {
        auto size        = expr->getBitvectorSize();
        auto bvsize      = this->bv(size, size);
        const auto& node = this->bvor(
                             this->bvshl(expr, this->bvsmod(rot, bvsize)),
                             this->bvlshr(expr, this->bvsub(bvsize, this->bvsmod(rot, bvsize)))
                           );
        return node;
      }

      /* Otherwise, we concretize the index rotation */
      SharedAbstractNode node = std::make_shared<BvrolNode>(expr, this->integer(rot->evaluate()));
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvrol(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvror(const SharedAbstractNode& expr, triton::uint32 rot) {
      SharedAbstractNode node = std::make_shared<BvrorNode>(expr, rot);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvror(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvror(const SharedAbstractNode& expr, const SharedAbstractNode& rot) {
      /*
       * If the mode SYMBOLIZE_INDEX_ROTATION we apply a AST transformation
       * in order to make index rotation symbolic. Note that this mode increases the
       * complexity of solving.
       *
       * bvror(rot, expr) = ((value >> (rot % size)) | (value << (size - (rot % size))))
       **/
      if (this->modes->isModeEnabled(triton::modes::SYMBOLIZE_INDEX_ROTATION)) {
        auto size        = expr->getBitvectorSize();
        auto bvsize      = this->bv(size, size);
        const auto& node = this->bvor(
                             this->bvlshr(expr, this->bvsmod(rot, bvsize)),
                             this->bvshl(expr, this->bvsub(bvsize, this->bvsmod(rot, bvsize)))
                           );
        return node;
      }

      /* Otherwise, we concretize the index rotation */
      SharedAbstractNode node = std::make_shared<BvrorNode>(expr, this->integer(rot->evaluate()));
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvror(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvsdiv(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      if (this->modes->isModeEnabled(triton::modes::AST_OPTIMIZATIONS)) {
        /* Optimization: A / 1 = A */
        if (!expr2->isSymbolized() && expr2->evaluate() == 1)
          return expr1;
      }

      SharedAbstractNode node = std::make_shared<BvsdivNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvsdiv(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvsge(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvsgeNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvsge(): Not enough memory.");
      node->init();
      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvsgt(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvsgtNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvsgt(): Not enough memory.");
      node->init();
      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvshl(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      if (this->modes->isModeEnabled(triton::modes::AST_OPTIMIZATIONS)) {
        /* Optimization: 0 << A = 0 */
        if (!expr1->isSymbolized() && expr1->evaluate() == 0)
          return this->bv(0, expr1->getBitvectorSize());

        /* Optimization: A << 0 = A */
        if (!expr2->isSymbolized() && expr2->evaluate() == 0)
          return expr1;

        /* Optimization: A << B>=size(A) = 0 */
        if (!expr2->isSymbolized() && expr2->evaluate() >= expr1->getBitvectorSize())
          return this->bv(0, expr1->getBitvectorSize());
      }

      SharedAbstractNode node = std::make_shared<BvshlNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvshl(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvsle(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvsleNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvsle(): Not enough memory.");
      node->init();
      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvslt(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvsltNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvslt(): Not enough memory.");
      node->init();
      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvsmod(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvsmodNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvsmod(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvsrem(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvsremNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvsrem(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvsub(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      if (this->modes->isModeEnabled(triton::modes::AST_OPTIMIZATIONS)) {
        /* Optimization: A - 0 = A */
        if (!expr2->isSymbolized() && expr2->evaluate() == 0)
          return expr1;

        /* Optimization: 0 - A = -A */
        if (!expr1->isSymbolized() && expr1->evaluate() == 0)
          return this->bvneg(expr2);

        /* Optimization: A - A = 0 */
        if (expr1->equalTo(expr2))
          return this->bv(0, expr1->getBitvectorSize());
      }

      SharedAbstractNode node = std::make_shared<BvsubNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvsub(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvtrue(void) {
      SharedAbstractNode node = std::make_shared<BvNode>(1, 1, this->shared_from_this());
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvtrue(): Not enough memory.");
      node->init();
      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvudiv(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      if (this->modes->isModeEnabled(triton::modes::AST_OPTIMIZATIONS)) {
        /* Optimization: A / 1 = A */
        if (!expr2->isSymbolized() && expr2->evaluate() == 1)
          return expr1;
      }

      SharedAbstractNode node = std::make_shared<BvudivNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvudiv(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvuge(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvugeNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvuge(): Not enough memory.");
      node->init();
      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvugt(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvugtNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvugt(): Not enough memory.");
      node->init();
      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvule(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvuleNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvule(): Not enough memory.");
      node->init();
      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvult(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvultNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvult(): Not enough memory.");
      node->init();
      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvurem(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvuremNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvurem(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


     SharedAbstractNode AstContext::bvxnor(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvxnorNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvxnor(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    SharedAbstractNode AstContext::bvxor(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      if (this->modes->isModeEnabled(triton::modes::AST_OPTIMIZATIONS)) {
        /* Optimization: A ^ 0 = A */
        if (!expr2->isSymbolized() && expr2->evaluate() == 0)
          return expr1;

        /* Optimization: 0 ^ A = A */
        if (!expr1->isSymbolized() && expr1->evaluate() == 0)
          return expr2;

        /* Optimization: A ^ A = 0 */
        if (expr1->equalTo(expr2))
          return this->bv(0, expr1->getBitvectorSize());
      }

      SharedAbstractNode node = std::make_shared<BvxorNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::bvxor(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    template TRITON_EXPORT SharedAbstractNode AstContext::compound(const std::vector<SharedAbstractNode>& exprs);
    template TRITON_EXPORT SharedAbstractNode AstContext::compound(const std::list<SharedAbstractNode>& exprs);


    SharedAbstractNode AstContext::concat(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<ConcatNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::concat(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    template TRITON_EXPORT SharedAbstractNode AstContext::concat(const std::vector<SharedAbstractNode>& exprs);
    template TRITON_EXPORT SharedAbstractNode AstContext::concat(const std::list<SharedAbstractNode>& exprs);


    SharedAbstractNode AstContext::declare(const SharedAbstractNode& var) {
      SharedAbstractNode node = std::make_shared<DeclareNode>(var);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::declare(): Not enough memory.");
      node->init();
      return this->collect(node);
    }


    SharedAbstractNode AstContext::distinct(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<DistinctNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::distinct(): Not enough memory.");
      node->init();
      return this->collect(node);
    }


    SharedAbstractNode AstContext::equal(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<EqualNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::equal(): Not enough memory.");
      node->init();
      return this->collect(node);
    }


    SharedAbstractNode AstContext::extract(triton::uint32 high, triton::uint32 low, const SharedAbstractNode& expr) {
      auto node = expr;
      auto size = expr->getBitvectorSize();

      /* Optimization: If we extract the full size of expr, just return expr */
      if (low == 0 && (high + 1) == size)
        return expr;

      if (this->modes->isModeEnabled(triton::modes::AST_OPTIMIZATIONS) &&
          high > low && high < size) {
        while (true) {
          auto n = node;
          while (n->getType() == REFERENCE_NODE) {
            auto ref = reinterpret_cast<ReferenceNode*>(n.get());
            n = ref->getSymbolicExpression()->getAst();
          }
          if (n->getType() == CONCAT_NODE) {
            /* Optimization: If we extract the full part of concatenation, just
             * return the part */
            auto hi = n->getBitvectorSize() - 1;
            bool found = false;
            for (const auto& part : n->getChildren()) {
              if (hi < high) {
                break;
              }
              auto sz = part->getBitvectorSize();
              auto lo = hi + 1 - sz;
              if (hi == high && lo == low) {
                return part;
              }
              if (hi >= high && lo <= low) {
                node = part;
                high -= lo;
                low -= lo;
                found = true;
                break;
              }
              hi -= sz;
            }
            if (found) {
              continue;
            }
          }
          else if (n->getType() == ZX_NODE || n->getType() == SX_NODE) {
            /* Optimization: If we extract from the node being extended, just
             * return the node */
            n = n->getChildren()[1];
            auto sz = n->getBitvectorSize();
            if (low == 0 && high + 1 == sz) {
              return n;
            }
            if (high < sz) {
              node = n;
              continue;
            }
          }
          break;
        }

        /* Optimization: extract from extract is one extract */
        auto n = node;
        while (n->getType() == REFERENCE_NODE) {
          auto ref = reinterpret_cast<ReferenceNode*>(n.get());
          n = ref->getSymbolicExpression()->getAst();
        }
        if (n->getType() == EXTRACT_NODE) {
          const auto& childs = n->getChildren();
          auto hi = reinterpret_cast<IntegerNode*>(childs[0].get())->getInteger().convert_to<triton::uint32>();
          auto lo = reinterpret_cast<IntegerNode*>(childs[1].get())->getInteger().convert_to<triton::uint32>();
          if (lo + high <= hi) {
            node = childs[2];
            high += lo;
            low += lo;
          }
        }
      }

      node = std::make_shared<ExtractNode>(high, low, node);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::extract(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    template TRITON_EXPORT SharedAbstractNode AstContext::forall(const std::vector<SharedAbstractNode>& exprs, const SharedAbstractNode& body);
    template TRITON_EXPORT SharedAbstractNode AstContext::forall(const std::list<SharedAbstractNode>& exprs, const SharedAbstractNode& body);


    SharedAbstractNode AstContext::iff(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<IffNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::iff(): Not enough memory.");
      node->init();
      return this->collect(node);
    }


    SharedAbstractNode AstContext::integer(const triton::uint512& value) {
      SharedAbstractNode node = std::make_shared<IntegerNode>(value, this->shared_from_this());
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::integer(): Not enough memory.");
      node->init();
      return this->collect(node);
    }


    SharedAbstractNode AstContext::ite(const SharedAbstractNode& ifExpr, const SharedAbstractNode& thenExpr, const SharedAbstractNode& elseExpr) {
      SharedAbstractNode node = std::make_shared<IteNode>(ifExpr, thenExpr, elseExpr);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::ite(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false && node->isLogical() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    SharedAbstractNode AstContext::land(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<LandNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::land(): Not enough memory.");
      node->init();
      return this->collect(node);
    }


    template TRITON_EXPORT SharedAbstractNode AstContext::land(const std::vector<SharedAbstractNode>& exprs);
    template TRITON_EXPORT SharedAbstractNode AstContext::land(const std::list<SharedAbstractNode>& exprs);


    SharedAbstractNode AstContext::let(std::string alias, const SharedAbstractNode& expr2, const SharedAbstractNode& expr3) {
      SharedAbstractNode node = std::make_shared<LetNode>(alias, expr2, expr3);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::let(): Not enough memory.");
      node->init();
      return this->collect(node);
    }


    SharedAbstractNode AstContext::lnot(const SharedAbstractNode& expr) {
      SharedAbstractNode node = std::make_shared<LnotNode>(expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::lnot(): Not enough memory.");
      node->init();
      return this->collect(node);
    }


    SharedAbstractNode AstContext::lor(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<LorNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::lor(): Not enough memory.");
      node->init();
      return this->collect(node);
    }


    template TRITON_EXPORT SharedAbstractNode AstContext::lor(const std::vector<SharedAbstractNode>& exprs);
    template TRITON_EXPORT SharedAbstractNode AstContext::lor(const std::list<SharedAbstractNode>& exprs);


    SharedAbstractNode AstContext::lxor(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<LxorNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::lxor(): Not enough memory");
      node->init();
      return this->collect(node);
    }


    template TRITON_EXPORT SharedAbstractNode AstContext::lxor(const std::vector<SharedAbstractNode>& exprs);
    template TRITON_EXPORT SharedAbstractNode AstContext::lxor(const std::list<SharedAbstractNode>& exprs);


    SharedAbstractNode AstContext::reference(const triton::engines::symbolic::SharedSymbolicExpression& expr) {
      SharedAbstractNode node = std::make_shared<ReferenceNode>(expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::reference(): Not enough memory.");
      node->init();
      return this->collect(node);
    }


    SharedAbstractNode AstContext::string(std::string value) {
      SharedAbstractNode node = std::make_shared<StringNode>(value, this->shared_from_this());
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::string(): Not enough memory.");
      node->init();
      return this->collect(node);
    }


    SharedAbstractNode AstContext::sx(triton::uint32 sizeExt, const SharedAbstractNode& expr) {
      /* Optimization: Just return expr if the extend is zero */
      if (sizeExt == 0)
        return expr;

      SharedAbstractNode node = std::make_shared<SxNode>(sizeExt, expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::sx(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    SharedAbstractNode AstContext::variable(const triton::engines::symbolic::SharedSymbolicVariable& symVar) {
      // try to get node from variable pool
      auto it = this->valueMapping.find(symVar->getName());
      if (it != this->valueMapping.end()) {
        if (auto node = it->second.first.lock()) {
          if (node->getBitvectorSize() != symVar->getSize()) {
            throw triton::exceptions::Ast("AstContext::variable(): Missmatching variable size.");
          }
          // This node already exist, just return it
          return node;
        }
        throw triton::exceptions::Ast("AstContext::variable(): This symbolic variable is dead.");
      }
      else {
        // if not found, create a new variable node
        SharedAbstractNode node = std::make_shared<VariableNode>(symVar, this->shared_from_this());
        this->initVariable(symVar->getName(), 0, node);
        if (node == nullptr) {
          throw triton::exceptions::Ast("AstContext::variable(): Not enough memory");
        }
        node->init();
        return this->collect(node);
      }
    }


    SharedAbstractNode AstContext::zx(triton::uint32 sizeExt, const SharedAbstractNode& expr) {
      /* Optimization: Just return expr if the extend is zero */
      if (sizeExt == 0)
        return expr;

      SharedAbstractNode node = std::make_shared<ZxNode>(sizeExt, expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("AstContext::zx(): Not enough memory.");
      node->init();

      if (this->modes->isModeEnabled(triton::modes::CONSTANT_FOLDING)) {
        if (node->isSymbolized() == false) {
          return this->bv(node->evaluate(), node->getBitvectorSize());
        }
      }

      return this->collect(node);
    }


    void AstContext::initVariable(const std::string& name, const triton::uint512& value, const SharedAbstractNode& node) {
      auto it = this->valueMapping.find(name);
      if (it == this->valueMapping.end()) {
        this->valueMapping.insert(std::make_pair(name, std::make_pair(node, value)));
      }
      else {
        throw triton::exceptions::Ast("AstContext::initVariable(): Ast variable already initialized.");
      }
    }


    void AstContext::updateVariable(const std::string& name, const triton::uint512& value) {
      auto it = this->valueMapping.find(name);
      if (it != this->valueMapping.end()) {
        if (auto node = it->second.first.lock()) {
          it->second.second = value;
          node->initParents();
        }
        else {
          throw triton::exceptions::Ast("AstContext::updateVariable(): This symbolic variable is dead.");
        }
      }
      else {
        throw triton::exceptions::Ast("AstContext::updateVariable(): This symbolic variable is not assigned at any AbstractNode or does not exist.");
      }
    }


    SharedAbstractNode AstContext::getVariableNode(const std::string& name) {
      auto it = this->valueMapping.find(name);
      if (it != this->valueMapping.end()) {
        if (auto node = it->second.first.lock())
          return node;
        else
          throw triton::exceptions::Ast("AstContext::getVariableNode(): This symbolic variable is dead.");
      }

      return nullptr;
    }


    const triton::uint512& AstContext::getVariableValue(const std::string& name) const {
      auto it = this->valueMapping.find(name);
      if (it != this->valueMapping.end()) {
        if (auto node = it->second.first.lock())
          return it->second.second;
        else
          throw triton::exceptions::Ast("AstContext::getVariableValue(): This symbolic variable is dead.");
      }

      throw triton::exceptions::Ast("AstContext::updateVariable(): Variable does not exist.");
    }


    void AstContext::setRepresentationMode(triton::uint32 mode) {
      this->astRepresentation.setMode(mode);
    }


    triton::uint32 AstContext::getRepresentationMode(void) const {
      return this->astRepresentation.getMode();
    }


    std::ostream& AstContext::print(std::ostream& stream, AbstractNode* node) {
      return this->astRepresentation.print(stream, node);
    }

  }; /* ast namespace */
}; /* triton namespace */
