/*
** Copyright (C) - Triton
** This program is under the terms of the Apache License 2.0.
*/

#include <cstdio>
#include <memory>
#include <stdexcept>
#include <utility>

#include <triton/ast.hpp>
#include <triton/astContext.hpp>
#include <triton/context.hpp>
#include <triton/symbolicExpression.hpp>

namespace {

  struct AllocationCounts {
    unsigned allocated = 0;
    unsigned deallocated = 0;
    unsigned destroyed = 0;
  };

  template <typename T>
  struct CountingAllocator {
    using value_type = T;
    AllocationCounts* counts;

    explicit CountingAllocator(AllocationCounts& counts) : counts(&counts) {
    }

    template <typename U>
    CountingAllocator(const CountingAllocator<U>& other) : counts(other.counts) {
    }

    T* allocate(std::size_t size) {
      T* ptr = std::allocator<T>{}.allocate(size);
      ++counts->allocated;
      return ptr;
    }

    void deallocate(T* ptr, std::size_t size) {
      ++counts->deallocated;
      std::allocator<T>{}.deallocate(ptr, size);
    }

    template <typename U>
    bool operator==(const CountingAllocator<U>& other) const {
      return counts == other.counts;
    }

    template <typename U>
    bool operator!=(const CountingAllocator<U>& other) const {
      return !(*this == other);
    }
  };

  template <typename Node>
  struct TrackedNode : Node {
    AllocationCounts& counts;

    template <typename... Args>
    TrackedNode(AllocationCounts& counts, Args&&... args)
      : Node(std::forward<Args>(args)...), counts(counts) {
    }

    ~TrackedNode() override {
      ++counts.destroyed;
    }
  };

  template <typename Node, typename... Args>
  std::shared_ptr<TrackedNode<Node>> tracked(AllocationCounts& counts, Args&&... args) {
    using T = TrackedNode<Node>;
    return std::allocate_shared<T>(CountingAllocator<T>(counts), counts,
                                   std::forward<Args>(args)...);
  }

  void require(bool condition, const char* message) {
    if (!condition) {
      throw std::runtime_error(message);
    }
  }

  void requireReleased(const AllocationCounts& counts) {
    require(counts.allocated > 0, "allocate_shared did not use the tracking allocator");
    require(counts.destroyed == 1, "AST node destructor did not run");
    require(counts.deallocated == counts.allocated,
            "destroyed AST node's allocation is retained while its child is alive");
  }

  void testParentRelease() {
    AllocationCounts counts;
    triton::Context ctx(triton::arch::ARCH_X86_64);
    auto ast = ctx.getAstContext();
    auto var = ast->variable(ctx.newSymbolicVariable(64));
    {
      auto node = tracked<triton::ast::BvxorNode>(counts, var, ast->bv(1, 64));
      node->init();
    }
    // Do not call getParents(): it would hide delayed control-block reclamation.
    requireReleased(counts);
  }

  void testRepeatedChildAndInit() {
    AllocationCounts counts;
    triton::Context ctx(triton::arch::ARCH_X86_64);
    auto ast = ctx.getAstContext();
    auto sym = ctx.newSymbolicVariable(64);
    auto var = ast->variable(sym);
    auto survivor = ast->bvxor(var, ast->bv(1, 64));
    {
      auto node = tracked<triton::ast::BvaddNode>(counts, var, var);
      node->init();
      node->init();
      node->init();
    }
    requireReleased(counts);
    ctx.setConcreteVariableValue(sym, 7);
    require(survivor->evaluate() == 6, "surviving parent lost its variable dependency");
  }

  void testReplacingOneRepeatedChild() {
    AllocationCounts counts;
    triton::Context ctx(triton::arch::ARCH_X86_64);
    auto ast = ctx.getAstContext();
    auto sym = ctx.newSymbolicVariable(64);
    auto var = ast->variable(sym);
    auto replacement = ast->bv(3, 64);
    {
      auto node = tracked<triton::ast::BvaddNode>(counts, var, var);
      node->init();
      node->setChild(0, replacement);
      ctx.setConcreteVariableValue(sym, 7);
      require(node->evaluate() == 10, "replacing one child removed the remaining dependency");
    }
    requireReleased(counts);
  }

  void testSharedIntermediateChild() {
    AllocationCounts counts;
    triton::Context ctx(triton::arch::ARCH_X86_64);
    auto ast = ctx.getAstContext();
    auto var = ast->variable(ctx.newSymbolicVariable(64));
    auto shared = ast->bvadd(var, ast->bv(2, 64));
    {
      auto node = tracked<triton::ast::BvxorNode>(counts, shared, shared);
      node->init();
    }
    requireReleased(counts);
    require(shared->evaluate() == 2, "shared child was invalidated");
  }

  void testInvalidChildDuringDestruction() {
    AllocationCounts counts;
    triton::Context ctx(triton::arch::ARCH_X86_64);
    auto ast = ctx.getAstContext();
    auto var = ast->variable(ctx.newSymbolicVariable(64));
    {
      auto node = tracked<triton::ast::BvaddNode>(counts, var, var);
      node->init();
      node->getChildren()[1].reset();
    }
    requireReleased(counts);
  }

  void testCopiesAndReferences() {
    triton::Context ctx(triton::arch::ARCH_X86_64);
    auto ast = ctx.getAstContext();
    auto sym = ctx.newSymbolicVariable(64);
    auto var = ast->variable(sym);
    auto expression = ctx.newSymbolicExpression(ast->bvadd(var, ast->bv(2, 64)));
    auto reference = ast->reference(expression);
    auto original = ast->bvxor(reference, var);
    auto duplicate = triton::ast::newInstance(expression->getAst().get());
    auto unrolled = triton::ast::unroll(original);
    for (unsigned i = 0; i < 100; ++i) {
      auto temporary = triton::ast::unroll(original);
    }
    ctx.setConcreteVariableValue(sym, 7);
    require(original->evaluate() == 14, "original AST no longer follows its variable");
    require(duplicate->evaluate() == 9, "duplicate AST no longer follows its variable");
    require(unrolled->evaluate() == 14, "unrolled AST no longer follows its variable");
    expression->setAst(ast->bvadd(var, ast->bv(4, 64)));
    require(original->evaluate() == 12, "reference no longer follows expression replacement");
    require(duplicate->evaluate() == 9, "expression replacement modified the duplicate AST");
    require(unrolled->evaluate() == 14, "expression replacement modified the unrolled AST");
  }

} // namespace

int main() {
  const struct {
    const char* name;
    void (*run)();
  } tests[] = {
    {"parent allocation release", testParentRelease},
    {"repeated child and init", testRepeatedChildAndInit},
    {"replace one repeated child", testReplacingOneRepeatedChild},
    {"shared intermediate child", testSharedIntermediateChild},
    {"null child during destruction", testInvalidChildDuringDestruction},
    {"copies and references", testCopiesAndReferences},
  };
  unsigned failed = 0;
  for (const auto& test : tests) {
    try {
      test.run();
      std::printf("PASS: %s\n", test.name);
    }
    catch (const std::exception& error) {
      ++failed;
      std::printf("FAIL: %s: %s\n", test.name, error.what());
    }
  }
  std::printf("%u/%zu tests passed\n", static_cast<unsigned>(sizeof(tests) / sizeof(tests[0])) - failed,
              sizeof(tests) / sizeof(tests[0]));
  return failed ? 1 : 0;
}
