/*
** Copyright (C) - Triton
** This program is under the terms of the Apache License 2.0.
*/

#include <cstdio>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

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

  /* A few instructions on symbolic registers; returns one line per symbolic expression (id, text, hash, value) */
  std::vector<std::string> runProgram(triton::Context& ctx) {
    const char* program[] = {
      "\x48\x01\xd8",          /* add rax, rbx */
      "\x48\x0f\xaf\xc1",      /* imul rax, rcx */
      "\x48\x31\xc3",          /* xor rbx, rax */
      "\x48\xc1\xe0\x03",      /* shl rax, 3 */
      "\x48\x89\x04\x24",      /* mov [rsp], rax */
      "\x48\x8b\x14\x24",      /* mov rdx, [rsp] */
      "\x48\x29\xda",          /* sub rdx, rbx */
    };
    const unsigned sizes[] = {3, 4, 3, 4, 4, 4, 3};

    ctx.setConcreteRegisterValue(ctx.registers.x86_rsp, 0x7000);
    ctx.symbolizeRegister(ctx.registers.x86_rax);
    ctx.symbolizeRegister(ctx.registers.x86_rbx);
    ctx.setConcreteRegisterValue(ctx.registers.x86_rcx, 0x1234);

    std::vector<std::string> lines;
    triton::uint64 pc = 0x1000;
    for (unsigned i = 0; i < sizeof(sizes) / sizeof(sizes[0]); i++) {
      triton::arch::Instruction inst(pc, reinterpret_cast<const triton::uint8*>(program[i]), sizes[i]);
      ctx.processing(inst);
      pc += sizes[i];
      for (const auto& expr : inst.symbolicExpressions) {
        std::ostringstream line;
        line << expr->getId() << " " << expr->getAst().get() << " " << expr->getAst()->getHash() << " " << expr->getAst()->evaluate();
        lines.push_back(line.str());
      }
    }
    return lines;
  }

  std::string describe(const triton::ast::SharedAbstractNode& node) {
    std::ostringstream text;
    text << node.get() << " " << node->getHash() << " " << node->evaluate();
    return text.str();
  }

  void testNodesOutliveContext() {
    triton::ast::SharedAbstractNode node;
    std::string before;
    {
      triton::Context ctx(triton::arch::ARCH_X86_64);
      runProgram(ctx);
      node = ctx.getSymbolicRegister(ctx.registers.x86_rdx)->getAst();
      before = describe(node);
    }
    require(describe(node) == before, "AST changed after its context was destroyed");
    require(node->getChildren().size() == 2, "AST lost its children after its context was destroyed");
    /* The last reference to the AST context goes away with this node */
    node.reset();
  }

  void testNodesSurviveReset() {
    triton::Context ctx(triton::arch::ARCH_X86_64);
    runProgram(ctx);
    auto node = ctx.getSymbolicRegister(ctx.registers.x86_rdx)->getAst();
    auto before = describe(node);
    ctx.reset();
    require(describe(node) == before, "AST changed after its context was reset");
    runProgram(ctx);
    require(describe(node) == before, "AST changed after its context was reused");
  }

  void testInterleavedContexts() {
    std::vector<triton::ast::SharedAbstractNode> nodes;
    std::vector<std::string> before;
    for (unsigned i = 0; i < 50; i++) {
      triton::Context ctx(triton::arch::ARCH_X86_64);
      runProgram(ctx);
      nodes.push_back(ctx.getSymbolicRegister(ctx.registers.x86_rdx)->getAst());
      before.push_back(describe(nodes.back()));
      if (i % 3 == 0 && nodes.size() > 1) {
        nodes.erase(nodes.begin());
        before.erase(before.begin());
      }
    }
    for (unsigned i = 0; i < nodes.size(); i++) {
      require(describe(nodes[i]) == before[i], "AST of a destroyed context changed while other contexts were used");
    }
    while (!nodes.empty()) {
      nodes.pop_back();
    }
  }

  void testSameTreesAfterChurn() {
    triton::Context first(triton::arch::ARCH_X86_64);
    auto expected = runProgram(first);
    for (unsigned i = 0; i < 20; i++) {
      triton::Context other(triton::arch::ARCH_X86_64);
      runProgram(other);
    }
    triton::Context second(triton::arch::ARCH_X86_64);
    require(runProgram(second) == expected, "the same program built different expressions");
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
    {"nodes outlive their context", testNodesOutliveContext},
    {"nodes survive a context reset", testNodesSurviveReset},
    {"interleaved contexts", testInterleavedContexts},
    {"same trees after allocation churn", testSameTreesAfterChurn},
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
