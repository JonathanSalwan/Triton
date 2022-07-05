/*
** Output:
**
**  RAX expr: (bvxor ((_ extract 63 0) SymVar_0) (_ bv287454020 64))
**  constraint: (= (bvxor ((_ extract 63 0) SymVar_0) (_ bv287454020 64)) (_ bv0 64))
**  Model:
**    - Variable id  : 0
**    - Variable name: SymVar_0
**    - Value        : 11223344
**
*/


#include <iostream>
#include <triton/context.hpp>
#include <triton/ast.hpp>
#include <triton/x86Specifications.hpp>

using namespace triton;
using namespace triton::arch;


struct op {
  unsigned int addr;
  const void*  inst;
  unsigned int size;
};

struct op trace[] = {
  {0x400017, "\x48\x35\x44\x33\x22\x11", 6}, /* xor rax, 0x11223344 */
  {0x0,      nullptr,                    0}
};



int main(int ac, const char **av) {
  triton::Context ctx;

  /* Set the arch */
  ctx.setArchitecture(ARCH_X86_64);

  /* Build an instruction */
  Instruction inst;

  /* Setup opcode */
  inst.setOpcode(trace[0].inst, trace[0].size);

  /* Define RAX as symbolic variable */
  ctx.symbolizeRegister(ctx.registers.x86_rax);

  /* Process everything */
  ctx.processing(inst);

  /* Get the RAX symbolic ID */
  auto raxSym = ctx.getSymbolicRegister(ctx.registers.x86_rax);

  /* Get the RAX full AST */
  auto raxFullAst = triton::ast::unroll(raxSym->getAst());

  /* Display RAX's AST*/
  std::cout << "RAX expr: " << raxFullAst << std::endl;

  /* Get the context to create and ast constraint*/
  auto ast = ctx.getAstContext();

  /* Modify RAX's AST to build the constraint */
  auto constraint = ast->equal(raxFullAst, ast->bv(0, raxFullAst->getBitvectorSize()));

  /* Display the AST */
  std::cout << "constraint: " << constraint << std::endl;

  /* Ask a model */
  auto model = ctx.getModel(constraint);

  /* Display all symbolic variable value contained in the model */
  std::cout << "Model:" << std::endl;
  for (auto it = model.begin(); it != model.end(); it++) {
    std::cout << "  - Variable id  : " << it->first << std::endl;
    std::cout << "  - Variable name: " << it->second.getVariable()->getName() << std::endl;
    std::cout << "  - Value        : " << std::hex << it->second.getValue() << std::endl;
  }

  return 0;
}

