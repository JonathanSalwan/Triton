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
#include <triton/api.hpp>
#include <triton/x86Specifications.hpp>

using namespace triton;
using namespace triton::arch;


struct op {
  unsigned int    addr;
  unsigned char*  inst;
  unsigned int    size;
};

struct op trace[] = {
  {0x400017, (unsigned char *)"\x48\x35\x44\x33\x22\x11", 6}, /* xor rax, 0x11223344 */
  {0x0,      nullptr,                                     0}
};



int main(int ac, const char **av) {

  triton::API api;
  /* Set the arch */
  api.setArchitecture(ARCH_X86_64);

  /* Build an instruction */
  Instruction inst;

  /* Setup opcode */
  inst.setOpcode(trace[0].inst, trace[0].size);

  /* Define RAX as symbolic variable */
  api.convertRegisterToSymbolicVariable(triton::arch::Register(api.getRegister(ID_REG_RAX)));

  /* Process everything */
  api.processing(inst);

  /* Get the RAX symbolic ID */
  auto raxSymId = api.getSymbolicRegisterId(api.getRegister(ID_REG_RAX));

  /* Get the RAX full AST */
  auto raxFullAst = api.getFullAstFromId(raxSymId);

  /* Display RAX's AST*/
  std::cout << "RAX expr: " << raxFullAst << std::endl;

  /* Get the context to create and ast constraint*/
  auto& C = api.getAstContext();

  /* Modify RAX's AST to build the constraint */
  auto constraint = C.equal(raxFullAst, C.bv(0, raxFullAst->getBitvectorSize()));

  /* Display the AST */
  std::cout << "constraint: " << constraint << std::endl;

  /* Ask a model */
  auto model = api.getModel(constraint);

  /* Display all symbolic variable value contained in the model */
  std::cout << "Model:" << std::endl;
  for (auto it = model.begin(); it != model.end(); it++) {
    std::cout << "  - Variable id  : " << it->first << std::endl;
    std::cout << "  - Variable name: " << it->second.getName() << std::endl;
    std::cout << "  - Value        : " << std::hex << it->second.getValue() << std::endl;
  }

  return 0;
}

