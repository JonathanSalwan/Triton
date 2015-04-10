
#include "Inst.h"
#include "xed-category-enum.h"


Inst::Inst(uint64_t threadId, uint64_t address, const std::string &insDis):
  threadId(threadId), address(address), disassembly(insDis)
{
}


Inst::~Inst()
{
}


/* Returns the instruction assembly */
const std::string &Inst::getDisassembly(void)
{
  return this->disassembly;
}


/* Returns the instruction address */
uint64_t Inst::getAddress(void)
{
  return this->address;
}


/* Returns the thread ID of the instruction */
uint64_t Inst::getThreadId(void)
{
  return this->threadId;
}


/* Returns the opcode of the instruction */
uint32_t Inst::getOpcode(void)
{
  return this->opcode;
}


/* Get the opcode category of the instruction */
int32_t Inst::getOpcodeCategory(void)
{
  return this->opcodeCategory;
}


/* Set the opcode of the instruction */
void Inst::setOpcode(uint32_t op)
{
  this->opcode = op;
}


/* Set the opcode category of the instruction */
void Inst::setOpcodeCategory(int32_t category)
{
  this->opcodeCategory = category;
}


/* Returns true of false if it's a branch instruction */
bool Inst::isBranch(void)
{
  return (this->opcodeCategory == XED_CATEGORY_COND_BR);
}


/* Returns the operands vector */
const std::vector< std::tuple<IRBuilderOperand::operand_t, uint64_t, uint32_t> > &Inst::getOperands(void)
{
  return this->operands;
}


/* Set the operands vector */
void Inst::setOperands(const std::vector< std::tuple<IRBuilderOperand::operand_t, uint64_t, uint32_t> > &operands)
{
  this->operands = operands;
}


/* Adds a new symbolic element */
void Inst::addElement(SymbolicElement *se)
{
  this->symbolicElements.push_back(se);
}


/* Returns the elements list */
const std::list<SymbolicElement*> &Inst::getSymbolicElements(void)
{
  return this->symbolicElements;
}


/* Returns the number of elements */
size_t Inst::numberOfElements(void)
{
  return this->symbolicElements.size();
}

