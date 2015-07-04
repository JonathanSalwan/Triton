
#include <pin.H>
#include <Inst.h>


Inst::Inst(uint64 threadId, uint64 address, const std::string &dis)
{
  this->address     = address;
  this->baseAddress = IMG_LowAddress(SEC_Img(RTN_Sec(RTN_FindByAddress(address))));
  this->disassembly = dis;
  this->imageName   = IMG_Name(SEC_Img(RTN_Sec(RTN_FindByAddress(address))));
  this->offset      = this->address - this->baseAddress;
  this->routineName = RTN_FindNameByAddress(address);
  this->sectionName = SEC_Name(RTN_Sec(RTN_FindByAddress(address)));
  this->threadId    = threadId;
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
uint64 Inst::getAddress(void)
{
  return this->address;
}


/* Returns the thread ID of the instruction */
uint64 Inst::getThreadID(void)
{
  return this->threadId;
}


/* Returns the opcode of the instruction */
uint32 Inst::getOpcode(void)
{
  return this->opcode;
}


/* Get the opcode category of the instruction */
int32_t Inst::getOpcodeCategory(void)
{
  return this->opcodeCategory;
}


/* Set the opcode of the instruction */
void Inst::setOpcode(uint32 op)
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
const std::vector<TritonOperand> &Inst::getOperands(void)
{
  return this->operands;
}


/* Set the operands vector */
void Inst::setOperands(const std::vector<TritonOperand> &operands)
{
  this->operands = operands;
}


/* Adds a new symbolic expression */
void Inst::addExpression(SymbolicExpression *se)
{
  this->symbolicExpressions.push_back(se);
}


/* Returns the expressions list */
const std::list<SymbolicExpression*> &Inst::getSymbolicExpressions(void)
{
  return this->symbolicExpressions;
}


/* Returns the number of expressions */
size_t Inst::numberOfExpressions(void)
{
  return this->symbolicExpressions.size();
}


/* Returns the image name */
const std::string &Inst::getImageName(void)
{
  return this->imageName;
}


/* Returns the section name */
const std::string &Inst::getSectionName(void)
{
  return this->imageName;
}


/* Returns the routine name */
const std::string &Inst::getRoutineName(void)
{
  return this->routineName;
}


/* Returns the base address */
uint64 Inst::getBaseAddress(void)
{
  return this->baseAddress;
}


/* Returns the offset of the instruction in the file */
uint64 Inst::getOffset(void)
{
  return this->offset;
}

