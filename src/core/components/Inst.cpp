/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <pin.H>
#include <Inst.h>
#include <IRBuilder.h>



Inst::Inst(__uint threadId, __uint address, const std::string &dis) {
  RTN rtn;
  SEC sec;
  IMG img;

  this->address             = address;
  this->branchTaken         = false;
  this->branchTargetAddress = 0;
  this->disassembly         = dis;
  this->nextAddress         = 0;
  this->threadId            = threadId;
  this->baseAddress         = 0;
  this->imageName           = "unknown";
  this->sectionName         = "unknown";

  rtn = RTN_FindByAddress(address);
  if (RTN_Valid(rtn)) {

    sec = RTN_Sec(rtn);
    if (SEC_Valid(sec)) {

      this->sectionName = SEC_Name(sec);

      img = SEC_Img(sec);
      if (IMG_Valid(img)) {
        this->baseAddress = IMG_LowAddress(img);
        this->imageName   = IMG_Name(img);
      }
    }
  }

  this->offset        = this->address - this->baseAddress;
  this->routineName   = RTN_FindNameByAddress(address);
  if (this->routineName.empty())
    this->routineName = "unknown";
}


Inst::~Inst() {
}


/* Returns the instruction assembly */
const std::string &Inst::getDisassembly(void) {
  return this->disassembly;
}


/* Returns the instruction address */
__uint Inst::getAddress(void) {
  return this->address;
}


/* Returns the next instruction address */
__uint Inst::getNextAddress(void) {
  return this->nextAddress;
}


/* If the instruction is a branch, this method returns the target address */
__uint Inst::getBranchTargetAddress(void) {
  return this->branchTargetAddress;
}


/* Returns the thread ID of the instruction */
__uint Inst::getThreadID(void) {
  return this->threadId;
}


/* Returns the opcode of the instruction */
uint32 Inst::getOpcode(void) {
  return this->opcode;
}


/* Get the opcode category of the instruction */
int32_t Inst::getOpcodeCategory(void) {
  return this->opcodeCategory;
}


/* Set the opcode of the instruction */
void Inst::setOpcode(uint32 op) {
  this->opcode = op;
}


/* Set the opcode category of the instruction */
void Inst::setOpcodeCategory(int32_t category) {
  this->opcodeCategory = category;
}


/* Set the next instruction address */
void Inst::setNextAddress(__uint addr) {
  this->nextAddress = addr;
}


/* Set the branch taken flag */
void Inst::setBranchTaken(bool flag) {
  this->branchTaken = flag;
}


/* Set the branch target address */
void Inst::setBranchTargetAddress(__uint addr) {
  this->branchTargetAddress = addr;
}


/* Returns true or false if it's a branch instruction */
bool Inst::isBranch(void) {
  return (this->opcodeCategory == XED_CATEGORY_COND_BR);
}


/* Returns true or false if the branch is taken */
bool Inst::isBranchTaken(void) {
  return this->branchTaken;
}


/* Returns the operands vector */
const std::vector<TritonOperand> &Inst::getOperands(void) {
  return this->operands;
}


/* Set the operands vector */
void Inst::setOperands(const std::vector<TritonOperand> &operands) {
  this->operands = operands;
}

#ifndef LIGHT_VERSION

/* Adds a new symbolic expression */
void Inst::addExpression(SymbolicExpression *se) {
  this->symbolicExpressions.push_back(se);
}


/* Returns the expressions list */
const std::list<SymbolicExpression*> &Inst::getSymbolicExpressions(void) {
  return this->symbolicExpressions;
}


/* Returns the number of expressions */
size_t Inst::numberOfExpressions(void) {
  return this->symbolicExpressions.size();
}

#endif

/* Returns the image name */
const std::string &Inst::getImageName(void) {
  return this->imageName;
}


/* Returns the section name */
const std::string &Inst::getSectionName(void) {
  return this->imageName;
}


/* Returns the routine name */
const std::string &Inst::getRoutineName(void) {
  return this->routineName;
}


/* Returns the base address */
__uint Inst::getBaseAddress(void) {
  return this->baseAddress;
}


/* Returns the offset of the instruction in the file */
__uint Inst::getOffset(void) {
  return this->offset;
}


/* Import Irb information to Inst */
void Inst::importIrbInformation(void *irbv) {
  IRBuilder *irb = reinterpret_cast<IRBuilder *>(irbv);
  this->setNextAddress(irb->getNextAddress());
  this->setOpcode(irb->getOpcode());
  this->setOpcodeCategory(irb->getOpcodeCategory());
  this->setOperands(irb->getOperands());
  this->setBranchTaken(irb->isBranchTaken());
  this->setBranchTargetAddress(irb->getBranchTargetAddress());
}

