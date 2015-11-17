/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>

#include <pin.H>
#include <BaseIRBuilder.h>



BaseIRBuilder::BaseIRBuilder(reg_size address, const std::string &dis) {
  RTN rtn;
  SEC sec;
  IMG img;

  this->address             = address;
  this->branchTaken         = false;
  this->branchTargetAddress = 0;
  this->disas               = dis;
  this->needSetup           = false;
  this->nextAddress         = 0;
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


uint32 BaseIRBuilder::getOpcode(void) const {
  return this->opcode;
}


reg_size BaseIRBuilder::getThreadID(void) const {
  return this->threadId;
}


void BaseIRBuilder::setOpcode(uint32 op) {
  this->opcode = op;
}


void BaseIRBuilder::setNextAddress(reg_size nextAddress) {
  this->nextAddress = nextAddress;
}


void BaseIRBuilder::setBranchTaken(bool flag) {
  this->branchTaken = flag;
}


void BaseIRBuilder::setBranchTargetAddress(reg_size addr) {
  this->branchTargetAddress = addr;
}


void BaseIRBuilder::setOpcodeCategory(sint32 category) {
  this->opcodeCategory = category;
}


void BaseIRBuilder::setThreadID(reg_size threadId) {
  this->threadId = threadId;
}


sint32 BaseIRBuilder::getOpcodeCategory(void) const {
  return this->opcodeCategory;
}


bool BaseIRBuilder::isBranch(void) {
  return (this->opcodeCategory == XED_CATEGORY_COND_BR);
}


bool BaseIRBuilder::isBranchTaken(void) {
  return this->branchTaken;
}


reg_size BaseIRBuilder::getAddress(void) const {
  return this->address;
}


reg_size BaseIRBuilder::getBaseAddress(void) const {
  return this->baseAddress;
}


reg_size BaseIRBuilder::getBranchTargetAddress(void) const {
  return this->branchTargetAddress;
}


reg_size BaseIRBuilder::getNextAddress(void) const {
  return this->nextAddress;
}


reg_size BaseIRBuilder::getOffset(void) const {
  return this->offset;
}


const std::string &BaseIRBuilder::getDisassembly(void) const {
  return this->disas;
}


const std::string &BaseIRBuilder::getImageName(void) const {
  return this->imageName;
}


const std::string &BaseIRBuilder::getSectionName(void) const {
  return this->imageName;
}


const std::string &BaseIRBuilder::getRoutineName(void) const {
  return this->routineName;
}


const std::vector<TritonOperand> &BaseIRBuilder::getOperands(void) const {
  return this->operands;
}


void BaseIRBuilder::addOperand(const TritonOperand &operand) {
  if (IRBuilder::isMemOperand(operand.getType()))
    this->needSetup = true;

  this->operands.push_back(operand);
}


void BaseIRBuilder::setup(reg_size mem_value) {
  for (auto it = this->operands.begin(); it != this->operands.end(); ++it)
    if (IRBuilder::isMemOperand(it->getType())) {
      it->setMemAddress(mem_value);
      this->needSetup = false;
      break;
    }
}


void BaseIRBuilder::checkSetup() const {
  if (this->needSetup)
    throw std::runtime_error("Error: IRBuilder.setup must be call before "
                             "IRBuilder.process, when there are MEM_* operands.");
}

