/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>

#include <pin.H>
#include <BaseIRBuilder.h>



BaseIRBuilder::BaseIRBuilder(__uint address, const std::string &dis) {
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


__uint BaseIRBuilder::getThreadID(void) const {
  return this->threadId;
}


void BaseIRBuilder::setOpcode(uint32 op) {
  this->opcode = op;
}


void BaseIRBuilder::setNextAddress(__uint nextAddress) {
  this->nextAddress = nextAddress;
}


void BaseIRBuilder::setBranchTaken(bool flag) {
  this->branchTaken = flag;
}


void BaseIRBuilder::setBranchTargetAddress(__uint addr) {
  this->branchTargetAddress = addr;
}


void BaseIRBuilder::setOpcodeCategory(sint32 category) {
  this->opcodeCategory = category;
}


void BaseIRBuilder::setThreadID(__uint threadId) {
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


__uint BaseIRBuilder::getAddress(void) const {
  return this->address;
}


__uint BaseIRBuilder::getBaseAddress(void) const {
  return this->baseAddress;
}


__uint BaseIRBuilder::getBranchTargetAddress(void) const {
  return this->branchTargetAddress;
}


__uint BaseIRBuilder::getNextAddress(void) const {
  return this->nextAddress;
}


__uint BaseIRBuilder::getOffset(void) const {
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


void BaseIRBuilder::setup(__uint mem_value) {
  for (auto it = this->operands.begin(); it != this->operands.end(); ++it) {
    if (IRBuilder::isMemOperand(it->getType())) {
      it->setMemAddress(mem_value);
      this->needSetup = false;
    }
  }
}


void BaseIRBuilder::checkSetup(void) const {
  if (this->needSetup)
    throw std::runtime_error("Error: IRBuilder.setup must be call before "
                             "IRBuilder.process, when there are MEM_* operands.");
}

