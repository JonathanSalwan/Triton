//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <cstring>

#include <architecture.hpp>
#include <coreUtils.hpp>
#include <cpuSize.hpp>
#include <immediateOperand.hpp>
#include <x86Cpu.hpp>
#include <x86Specifications.hpp>

#ifdef __unix__
  #include <capstone/capstone.h>
#elif _WIN32
  #include <capstone.h>
#endif

#ifdef TRITON_PYTHON_BINDINGS
  #include <pythonBindings.hpp>
#endif



namespace triton {
  namespace arch {
    namespace x86 {

    x86Cpu::x86Cpu() {
      this->clear();
    }


    x86Cpu::x86Cpu(const x86Cpu& other) {
      this->copy(other);
    }


    x86Cpu::~x86Cpu() {
    }


    void x86Cpu::copy(const x86Cpu& other) {
      this->memory = other.memory;
      (*((triton::uint32*)(this->eax)))     = (*((triton::uint32*)(other.eax)));
      (*((triton::uint32*)(this->ebx)))     = (*((triton::uint32*)(other.ebx)));
      (*((triton::uint32*)(this->ecx)))     = (*((triton::uint32*)(other.ecx)));
      (*((triton::uint32*)(this->edx)))     = (*((triton::uint32*)(other.edx)));
      (*((triton::uint32*)(this->edi)))     = (*((triton::uint32*)(other.edi)));
      (*((triton::uint32*)(this->esi)))     = (*((triton::uint32*)(other.esi)));
      (*((triton::uint32*)(this->esp)))     = (*((triton::uint32*)(other.esp)));
      (*((triton::uint32*)(this->ebp)))     = (*((triton::uint32*)(other.ebp)));
      (*((triton::uint32*)(this->eip)))     = (*((triton::uint32*)(other.eip)));
      (*((triton::uint32*)(this->eflags)))  = (*((triton::uint32*)(other.eflags)));
      memcpy(this->xmm0, other.xmm0, sizeof(this->xmm0));
      memcpy(this->xmm1, other.xmm1, sizeof(this->xmm1));
      memcpy(this->xmm2, other.xmm2, sizeof(this->xmm2));
      memcpy(this->xmm3, other.xmm3, sizeof(this->xmm3));
      memcpy(this->xmm4, other.xmm4, sizeof(this->xmm4));
      memcpy(this->xmm5, other.xmm5, sizeof(this->xmm5));
      memcpy(this->xmm6, other.xmm6, sizeof(this->xmm6));
      memcpy(this->xmm7, other.xmm7, sizeof(this->xmm7));
    }


    void x86Cpu::init(void) {
      /* Define registers ========================================================= */
      triton::arch::x86::x86_reg_eax    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EAX);
      triton::arch::x86::x86_reg_ax     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_AX);
      triton::arch::x86::x86_reg_ah     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_AH);
      triton::arch::x86::x86_reg_al     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_AL);

      triton::arch::x86::x86_reg_ebx    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EBX);
      triton::arch::x86::x86_reg_bx     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_BX);
      triton::arch::x86::x86_reg_bh     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_BH);
      triton::arch::x86::x86_reg_bl     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_BL);

      triton::arch::x86::x86_reg_ecx    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_ECX);
      triton::arch::x86::x86_reg_cx     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_CX);
      triton::arch::x86::x86_reg_ch     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_CH);
      triton::arch::x86::x86_reg_cl     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_CL);

      triton::arch::x86::x86_reg_edx    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EDX);
      triton::arch::x86::x86_reg_dx     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_DX);
      triton::arch::x86::x86_reg_dh     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_DH);
      triton::arch::x86::x86_reg_dl     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_DL);

      triton::arch::x86::x86_reg_edi    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EDI);
      triton::arch::x86::x86_reg_di     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_DI);
      triton::arch::x86::x86_reg_dil    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_DIL);

      triton::arch::x86::x86_reg_esi    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_ESI);
      triton::arch::x86::x86_reg_si     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_SI);
      triton::arch::x86::x86_reg_sil    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_SIL);

      triton::arch::x86::x86_reg_esp    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_ESP);
      triton::arch::x86::x86_reg_sp     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_SP);
      triton::arch::x86::x86_reg_spl    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_SPL);
      triton::arch::x86::x86_reg_stack  = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_ESP);

      triton::arch::x86::x86_reg_ebp    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EBP);
      triton::arch::x86::x86_reg_bp     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_BP);
      triton::arch::x86::x86_reg_bpl    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_BPL);

      triton::arch::x86::x86_reg_eip    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EIP);
      triton::arch::x86::x86_reg_ip     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_IP);
      triton::arch::x86::x86_reg_pc     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EIP);

      triton::arch::x86::x86_reg_eflags = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EFLAGS);
      triton::arch::x86::x86_reg_flags  = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EFLAGS);

      triton::arch::x86::x86_reg_xmm0   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM0);
      triton::arch::x86::x86_reg_xmm1   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM1);
      triton::arch::x86::x86_reg_xmm2   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM2);
      triton::arch::x86::x86_reg_xmm3   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM3);
      triton::arch::x86::x86_reg_xmm4   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM4);
      triton::arch::x86::x86_reg_xmm5   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM5);
      triton::arch::x86::x86_reg_xmm6   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM6);
      triton::arch::x86::x86_reg_xmm7   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM7);

      triton::arch::x86::x86_reg_af     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_AF);
      triton::arch::x86::x86_reg_cf     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_CF);
      triton::arch::x86::x86_reg_df     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_DF);
      triton::arch::x86::x86_reg_if     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_IF);
      triton::arch::x86::x86_reg_of     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_OF);
      triton::arch::x86::x86_reg_pf     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_PF);
      triton::arch::x86::x86_reg_sf     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_SF);
      triton::arch::x86::x86_reg_tf     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_TF);
      triton::arch::x86::x86_reg_zf     = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_ZF);

      /* Update python env ======================================================== */
      #ifdef TRITON_PYTHON_BINDINGS
        triton::bindings::python::initRegNamespace();
        triton::bindings::python::initCpuSizeNamespace();
        triton::bindings::python::initX86OpcodesNamespace();
        #ifdef __unix__
          triton::bindings::python::initSyscallNamespace();
        #endif
      #endif
    }


    void x86Cpu::clear(void) {
      /* Clear memory */
      this->memory.clear();

      /* Clear registers */
      memset(this->eax,     0x00, sizeof(this->eax));
      memset(this->ebx,     0x00, sizeof(this->ebx));
      memset(this->ecx,     0x00, sizeof(this->ecx));
      memset(this->edx,     0x00, sizeof(this->edx));
      memset(this->edi,     0x00, sizeof(this->edi));
      memset(this->esi,     0x00, sizeof(this->esi));
      memset(this->esp,     0x00, sizeof(this->esp));
      memset(this->ebp,     0x00, sizeof(this->ebp));
      memset(this->eip,     0x00, sizeof(this->eip));
      memset(this->eflags,  0x00, sizeof(this->eflags));
      memset(this->xmm0,    0x00, sizeof(this->xmm0));
      memset(this->xmm1,    0x00, sizeof(this->xmm1));
      memset(this->xmm2,    0x00, sizeof(this->xmm2));
      memset(this->xmm3,    0x00, sizeof(this->xmm3));
      memset(this->xmm4,    0x00, sizeof(this->xmm4));
      memset(this->xmm5,    0x00, sizeof(this->xmm5));
      memset(this->xmm6,    0x00, sizeof(this->xmm6));
      memset(this->xmm7,    0x00, sizeof(this->xmm7));
    }


    void x86Cpu::operator=(const x86Cpu& other) {
      this->copy(other);
    }


    bool x86Cpu::isFlag(triton::uint32 regId) {
      return ((regId >= triton::arch::x86::ID_REG_AF && regId <= triton::arch::x86::ID_REG_ZF) ? true : false);
    }


    bool x86Cpu::isReg(triton::uint32 regId) {
      return ((regId >= triton::arch::x86::ID_REG_EAX && regId <= triton::arch::x86::ID_REG_XMM7) ? true : false);
    }


    bool x86Cpu::isRegValid(triton::uint32 regId) {
      return (this->isFlag(regId) | this->isReg(regId));
    }


    bool x86Cpu::isGPR(triton::uint32 regId) {
      return ((regId >= triton::arch::x86::ID_REG_EAX && regId < triton::arch::x86::ID_REG_XMM0) ? true : false);
    }


    bool x86Cpu::isSSE(triton::uint32 regId) {
      return ((regId >= triton::arch::x86::ID_REG_XMM0 && regId <= triton::arch::x86::ID_REG_XMM7) ? true : false);
    }


    triton::uint32 x86Cpu::invalidReg(void) {
      return triton::arch::x86::ID_REG_INVALID;
    }


    triton::uint32 x86Cpu::numberOfReg(void) {
      return triton::arch::x86::ID_REG_LAST_ITEM;
    }


    triton::uint32 x86Cpu::regSize(void) {
      return 4;
    }


    triton::uint32 x86Cpu::regBitSize(void) {
      return 32;
    }


    std::tuple<std::string, triton::uint32, triton::uint32, triton::uint32> x86Cpu::getRegInfo(triton::uint32 reg) {
      return triton::arch::x86::regIdToRegInfo(reg);
    }


    std::set<triton::arch::RegisterOperand*> x86Cpu::getParentRegister(void) {
      std::set<triton::arch::RegisterOperand*> ret;
      ret.insert(&TRITON_X86_REG_EAX);
      ret.insert(&TRITON_X86_REG_EBX);
      ret.insert(&TRITON_X86_REG_ECX);
      ret.insert(&TRITON_X86_REG_EDX);
      ret.insert(&TRITON_X86_REG_EDI);
      ret.insert(&TRITON_X86_REG_ESI);
      ret.insert(&TRITON_X86_REG_EBP);
      ret.insert(&TRITON_X86_REG_ESP);
      ret.insert(&TRITON_X86_REG_EIP);
      ret.insert(&TRITON_X86_REG_EFLAGS);
      ret.insert(&TRITON_X86_REG_AF);
      ret.insert(&TRITON_X86_REG_CF);
      ret.insert(&TRITON_X86_REG_DF);
      ret.insert(&TRITON_X86_REG_IF);
      ret.insert(&TRITON_X86_REG_OF);
      ret.insert(&TRITON_X86_REG_PF);
      ret.insert(&TRITON_X86_REG_SF);
      ret.insert(&TRITON_X86_REG_TF);
      ret.insert(&TRITON_X86_REG_ZF);
      ret.insert(&TRITON_X86_REG_XMM0);
      ret.insert(&TRITON_X86_REG_XMM1);
      ret.insert(&TRITON_X86_REG_XMM2);
      ret.insert(&TRITON_X86_REG_XMM3);
      ret.insert(&TRITON_X86_REG_XMM4);
      ret.insert(&TRITON_X86_REG_XMM5);
      ret.insert(&TRITON_X86_REG_XMM6);
      ret.insert(&TRITON_X86_REG_XMM7);
      return ret;
    }


    void x86Cpu::disassembly(triton::arch::Instruction &inst) {
      csh       handle;
      cs_insn*  insn;
      size_t    count;

      /* Check if the opcodes and opcodes' size are defined */
      if (inst.getOpcodes() == nullptr || inst.getOpcodesSize() == 0)
        throw std::runtime_error("x86Cpu::disassembly(): Opcodes and opcodesSize must be definied.");

      /* Open capstone */
      if (cs_open(CS_ARCH_X86, CS_MODE_32, &handle) != CS_ERR_OK)
        throw std::runtime_error("x86Cpu::disassembly(): Cannot open capstone.");

      /* Init capstone's options */
      cs_option(handle, CS_OPT_DETAIL, CS_OPT_ON);
      cs_option(handle, CS_OPT_SYNTAX, CS_OPT_SYNTAX_INTEL);

      /* Let's disass and build our operands */
      count = cs_disasm(handle, inst.getOpcodes(), inst.getOpcodesSize(), inst.getAddress(), 0, &insn);
      if (count > 0) {
        cs_detail* detail = insn->detail;
        for (triton::uint32 j = 0; j < count; j++) {

          /* Init the disassembly */
          std::stringstream str;
          str << insn[j].mnemonic << " " <<  insn[j].op_str;
          inst.setDisassembly(str.str());

          /* Init the instruction's type */
          inst.setType(capstoneInstToTritonInst(insn[j].id));

          /* Init operands */
          for (triton::uint32 n = 0; n < detail->x86.op_count; n++) {
            cs_x86_op *op = &(detail->x86.operands[n]);
            switch(op->type) {

              case X86_OP_IMM:
                inst.operands.push_back(triton::arch::OperandWrapper(triton::arch::ImmediateOperand(op->imm, op->size)));
                break;

              case X86_OP_MEM: {
                triton::arch::MemoryOperand mem = inst.popMemoryAccess();

                /* Set the size if the memory is not valid */
                if (!mem.isValid())
                  mem.setPair(std::make_pair(((op->size * BYTE_SIZE_BIT) - 1), 0));

                /* LEA if exists */
                triton::arch::RegisterOperand base(triton::arch::x86::capstoneRegToTritonReg(op->mem.base));
                triton::arch::RegisterOperand index(triton::arch::x86::capstoneRegToTritonReg(op->mem.index));
                triton::arch::ImmediateOperand disp(op->mem.disp, op->size);
                triton::arch::ImmediateOperand scale(op->mem.scale, op->size);

                mem.setBaseReg(base);
                mem.setIndexReg(index);
                mem.setDisplacement(disp);
                mem.setScale(scale);

                inst.operands.push_back(triton::arch::OperandWrapper(mem));
                break;
              }

              case X86_OP_REG:
                inst.operands.push_back(triton::arch::OperandWrapper(inst.getRegisterState(triton::arch::x86::capstoneRegToTritonReg(op->reg))));
                break;

              default:
                break;
            }
          }

        }
        /* Set branch */
        if (detail->groups_count > 0) {
          for (triton::uint32 n = 0; n < detail->groups_count; n++) {
            if (detail->groups[n] == X86_GRP_JUMP)
              inst.setBranch(true);
            if (detail->groups[n] == X86_GRP_JUMP || detail->groups[n] == X86_GRP_CALL || detail->groups[n] == X86_GRP_RET)
              inst.setControlFlow(true);
          }
        }
        cs_free(insn, count);
      }
      else
        throw std::runtime_error("x86Cpu::disassembly(): Failed to disassemble the given code.");

      cs_close(&handle);
      return;
    }


    void x86Cpu::buildSemantics(triton::arch::Instruction &inst) {
      if (!inst.getType())
        throw std::runtime_error("x8664Cpu::buildSemantics(): You must disassemble the instruction before.");
      triton::arch::x86::semantics::build(inst);
    }


    triton::uint8 x86Cpu::getLastMemoryValue(triton::__uint addr) {
      if (this->memory.find(addr) == this->memory.end())
        return 0x00;
      return this->memory[addr];
    }


    triton::uint128 x86Cpu::getLastMemoryValue(triton::arch::MemoryOperand& mem) {
      triton::uint128 ret = 0;
      triton::__uint addr = mem.getAddress();
      triton::uint32 size = mem.getSize();

      if (size == 0 || size > DQWORD_SIZE)
        throw std::invalid_argument("x86Cpu::getLastMemoryValue(): Invalid size memory");

      for (triton::sint32 i = size-1; i >= 0; i--)
        ret = ((ret << BYTE_SIZE_BIT) | this->memory[addr+i]);

      return ret;
    }


    triton::uint128 x86Cpu::getLastRegisterValue(triton::arch::RegisterOperand& reg) {
      triton::uint128 value = 0;
      switch (reg.getId()) {
        case triton::arch::x86::ID_REG_EAX: return (*((triton::uint32*)(this->eax)));
        case triton::arch::x86::ID_REG_AX:  return (*((triton::uint16*)(this->eax)));
        case triton::arch::x86::ID_REG_AH:  return (*((triton::uint8*)(this->eax+1)));
        case triton::arch::x86::ID_REG_AL:  return (*((triton::uint8*)(this->eax)));

        case triton::arch::x86::ID_REG_EBX: return (*((triton::uint32*)(this->ebx)));
        case triton::arch::x86::ID_REG_BX:  return (*((triton::uint16*)(this->ebx)));
        case triton::arch::x86::ID_REG_BH:  return (*((triton::uint8*)(this->ebx+1)));
        case triton::arch::x86::ID_REG_BL:  return (*((triton::uint8*)(this->ebx)));

        case triton::arch::x86::ID_REG_ECX: return (*((triton::uint32*)(this->ecx)));
        case triton::arch::x86::ID_REG_CX:  return (*((triton::uint16*)(this->ecx)));
        case triton::arch::x86::ID_REG_CH:  return (*((triton::uint8*)(this->ecx+1)));
        case triton::arch::x86::ID_REG_CL:  return (*((triton::uint8*)(this->ecx)));

        case triton::arch::x86::ID_REG_EDX: return (*((triton::uint32*)(this->edx)));
        case triton::arch::x86::ID_REG_DX:  return (*((triton::uint16*)(this->edx)));
        case triton::arch::x86::ID_REG_DH:  return (*((triton::uint8*)(this->edx+1)));
        case triton::arch::x86::ID_REG_DL:  return (*((triton::uint8*)(this->edx)));

        case triton::arch::x86::ID_REG_EDI: return (*((triton::uint32*)(this->edi)));
        case triton::arch::x86::ID_REG_DI:  return (*((triton::uint16*)(this->edi)));
        case triton::arch::x86::ID_REG_DIL: return (*((triton::uint8*)(this->edi)));

        case triton::arch::x86::ID_REG_ESI: return (*((triton::uint32*)(this->esi)));
        case triton::arch::x86::ID_REG_SI:  return (*((triton::uint16*)(this->esi)));
        case triton::arch::x86::ID_REG_SIL: return (*((triton::uint8*)(this->esi)));

        case triton::arch::x86::ID_REG_ESP: return (*((triton::uint32*)(this->esp)));
        case triton::arch::x86::ID_REG_SP:  return (*((triton::uint16*)(this->esp)));
        case triton::arch::x86::ID_REG_SPL: return (*((triton::uint8*)(this->esp)));

        case triton::arch::x86::ID_REG_EBP: return (*((triton::uint32*)(this->ebp)));
        case triton::arch::x86::ID_REG_BP:  return (*((triton::uint16*)(this->ebp)));
        case triton::arch::x86::ID_REG_BPL: return (*((triton::uint8*)(this->ebp)));

        case triton::arch::x86::ID_REG_EIP: return (*((triton::uint32*)(this->eip)));
        case triton::arch::x86::ID_REG_IP:  return (*((triton::uint16*)(this->eip)));

        case triton::arch::x86::ID_REG_EFLAGS: return (*((triton::uint32*)(this->eflags)));

        case triton::arch::x86::ID_REG_XMM0: value = triton::fromBufferToUint128(this->xmm0); return value;
        case triton::arch::x86::ID_REG_XMM1: value = triton::fromBufferToUint128(this->xmm1); return value;
        case triton::arch::x86::ID_REG_XMM2: value = triton::fromBufferToUint128(this->xmm2); return value;
        case triton::arch::x86::ID_REG_XMM3: value = triton::fromBufferToUint128(this->xmm3); return value;
        case triton::arch::x86::ID_REG_XMM4: value = triton::fromBufferToUint128(this->xmm4); return value;
        case triton::arch::x86::ID_REG_XMM5: value = triton::fromBufferToUint128(this->xmm5); return value;
        case triton::arch::x86::ID_REG_XMM6: value = triton::fromBufferToUint128(this->xmm6); return value;
        case triton::arch::x86::ID_REG_XMM7: value = triton::fromBufferToUint128(this->xmm7); return value;

        case triton::arch::x86::ID_REG_AF: return (((*((triton::uint32*)(this->eflags))) >> 4) & 1);
        case triton::arch::x86::ID_REG_CF: return ((*((triton::uint32*)(this->eflags))) & 1);
        case triton::arch::x86::ID_REG_DF: return (((*((triton::uint32*)(this->eflags))) >> 10) & 1);
        case triton::arch::x86::ID_REG_IF: return (((*((triton::uint32*)(this->eflags))) >> 9) & 1);
        case triton::arch::x86::ID_REG_OF: return (((*((triton::uint32*)(this->eflags))) >> 11) & 1);
        case triton::arch::x86::ID_REG_PF: return (((*((triton::uint32*)(this->eflags))) >> 2) & 1);
        case triton::arch::x86::ID_REG_SF: return (((*((triton::uint32*)(this->eflags))) >> 7) & 1);
        case triton::arch::x86::ID_REG_TF: return (((*((triton::uint32*)(this->eflags))) >> 8) & 1);
        case triton::arch::x86::ID_REG_ZF: return (((*((triton::uint32*)(this->eflags))) >> 6) & 1);

        default:
          throw std::invalid_argument("x86Cpu::getLastRegisterValue(): Invalid register");
      }

      return value;
    }


    void x86Cpu::setLastMemoryValue(triton::__uint addr, triton::uint8 value) {
      this->memory[addr] = value;
    }


    void x86Cpu::setLastMemoryValue(triton::arch::MemoryOperand& mem) {
      triton::__uint addr = mem.getAddress();
      triton::uint32 size = mem.getSize();
      triton::uint128 cv  = mem.getConcreteValue();

      if (size == 0 || size > DQWORD_SIZE)
        throw std::invalid_argument("x86Cpu::setLastMemoryValue(): Invalid size memory");

      for (triton::uint32 i = 0; i < size; i++) {
        this->memory[addr+i] = static_cast<triton::uint8>(cv & 0xff);
        cv >>= 8;
      }
    }


    void x86Cpu::setLastRegisterValue(triton::arch::RegisterOperand& reg) {
      triton::uint128 value = reg.getConcreteValue();

      if (reg.isFlag())
        throw std::invalid_argument("x86Cpu::setLastRegisterValue(): You cannot set an isolated flag. Use the flags register EFLAGS.");

      switch (reg.getId()) {
        case triton::arch::x86::ID_REG_EAX: (*((triton::uint32*)(this->eax))) = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_AX:  (*((triton::uint16*)(this->eax))) = static_cast<triton::uint16>(value); break;
        case triton::arch::x86::ID_REG_AH:  (*((triton::uint8*)(this->eax+1))) = static_cast<triton::uint8>(value); break;
        case triton::arch::x86::ID_REG_AL:  (*((triton::uint8*)(this->eax))) = static_cast<triton::uint8>(value); break;

        case triton::arch::x86::ID_REG_EBX: (*((triton::uint32*)(this->ebx))) = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_BX:  (*((triton::uint16*)(this->ebx))) = static_cast<triton::uint16>(value); break;
        case triton::arch::x86::ID_REG_BH:  (*((triton::uint8*)(this->ebx+1))) = static_cast<triton::uint8>(value); break;
        case triton::arch::x86::ID_REG_BL:  (*((triton::uint8*)(this->ebx))) = static_cast<triton::uint8>(value); break;

        case triton::arch::x86::ID_REG_ECX: (*((triton::uint32*)(this->ecx))) = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_CX:  (*((triton::uint16*)(this->ecx))) = static_cast<triton::uint16>(value); break;
        case triton::arch::x86::ID_REG_CH:  (*((triton::uint8*)(this->ecx+1))) = static_cast<triton::uint8>(value); break;
        case triton::arch::x86::ID_REG_CL:  (*((triton::uint8*)(this->ecx))) = static_cast<triton::uint8>(value); break;

        case triton::arch::x86::ID_REG_EDX: (*((triton::uint32*)(this->edx))) = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_DX:  (*((triton::uint16*)(this->edx))) = static_cast<triton::uint16>(value); break;
        case triton::arch::x86::ID_REG_DH:  (*((triton::uint8*)(this->edx+1))) = static_cast<triton::uint8>(value); break;
        case triton::arch::x86::ID_REG_DL:  (*((triton::uint8*)(this->edx))) = static_cast<triton::uint8>(value); break;

        case triton::arch::x86::ID_REG_EDI: (*((triton::uint32*)(this->edi))) = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_DI:  (*((triton::uint16*)(this->edi))) = static_cast<triton::uint16>(value); break;
        case triton::arch::x86::ID_REG_DIL: (*((triton::uint8*)(this->edi))) = static_cast<triton::uint8>(value); break;

        case triton::arch::x86::ID_REG_ESI: (*((triton::uint32*)(this->esi))) = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_SI:  (*((triton::uint16*)(this->esi))) = static_cast<triton::uint16>(value); break;
        case triton::arch::x86::ID_REG_SIL: (*((triton::uint8*)(this->esi))) = static_cast<triton::uint8>(value); break;

        case triton::arch::x86::ID_REG_ESP: (*((triton::uint32*)(this->esp))) = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_SP:  (*((triton::uint16*)(this->esp))) = static_cast<triton::uint16>(value); break;
        case triton::arch::x86::ID_REG_SPL: (*((triton::uint8*)(this->esp))) = static_cast<triton::uint8>(value); break;

        case triton::arch::x86::ID_REG_EBP: (*((triton::uint32*)(this->ebp))) = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_BP:  (*((triton::uint16*)(this->ebp))) = static_cast<triton::uint16>(value); break;
        case triton::arch::x86::ID_REG_BPL: (*((triton::uint8*)(this->ebp))) = static_cast<triton::uint8>(value); break;

        case triton::arch::x86::ID_REG_EIP: (*((triton::uint32*)(this->eip))) = static_cast<triton::uint32>(value); break;
        case triton::arch::x86::ID_REG_IP:  (*((triton::uint16*)(this->eip))) = static_cast<triton::uint16>(value); break;

        case triton::arch::x86::ID_REG_EFLAGS: (*((triton::uint32*)(this->eflags))) = static_cast<triton::uint32>(value); break;

        case triton::arch::x86::ID_REG_XMM0: triton::fromUint128ToBuffer(value, this->xmm0); break;
        case triton::arch::x86::ID_REG_XMM1: triton::fromUint128ToBuffer(value, this->xmm1); break;
        case triton::arch::x86::ID_REG_XMM2: triton::fromUint128ToBuffer(value, this->xmm2); break;
        case triton::arch::x86::ID_REG_XMM3: triton::fromUint128ToBuffer(value, this->xmm3); break;
        case triton::arch::x86::ID_REG_XMM4: triton::fromUint128ToBuffer(value, this->xmm4); break;
        case triton::arch::x86::ID_REG_XMM5: triton::fromUint128ToBuffer(value, this->xmm5); break;
        case triton::arch::x86::ID_REG_XMM6: triton::fromUint128ToBuffer(value, this->xmm6); break;
        case triton::arch::x86::ID_REG_XMM7: triton::fromUint128ToBuffer(value, this->xmm7); break;

        default:
          throw std::invalid_argument("x86Cpu:setLastRegisterValue() - Invalid register");
      }
    }

    }; /* x86 namespace */
  }; /* arch namespace */
}; /* triton namespace */

