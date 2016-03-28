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
#include <externalLibs.hpp>
#include <immediateOperand.hpp>
#include <x86Cpu.hpp>
#include <x86Specifications.hpp>

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
      memcpy(this->eax,     other.eax,    sizeof(this->eax));
      memcpy(this->ebx,     other.ebx,    sizeof(this->ebx));
      memcpy(this->ecx,     other.ecx,    sizeof(this->ecx));
      memcpy(this->edx,     other.edx,    sizeof(this->edx));
      memcpy(this->edi,     other.edi,    sizeof(this->edi));
      memcpy(this->esi,     other.esi,    sizeof(this->esi));
      memcpy(this->esp,     other.esp,    sizeof(this->esp));
      memcpy(this->ebp,     other.ebp,    sizeof(this->ebp));
      memcpy(this->eip,     other.eip,    sizeof(this->eip));
      memcpy(this->eflags,  other.eflags, sizeof(this->eflags));
      memcpy(this->mm0,     other.mm0,    sizeof(this->mm0));
      memcpy(this->mm1,     other.mm1,    sizeof(this->mm1));
      memcpy(this->mm2,     other.mm2,    sizeof(this->mm2));
      memcpy(this->mm3,     other.mm3,    sizeof(this->mm3));
      memcpy(this->mm4,     other.mm4,    sizeof(this->mm4));
      memcpy(this->mm5,     other.mm5,    sizeof(this->mm5));
      memcpy(this->mm6,     other.mm6,    sizeof(this->mm6));
      memcpy(this->mm7,     other.mm7,    sizeof(this->mm7));
      memcpy(this->xmm0,    other.xmm0,   sizeof(this->xmm0));
      memcpy(this->xmm1,    other.xmm1,   sizeof(this->xmm1));
      memcpy(this->xmm2,    other.xmm2,   sizeof(this->xmm2));
      memcpy(this->xmm3,    other.xmm3,   sizeof(this->xmm3));
      memcpy(this->xmm4,    other.xmm4,   sizeof(this->xmm4));
      memcpy(this->xmm5,    other.xmm5,   sizeof(this->xmm5));
      memcpy(this->xmm6,    other.xmm6,   sizeof(this->xmm6));
      memcpy(this->xmm7,    other.xmm7,   sizeof(this->xmm7));
      memcpy(this->ymm0,    other.ymm0,   sizeof(this->ymm0));
      memcpy(this->ymm1,    other.ymm1,   sizeof(this->ymm1));
      memcpy(this->ymm2,    other.ymm2,   sizeof(this->ymm2));
      memcpy(this->ymm3,    other.ymm3,   sizeof(this->ymm3));
      memcpy(this->ymm4,    other.ymm4,   sizeof(this->ymm4));
      memcpy(this->ymm5,    other.ymm5,   sizeof(this->ymm5));
      memcpy(this->ymm6,    other.ymm6,   sizeof(this->ymm6));
      memcpy(this->ymm7,    other.ymm7,   sizeof(this->ymm7));
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

      triton::arch::x86::x86_reg_mm0    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_MM0);
      triton::arch::x86::x86_reg_mm1    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_MM1);
      triton::arch::x86::x86_reg_mm2    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_MM2);
      triton::arch::x86::x86_reg_mm3    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_MM3);
      triton::arch::x86::x86_reg_mm4    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_MM4);
      triton::arch::x86::x86_reg_mm5    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_MM5);
      triton::arch::x86::x86_reg_mm6    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_MM6);
      triton::arch::x86::x86_reg_mm7    = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_MM7);

      triton::arch::x86::x86_reg_xmm0   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM0);
      triton::arch::x86::x86_reg_xmm1   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM1);
      triton::arch::x86::x86_reg_xmm2   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM2);
      triton::arch::x86::x86_reg_xmm3   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM3);
      triton::arch::x86::x86_reg_xmm4   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM4);
      triton::arch::x86::x86_reg_xmm5   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM5);
      triton::arch::x86::x86_reg_xmm6   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM6);
      triton::arch::x86::x86_reg_xmm7   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM7);

      triton::arch::x86::x86_reg_ymm0   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_YMM0);
      triton::arch::x86::x86_reg_ymm1   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_YMM1);
      triton::arch::x86::x86_reg_ymm2   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_YMM2);
      triton::arch::x86::x86_reg_ymm3   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_YMM3);
      triton::arch::x86::x86_reg_ymm4   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_YMM4);
      triton::arch::x86::x86_reg_ymm5   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_YMM5);
      triton::arch::x86::x86_reg_ymm6   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_YMM6);
      triton::arch::x86::x86_reg_ymm7   = triton::arch::RegisterOperand(triton::arch::x86::ID_REG_YMM7);

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
      memset(this->mm0,     0x00, sizeof(this->mm0));
      memset(this->mm1,     0x00, sizeof(this->mm1));
      memset(this->mm2,     0x00, sizeof(this->mm2));
      memset(this->mm3,     0x00, sizeof(this->mm3));
      memset(this->mm4,     0x00, sizeof(this->mm4));
      memset(this->mm5,     0x00, sizeof(this->mm5));
      memset(this->mm6,     0x00, sizeof(this->mm6));
      memset(this->mm7,     0x00, sizeof(this->mm7));
      memset(this->xmm0,    0x00, sizeof(this->xmm0));
      memset(this->xmm1,    0x00, sizeof(this->xmm1));
      memset(this->xmm2,    0x00, sizeof(this->xmm2));
      memset(this->xmm3,    0x00, sizeof(this->xmm3));
      memset(this->xmm4,    0x00, sizeof(this->xmm4));
      memset(this->xmm5,    0x00, sizeof(this->xmm5));
      memset(this->xmm6,    0x00, sizeof(this->xmm6));
      memset(this->xmm7,    0x00, sizeof(this->xmm7));
      memset(this->ymm0,    0x00, sizeof(this->ymm0));
      memset(this->ymm1,    0x00, sizeof(this->ymm1));
      memset(this->ymm2,    0x00, sizeof(this->ymm2));
      memset(this->ymm3,    0x00, sizeof(this->ymm3));
      memset(this->ymm4,    0x00, sizeof(this->ymm4));
      memset(this->ymm5,    0x00, sizeof(this->ymm5));
      memset(this->ymm6,    0x00, sizeof(this->ymm6));
      memset(this->ymm7,    0x00, sizeof(this->ymm7));
    }


    void x86Cpu::operator=(const x86Cpu& other) {
      this->copy(other);
    }


    bool x86Cpu::isFlag(triton::uint32 regId) {
      return ((regId >= triton::arch::x86::ID_REG_AF && regId <= triton::arch::x86::ID_REG_ZF) ? true : false);
    }


    bool x86Cpu::isRegister(triton::uint32 regId) {
      return ((regId >= triton::arch::x86::ID_REG_EAX && regId <= triton::arch::x86::ID_REG_XMM7) ? true : false);
    }


    bool x86Cpu::isRegisterValid(triton::uint32 regId) {
      return (this->isFlag(regId) | this->isRegister(regId));
    }


    bool x86Cpu::isGPR(triton::uint32 regId) {
      return ((regId >= triton::arch::x86::ID_REG_EAX && regId < triton::arch::x86::ID_REG_MM0) ? true : false);
    }


    bool x86Cpu::isMMX(triton::uint32 regId) {
      return ((regId >= triton::arch::x86::ID_REG_MM0 && regId <= triton::arch::x86::ID_REG_MM7) ? true : false);
    }


    bool x86Cpu::isSSE(triton::uint32 regId) {
      return ((regId >= triton::arch::x86::ID_REG_XMM0 && regId <= triton::arch::x86::ID_REG_XMM7) ? true : false);
    }


    bool x86Cpu::isAVX256(triton::uint32 regId) {
      return ((regId >= triton::arch::x86::ID_REG_YMM0 && regId <= triton::arch::x86::ID_REG_YMM7) ? true : false);
    }


    triton::uint32 x86Cpu::invalidRegister(void) {
      return triton::arch::x86::ID_REG_INVALID;
    }


    triton::uint32 x86Cpu::numberOfRegisters(void) {
      return triton::arch::x86::ID_REG_LAST_ITEM;
    }


    triton::uint32 x86Cpu::registerSize(void) {
      return DWORD_SIZE;
    }


    triton::uint32 x86Cpu::registerBitSize(void) {
      return DWORD_SIZE_BIT;
    }


    std::tuple<std::string, triton::uint32, triton::uint32, triton::uint32> x86Cpu::getRegisterInformation(triton::uint32 reg) {
      return triton::arch::x86::regIdToRegInfo(reg);
    }


    std::set<triton::arch::RegisterOperand*> x86Cpu::getAllRegisters(void) {
      std::set<triton::arch::RegisterOperand*> ret;

      for (triton::uint32 index = 0; index < triton::arch::x86::ID_REG_LAST_ITEM; index++) {
        if (this->isRegisterValid(triton::arch::x86::x86_regs[index]->getId()))
          ret.insert(triton::arch::x86::x86_regs[index]);
      }

      return ret;
    }


    std::set<triton::arch::RegisterOperand*> x86Cpu::getParentRegisters(void) {
      std::set<triton::arch::RegisterOperand*> ret;

      for (triton::uint32 index = 0; index < triton::arch::x86::ID_REG_LAST_ITEM; index++) {
        /* Add GPR */
        if (triton::arch::x86::x86_regs[index]->getSize() == this->registerSize())
          ret.insert(triton::arch::x86::x86_regs[index]);

        /* Add Flags */
        else if (this->isFlag(triton::arch::x86::x86_regs[index]->getId()))
          ret.insert(triton::arch::x86::x86_regs[index]);

        /* Add MMX */
        else if (this->isMMX(triton::arch::x86::x86_regs[index]->getId()))
          ret.insert(triton::arch::x86::x86_regs[index]);

        /* Add SSE */
        else if (this->isSSE(triton::arch::x86::x86_regs[index]->getId()))
          ret.insert(triton::arch::x86::x86_regs[index]);

        /* Add AVX-256 */
        else if (this->isAVX256(triton::arch::x86::x86_regs[index]->getId()))
          ret.insert(triton::arch::x86::x86_regs[index]);
      }

      return ret;
    }


    void x86Cpu::disassembly(triton::arch::Instruction &inst) {
      triton::extlibs::capstone::csh       handle;
      triton::extlibs::capstone::cs_insn*  insn;
      size_t                               count = 0;

      /* Check if the opcodes and opcodes' size are defined */
      if (inst.getOpcodes() == nullptr || inst.getOpcodesSize() == 0)
        throw std::runtime_error("x86Cpu::disassembly(): Opcodes and opcodesSize must be definied.");

      /* Open capstone */
      if (triton::extlibs::capstone::cs_open(triton::extlibs::capstone::CS_ARCH_X86, triton::extlibs::capstone::CS_MODE_32, &handle) != triton::extlibs::capstone::CS_ERR_OK)
        throw std::runtime_error("x86Cpu::disassembly(): Cannot open capstone.");

      /* Init capstone's options */
      triton::extlibs::capstone::cs_option(handle, triton::extlibs::capstone::CS_OPT_DETAIL, triton::extlibs::capstone::CS_OPT_ON);
      triton::extlibs::capstone::cs_option(handle, triton::extlibs::capstone::CS_OPT_SYNTAX, triton::extlibs::capstone::CS_OPT_SYNTAX_INTEL);

      /* Let's disass and build our operands */
      count = triton::extlibs::capstone::cs_disasm(handle, inst.getOpcodes(), inst.getOpcodesSize(), inst.getAddress(), 0, &insn);
      if (count > 0) {
        triton::extlibs::capstone::cs_detail* detail = insn->detail;
        for (triton::uint32 j = 0; j < count; j++) {

          /* Init the disassembly */
          std::stringstream str;
          str << insn[j].mnemonic << " " <<  insn[j].op_str;
          inst.setDisassembly(str.str());

          /* Init the instruction's type */
          inst.setType(capstoneInstToTritonInst(insn[j].id));

          /* Init operands */
          for (triton::uint32 n = 0; n < detail->x86.op_count; n++) {
            triton::extlibs::capstone::cs_x86_op* op = &(detail->x86.operands[n]);
            switch(op->type) {

              case triton::extlibs::capstone::X86_OP_IMM:
                inst.operands.push_back(triton::arch::OperandWrapper(triton::arch::ImmediateOperand(op->imm, op->size)));
                break;

              case triton::extlibs::capstone::X86_OP_MEM: {
                triton::arch::MemoryOperand mem = inst.popMemoryAccess();

                /* Set the size if the memory is not valid */
                if (!mem.isValid())
                  mem.setPair(std::make_pair(((op->size * BYTE_SIZE_BIT) - 1), 0));

                /* LEA if exists */
                triton::arch::RegisterOperand base(triton::arch::x86::capstoneRegToTritonReg(op->mem.base));
                triton::arch::RegisterOperand index(triton::arch::x86::capstoneRegToTritonReg(op->mem.index));
                triton::arch::ImmediateOperand disp(op->mem.disp, op->size);
                triton::arch::ImmediateOperand scale(op->mem.scale, op->size);

                mem.setBaseRegister(base);
                mem.setIndexRegister(index);
                mem.setDisplacement(disp);
                mem.setScale(scale);

                inst.operands.push_back(triton::arch::OperandWrapper(mem));
                break;
              }

              case triton::extlibs::capstone::X86_OP_REG:
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
            if (detail->groups[n] == triton::extlibs::capstone::X86_GRP_JUMP)
              inst.setBranch(true);
            if (detail->groups[n] == triton::extlibs::capstone::X86_GRP_JUMP ||
                detail->groups[n] == triton::extlibs::capstone::X86_GRP_CALL ||
                detail->groups[n] == triton::extlibs::capstone::X86_GRP_RET)
              inst.setControlFlow(true);
          }
        }
        triton::extlibs::capstone::cs_free(insn, count);
      }
      else
        throw std::runtime_error("x86Cpu::disassembly(): Failed to disassemble the given code.");

      triton::extlibs::capstone::cs_close(&handle);
      return;
    }


    void x86Cpu::buildSemantics(triton::arch::Instruction &inst) {
      if (!inst.getType())
        throw std::runtime_error("x86Cpu::buildSemantics(): You must disassemble the instruction before.");
      triton::arch::x86::semantics::build(inst);
    }


    triton::uint8 x86Cpu::getLastMemoryValue(triton::__uint addr) {
      if (this->memory.find(addr) == this->memory.end())
        return 0x00;
      return this->memory[addr];
    }


    triton::uint512 x86Cpu::getLastMemoryValue(triton::arch::MemoryOperand& mem) {
      triton::uint512 ret = 0;
      triton::__uint addr = mem.getAddress();
      triton::uint32 size = mem.getSize();

      if (size == 0 || size > DQQWORD_SIZE)
        throw std::invalid_argument("x86Cpu::getLastMemoryValue(): Invalid size memory.");

      for (triton::sint32 i = size-1; i >= 0; i--)
        ret = ((ret << BYTE_SIZE_BIT) | this->memory[addr+i]);

      return ret;
    }


    std::vector<triton::uint8> x86Cpu::getLastMemoryAreaValue(triton::__uint baseAddr, triton::uint32 size) {
      std::vector<triton::uint8> area;

      for (triton::uint32 index = 0; index < size; index++) {
        if (this->memory.find(baseAddr+index) != this->memory.end())
          area.push_back(this->memory[baseAddr+index]);
        else
          area.push_back(0x00);
      }

      return area;
    }


    triton::uint512 x86Cpu::getLastRegisterValue(triton::arch::RegisterOperand& reg) {
      triton::uint512 value = 0;
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

        case triton::arch::x86::ID_REG_MM0:  return (*((triton::uint64*)(this->mm0)));
        case triton::arch::x86::ID_REG_MM1:  return (*((triton::uint64*)(this->mm1)));
        case triton::arch::x86::ID_REG_MM2:  return (*((triton::uint64*)(this->mm2)));
        case triton::arch::x86::ID_REG_MM3:  return (*((triton::uint64*)(this->mm3)));
        case triton::arch::x86::ID_REG_MM4:  return (*((triton::uint64*)(this->mm4)));
        case triton::arch::x86::ID_REG_MM5:  return (*((triton::uint64*)(this->mm5)));
        case triton::arch::x86::ID_REG_MM6:  return (*((triton::uint64*)(this->mm6)));
        case triton::arch::x86::ID_REG_MM7:  return (*((triton::uint64*)(this->mm7)));

        case triton::arch::x86::ID_REG_XMM0: value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm0); return value;
        case triton::arch::x86::ID_REG_XMM1: value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm1); return value;
        case triton::arch::x86::ID_REG_XMM2: value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm2); return value;
        case triton::arch::x86::ID_REG_XMM3: value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm3); return value;
        case triton::arch::x86::ID_REG_XMM4: value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm4); return value;
        case triton::arch::x86::ID_REG_XMM5: value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm5); return value;
        case triton::arch::x86::ID_REG_XMM6: value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm6); return value;
        case triton::arch::x86::ID_REG_XMM7: value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm7); return value;

        case triton::arch::x86::ID_REG_YMM0: value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm0); return value;
        case triton::arch::x86::ID_REG_YMM1: value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm1); return value;
        case triton::arch::x86::ID_REG_YMM2: value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm2); return value;
        case triton::arch::x86::ID_REG_YMM3: value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm3); return value;
        case triton::arch::x86::ID_REG_YMM4: value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm4); return value;
        case triton::arch::x86::ID_REG_YMM5: value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm5); return value;
        case triton::arch::x86::ID_REG_YMM6: value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm6); return value;
        case triton::arch::x86::ID_REG_YMM7: value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm7); return value;

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
          throw std::invalid_argument("x86Cpu::getLastRegisterValue(): Invalid register.");
      }

      return value;
    }


    void x86Cpu::setLastMemoryValue(triton::__uint addr, triton::uint8 value) {
      this->memory[addr] = value;
    }


    void x86Cpu::setLastMemoryValue(triton::arch::MemoryOperand& mem) {
      triton::__uint addr = mem.getAddress();
      triton::uint32 size = mem.getSize();
      triton::uint512 cv  = mem.getConcreteValue();

      if (size == 0 || size > DQQWORD_SIZE)
        throw std::invalid_argument("x86Cpu::setLastMemoryValue(): Invalid size memory.");

      for (triton::uint32 i = 0; i < size; i++) {
        this->memory[addr+i] = (cv & 0xff).convert_to<triton::uint8>();
        cv >>= 8;
      }
    }


    void x86Cpu::setLastMemoryAreaValue(triton::__uint baseAddr, std::vector<triton::uint8>& values) {
      for (triton::uint32 index = 0; index < values.size(); index++) {
        this->memory[baseAddr+index] = values[index];
      }
    }


    void x86Cpu::setLastRegisterValue(triton::arch::RegisterOperand& reg) {
      triton::uint512 value = reg.getConcreteValue();

      if (reg.isFlag())
        throw std::invalid_argument("x86Cpu::setLastRegisterValue(): You cannot set an isolated flag. Use the flags register EFLAGS.");

      switch (reg.getId()) {
        case triton::arch::x86::ID_REG_EAX: (*((triton::uint32*)(this->eax)))  = value.convert_to<triton::uint32>(); break;
        case triton::arch::x86::ID_REG_AX:  (*((triton::uint16*)(this->eax)))  = value.convert_to<triton::uint16>(); break;
        case triton::arch::x86::ID_REG_AH:  (*((triton::uint8*)(this->eax+1))) = value.convert_to<triton::uint8>(); break;
        case triton::arch::x86::ID_REG_AL:  (*((triton::uint8*)(this->eax)))   = value.convert_to<triton::uint8>(); break;

        case triton::arch::x86::ID_REG_EBX: (*((triton::uint32*)(this->ebx)))  = value.convert_to<triton::uint32>(); break;
        case triton::arch::x86::ID_REG_BX:  (*((triton::uint16*)(this->ebx)))  = value.convert_to<triton::uint16>(); break;
        case triton::arch::x86::ID_REG_BH:  (*((triton::uint8*)(this->ebx+1))) = value.convert_to<triton::uint8>(); break;
        case triton::arch::x86::ID_REG_BL:  (*((triton::uint8*)(this->ebx)))   = value.convert_to<triton::uint8>(); break;

        case triton::arch::x86::ID_REG_ECX: (*((triton::uint32*)(this->ecx)))  = value.convert_to<triton::uint32>(); break;
        case triton::arch::x86::ID_REG_CX:  (*((triton::uint16*)(this->ecx)))  = value.convert_to<triton::uint16>(); break;
        case triton::arch::x86::ID_REG_CH:  (*((triton::uint8*)(this->ecx+1))) = value.convert_to<triton::uint8>(); break;
        case triton::arch::x86::ID_REG_CL:  (*((triton::uint8*)(this->ecx)))   = value.convert_to<triton::uint8>(); break;

        case triton::arch::x86::ID_REG_EDX: (*((triton::uint32*)(this->edx)))  = value.convert_to<triton::uint32>(); break;
        case triton::arch::x86::ID_REG_DX:  (*((triton::uint16*)(this->edx)))  = value.convert_to<triton::uint16>(); break;
        case triton::arch::x86::ID_REG_DH:  (*((triton::uint8*)(this->edx+1))) = value.convert_to<triton::uint8>(); break;
        case triton::arch::x86::ID_REG_DL:  (*((triton::uint8*)(this->edx)))   = value.convert_to<triton::uint8>(); break;

        case triton::arch::x86::ID_REG_EDI: (*((triton::uint32*)(this->edi)))  = value.convert_to<triton::uint32>(); break;
        case triton::arch::x86::ID_REG_DI:  (*((triton::uint16*)(this->edi)))  = value.convert_to<triton::uint16>(); break;
        case triton::arch::x86::ID_REG_DIL: (*((triton::uint8*)(this->edi)))   = value.convert_to<triton::uint8>(); break;

        case triton::arch::x86::ID_REG_ESI: (*((triton::uint32*)(this->esi)))  = value.convert_to<triton::uint32>(); break;
        case triton::arch::x86::ID_REG_SI:  (*((triton::uint16*)(this->esi)))  = value.convert_to<triton::uint16>(); break;
        case triton::arch::x86::ID_REG_SIL: (*((triton::uint8*)(this->esi)))   = value.convert_to<triton::uint8>(); break;

        case triton::arch::x86::ID_REG_ESP: (*((triton::uint32*)(this->esp)))  = value.convert_to<triton::uint32>(); break;
        case triton::arch::x86::ID_REG_SP:  (*((triton::uint16*)(this->esp)))  = value.convert_to<triton::uint16>(); break;
        case triton::arch::x86::ID_REG_SPL: (*((triton::uint8*)(this->esp)))   = value.convert_to<triton::uint8>(); break;

        case triton::arch::x86::ID_REG_EBP: (*((triton::uint32*)(this->ebp)))  = value.convert_to<triton::uint32>(); break;
        case triton::arch::x86::ID_REG_BP:  (*((triton::uint16*)(this->ebp)))  = value.convert_to<triton::uint16>(); break;
        case triton::arch::x86::ID_REG_BPL: (*((triton::uint8*)(this->ebp)))   = value.convert_to<triton::uint8>(); break;

        case triton::arch::x86::ID_REG_EIP: (*((triton::uint32*)(this->eip)))  = value.convert_to<triton::uint32>(); break;
        case triton::arch::x86::ID_REG_IP:  (*((triton::uint16*)(this->eip)))  = value.convert_to<triton::uint16>(); break;

        case triton::arch::x86::ID_REG_EFLAGS: (*((triton::uint32*)(this->eflags))) = value.convert_to<triton::uint32>(); break;

        case triton::arch::x86::ID_REG_MM0:  (*((triton::uint64*)(this->mm0))) = value.convert_to<triton::uint64>(); break;
        case triton::arch::x86::ID_REG_MM1:  (*((triton::uint64*)(this->mm1))) = value.convert_to<triton::uint64>(); break;
        case triton::arch::x86::ID_REG_MM2:  (*((triton::uint64*)(this->mm2))) = value.convert_to<triton::uint64>(); break;
        case triton::arch::x86::ID_REG_MM3:  (*((triton::uint64*)(this->mm3))) = value.convert_to<triton::uint64>(); break;
        case triton::arch::x86::ID_REG_MM4:  (*((triton::uint64*)(this->mm4))) = value.convert_to<triton::uint64>(); break;
        case triton::arch::x86::ID_REG_MM5:  (*((triton::uint64*)(this->mm5))) = value.convert_to<triton::uint64>(); break;
        case triton::arch::x86::ID_REG_MM6:  (*((triton::uint64*)(this->mm6))) = value.convert_to<triton::uint64>(); break;
        case triton::arch::x86::ID_REG_MM7:  (*((triton::uint64*)(this->mm7))) = value.convert_to<triton::uint64>(); break;

        case triton::arch::x86::ID_REG_XMM0: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm0); break;
        case triton::arch::x86::ID_REG_XMM1: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm1); break;
        case triton::arch::x86::ID_REG_XMM2: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm2); break;
        case triton::arch::x86::ID_REG_XMM3: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm3); break;
        case triton::arch::x86::ID_REG_XMM4: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm4); break;
        case triton::arch::x86::ID_REG_XMM5: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm5); break;
        case triton::arch::x86::ID_REG_XMM6: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm6); break;
        case triton::arch::x86::ID_REG_XMM7: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm7); break;

        case triton::arch::x86::ID_REG_YMM0: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm0); break;
        case triton::arch::x86::ID_REG_YMM1: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm1); break;
        case triton::arch::x86::ID_REG_YMM2: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm2); break;
        case triton::arch::x86::ID_REG_YMM3: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm3); break;
        case triton::arch::x86::ID_REG_YMM4: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm4); break;
        case triton::arch::x86::ID_REG_YMM5: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm5); break;
        case triton::arch::x86::ID_REG_YMM6: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm6); break;
        case triton::arch::x86::ID_REG_YMM7: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm7); break;

        default:
          throw std::invalid_argument("x86Cpu:setLastRegisterValue() - Invalid register.");
      }
    }

    }; /* x86 namespace */
  }; /* arch namespace */
}; /* triton namespace */

