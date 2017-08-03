//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstring>

#include <triton/architecture.hpp>
#include <triton/coreUtils.hpp>
#include <triton/cpuSize.hpp>
#include <triton/exceptions.hpp>
#include <triton/externalLibs.hpp>
#include <triton/immediate.hpp>
#include <triton/x86Cpu.hpp>



namespace triton {
  namespace arch {
    namespace x86 {

      x86Cpu::x86Cpu(triton::callbacks::Callbacks* callbacks) : x86Specifications(ARCH_X86) {
        this->callbacks = callbacks;
        this->clear();
      }

      x86Cpu::x86Cpu(const x86Cpu& other) : x86Specifications(ARCH_X86) {
        this->copy(other);
      }


      x86Cpu::~x86Cpu() {
        this->memory.clear();
      }


      void x86Cpu::copy(const x86Cpu& other) {
        this->callbacks = other.callbacks;
        this->memory    = other.memory;

        std::memcpy(this->eax,     other.eax,    sizeof(this->eax));
        std::memcpy(this->ebx,     other.ebx,    sizeof(this->ebx));
        std::memcpy(this->ecx,     other.ecx,    sizeof(this->ecx));
        std::memcpy(this->edx,     other.edx,    sizeof(this->edx));
        std::memcpy(this->edi,     other.edi,    sizeof(this->edi));
        std::memcpy(this->esi,     other.esi,    sizeof(this->esi));
        std::memcpy(this->esp,     other.esp,    sizeof(this->esp));
        std::memcpy(this->ebp,     other.ebp,    sizeof(this->ebp));
        std::memcpy(this->eip,     other.eip,    sizeof(this->eip));
        std::memcpy(this->eflags,  other.eflags, sizeof(this->eflags));
        std::memcpy(this->mm0,     other.mm0,    sizeof(this->mm0));
        std::memcpy(this->mm1,     other.mm1,    sizeof(this->mm1));
        std::memcpy(this->mm2,     other.mm2,    sizeof(this->mm2));
        std::memcpy(this->mm3,     other.mm3,    sizeof(this->mm3));
        std::memcpy(this->mm4,     other.mm4,    sizeof(this->mm4));
        std::memcpy(this->mm5,     other.mm5,    sizeof(this->mm5));
        std::memcpy(this->mm6,     other.mm6,    sizeof(this->mm6));
        std::memcpy(this->mm7,     other.mm7,    sizeof(this->mm7));
        std::memcpy(this->xmm0,    other.xmm0,   sizeof(this->xmm0));
        std::memcpy(this->xmm1,    other.xmm1,   sizeof(this->xmm1));
        std::memcpy(this->xmm2,    other.xmm2,   sizeof(this->xmm2));
        std::memcpy(this->xmm3,    other.xmm3,   sizeof(this->xmm3));
        std::memcpy(this->xmm4,    other.xmm4,   sizeof(this->xmm4));
        std::memcpy(this->xmm5,    other.xmm5,   sizeof(this->xmm5));
        std::memcpy(this->xmm6,    other.xmm6,   sizeof(this->xmm6));
        std::memcpy(this->xmm7,    other.xmm7,   sizeof(this->xmm7));
        std::memcpy(this->ymm0,    other.ymm0,   sizeof(this->ymm0));
        std::memcpy(this->ymm1,    other.ymm1,   sizeof(this->ymm1));
        std::memcpy(this->ymm2,    other.ymm2,   sizeof(this->ymm2));
        std::memcpy(this->ymm3,    other.ymm3,   sizeof(this->ymm3));
        std::memcpy(this->ymm4,    other.ymm4,   sizeof(this->ymm4));
        std::memcpy(this->ymm5,    other.ymm5,   sizeof(this->ymm5));
        std::memcpy(this->ymm6,    other.ymm6,   sizeof(this->ymm6));
        std::memcpy(this->ymm7,    other.ymm7,   sizeof(this->ymm7));
        std::memcpy(this->mxcsr,   other.mxcsr,  sizeof(this->mxcsr));
        std::memcpy(this->cr0,     other.cr0,    sizeof(this->cr0));
        std::memcpy(this->cr1,     other.cr1,    sizeof(this->cr1));
        std::memcpy(this->cr2,     other.cr2,    sizeof(this->cr2));
        std::memcpy(this->cr3,     other.cr3,    sizeof(this->cr3));
        std::memcpy(this->cr4,     other.cr4,    sizeof(this->cr4));
        std::memcpy(this->cr5,     other.cr5,    sizeof(this->cr5));
        std::memcpy(this->cr6,     other.cr6,    sizeof(this->cr6));
        std::memcpy(this->cr7,     other.cr7,    sizeof(this->cr7));
        std::memcpy(this->cr8,     other.cr8,    sizeof(this->cr8));
        std::memcpy(this->cr9,     other.cr9,    sizeof(this->cr9));
        std::memcpy(this->cr10,    other.cr10,   sizeof(this->cr10));
        std::memcpy(this->cr11,    other.cr11,   sizeof(this->cr11));
        std::memcpy(this->cr12,    other.cr12,   sizeof(this->cr12));
        std::memcpy(this->cr13,    other.cr13,   sizeof(this->cr13));
        std::memcpy(this->cr14,    other.cr14,   sizeof(this->cr14));
        std::memcpy(this->cr15,    other.cr15,   sizeof(this->cr15));
        std::memcpy(this->cs,      other.cs,     sizeof(this->cs));
        std::memcpy(this->ds,      other.ds,     sizeof(this->ds));
        std::memcpy(this->es,      other.es,     sizeof(this->es));
        std::memcpy(this->fs,      other.fs,     sizeof(this->fs));
        std::memcpy(this->gs,      other.gs,     sizeof(this->gs));
        std::memcpy(this->ss,      other.ss,     sizeof(this->ss));
      }


      void x86Cpu::clear(void) {
        /* Clear memory */
        this->memory.clear();

        /* Clear registers */
        std::memset(this->eax,     0x00, sizeof(this->eax));
        std::memset(this->ebx,     0x00, sizeof(this->ebx));
        std::memset(this->ecx,     0x00, sizeof(this->ecx));
        std::memset(this->edx,     0x00, sizeof(this->edx));
        std::memset(this->edi,     0x00, sizeof(this->edi));
        std::memset(this->esi,     0x00, sizeof(this->esi));
        std::memset(this->esp,     0x00, sizeof(this->esp));
        std::memset(this->ebp,     0x00, sizeof(this->ebp));
        std::memset(this->eip,     0x00, sizeof(this->eip));
        std::memset(this->eflags,  0x00, sizeof(this->eflags));
        std::memset(this->mm0,     0x00, sizeof(this->mm0));
        std::memset(this->mm1,     0x00, sizeof(this->mm1));
        std::memset(this->mm2,     0x00, sizeof(this->mm2));
        std::memset(this->mm3,     0x00, sizeof(this->mm3));
        std::memset(this->mm4,     0x00, sizeof(this->mm4));
        std::memset(this->mm5,     0x00, sizeof(this->mm5));
        std::memset(this->mm6,     0x00, sizeof(this->mm6));
        std::memset(this->mm7,     0x00, sizeof(this->mm7));
        std::memset(this->xmm0,    0x00, sizeof(this->xmm0));
        std::memset(this->xmm1,    0x00, sizeof(this->xmm1));
        std::memset(this->xmm2,    0x00, sizeof(this->xmm2));
        std::memset(this->xmm3,    0x00, sizeof(this->xmm3));
        std::memset(this->xmm4,    0x00, sizeof(this->xmm4));
        std::memset(this->xmm5,    0x00, sizeof(this->xmm5));
        std::memset(this->xmm6,    0x00, sizeof(this->xmm6));
        std::memset(this->xmm7,    0x00, sizeof(this->xmm7));
        std::memset(this->ymm0,    0x00, sizeof(this->ymm0));
        std::memset(this->ymm1,    0x00, sizeof(this->ymm1));
        std::memset(this->ymm2,    0x00, sizeof(this->ymm2));
        std::memset(this->ymm3,    0x00, sizeof(this->ymm3));
        std::memset(this->ymm4,    0x00, sizeof(this->ymm4));
        std::memset(this->ymm5,    0x00, sizeof(this->ymm5));
        std::memset(this->ymm6,    0x00, sizeof(this->ymm6));
        std::memset(this->ymm7,    0x00, sizeof(this->ymm7));
        std::memset(this->mxcsr,   0x00, sizeof(this->mxcsr));
        std::memset(this->cr0,     0x00, sizeof(this->cr0));
        std::memset(this->cr1,     0x00, sizeof(this->cr1));
        std::memset(this->cr2,     0x00, sizeof(this->cr2));
        std::memset(this->cr3,     0x00, sizeof(this->cr3));
        std::memset(this->cr4,     0x00, sizeof(this->cr4));
        std::memset(this->cr5,     0x00, sizeof(this->cr5));
        std::memset(this->cr6,     0x00, sizeof(this->cr6));
        std::memset(this->cr7,     0x00, sizeof(this->cr7));
        std::memset(this->cr8,     0x00, sizeof(this->cr8));
        std::memset(this->cr9,     0x00, sizeof(this->cr9));
        std::memset(this->cr10,    0x00, sizeof(this->cr10));
        std::memset(this->cr11,    0x00, sizeof(this->cr11));
        std::memset(this->cr12,    0x00, sizeof(this->cr12));
        std::memset(this->cr13,    0x00, sizeof(this->cr13));
        std::memset(this->cr14,    0x00, sizeof(this->cr14));
        std::memset(this->cr15,    0x00, sizeof(this->cr15));
        std::memset(this->cs,      0x00, sizeof(this->cs));
        std::memset(this->ds,      0x00, sizeof(this->ds));
        std::memset(this->es,      0x00, sizeof(this->es));
        std::memset(this->fs,      0x00, sizeof(this->fs));
        std::memset(this->gs,      0x00, sizeof(this->gs));
        std::memset(this->ss,      0x00, sizeof(this->ss));
      }


      void x86Cpu::operator=(const x86Cpu& other) {
        this->copy(other);
      }


      bool x86Cpu::isFlag(triton::arch::registers_e regId) const {
        return ((regId >= triton::arch::ID_REG_AF && regId <= triton::arch::ID_REG_FZ) ? true : false);
      }


      bool x86Cpu::isRegister(triton::arch::registers_e regId) const {
        return (
          this->isGPR(regId)      ||
          this->isMMX(regId)      ||
          this->isSSE(regId)      ||
          this->isAVX256(regId)   ||
          this->isControl(regId)  ||
          this->isSegment(regId)
        );
      }


      bool x86Cpu::isRegisterValid(triton::arch::registers_e regId) const {
        return (this->isFlag(regId) || this->isRegister(regId));
      }


      bool x86Cpu::isGPR(triton::arch::registers_e regId) const {
        return ((regId >= triton::arch::ID_REG_EAX && regId <= triton::arch::ID_REG_EFLAGS) ? true : false);
      }


      bool x86Cpu::isMMX(triton::arch::registers_e regId) const {
        return ((regId >= triton::arch::ID_REG_MM0 && regId <= triton::arch::ID_REG_MM7) ? true : false);
      }


      bool x86Cpu::isSSE(triton::arch::registers_e regId) const {
        return ((regId >= triton::arch::ID_REG_MXCSR && regId <= triton::arch::ID_REG_XMM7) ? true : false);
      }


      bool x86Cpu::isAVX256(triton::arch::registers_e regId) const {
        return ((regId >= triton::arch::ID_REG_YMM0 && regId <= triton::arch::ID_REG_YMM7) ? true : false);
      }


      bool x86Cpu::isControl(triton::arch::registers_e regId) const {
        return ((regId >= triton::arch::ID_REG_CR0 && regId <= triton::arch::ID_REG_CR15) ? true : false);
      }


      bool x86Cpu::isSegment(triton::arch::registers_e regId) const {
        return ((regId >= triton::arch::ID_REG_CS && regId <= triton::arch::ID_REG_SS) ? true : false);
      }


      triton::uint32 x86Cpu::numberOfRegisters(void) const {
        return triton::arch::ID_REG_LAST_ITEM;
      }


      triton::uint32 x86Cpu::registerSize(void) const {
        return DWORD_SIZE;
      }


      triton::uint32 x86Cpu::registerBitSize(void) const {
        return DWORD_SIZE_BIT;
      }



      const std::unordered_map<registers_e, const triton::arch::Register>& x86Cpu::getAllRegisters(void) const {
        return this->registers_;
      }


      std::set<const triton::arch::Register*> x86Cpu::getParentRegisters(void) const {
        std::set<const triton::arch::Register*> ret;

        for (const auto& kv: this->registers_) {
          auto regId = kv.first;
          const auto& reg = kv.second;

          /* Add GPR */
          if (reg.getSize() == this->registerSize())
            ret.insert(&reg);

          /* Add Flags */
          else if (this->isFlag(regId))
            ret.insert(&reg);

          /* Add MMX */
          else if (this->isMMX(regId))
            ret.insert(&reg);

          /* Add SSE */
          else if (this->isSSE(regId))
            ret.insert(&reg);

          /* Add AVX-256 */
          else if (this->isAVX256(regId))
            ret.insert(&reg);

          /* Add Control */
          else if (this->isControl(regId))
            ret.insert(&reg);
        }

        return ret;
      }


      const triton::arch::Register& x86Cpu::getRegister(triton::arch::registers_e id) const {
        try {
          return this->registers_.at(id);
        } catch(const std::out_of_range& e) {
          throw triton::exceptions::Cpu("x86Cpu::getRegister(): Invalid register for this architecture.");
        }
      }


      const triton::arch::Register& x86Cpu::getParentRegister(const triton::arch::Register& reg) const {
        return this->getRegister(reg.getParent());
      }


      const triton::arch::Register& x86Cpu::getParentRegister(triton::arch::registers_e id) const {
        return this->getParentRegister(this->getRegister(id));
      }


      void x86Cpu::disassembly(triton::arch::Instruction& inst) const {
        triton::extlibs::capstone::csh       handle;
        triton::extlibs::capstone::cs_insn*  insn;
        triton::usize                        count = 0;

        /* Check if the opcode and opcode' size are defined */
        if (inst.getOpcode() == nullptr || inst.getSize() == 0)
          throw triton::exceptions::Disassembly("x86Cpu::disassembly(): Opcode and opcodeSize must be definied.");

        /* Open capstone */
        if (triton::extlibs::capstone::cs_open(triton::extlibs::capstone::CS_ARCH_X86, triton::extlibs::capstone::CS_MODE_32, &handle) != triton::extlibs::capstone::CS_ERR_OK)
          throw triton::exceptions::Disassembly("x86Cpu::disassembly(): Cannot open capstone.");

        /* Init capstone's options */
        triton::extlibs::capstone::cs_option(handle, triton::extlibs::capstone::CS_OPT_DETAIL, triton::extlibs::capstone::CS_OPT_ON);
        triton::extlibs::capstone::cs_option(handle, triton::extlibs::capstone::CS_OPT_SYNTAX, triton::extlibs::capstone::CS_OPT_SYNTAX_INTEL);

        /* Clear instructicon's operands if alredy defined */
        inst.operands.clear();

        /* Let's disass and build our operands */
        count = triton::extlibs::capstone::cs_disasm(handle, inst.getOpcode(), inst.getSize(), inst.getAddress(), 0, &insn);
        if (count > 0) {
          triton::extlibs::capstone::cs_detail* detail = insn->detail;
          for (triton::uint32 j = 0; j < 1; j++) {

            /* Init the disassembly */
            std::stringstream str;

            /* Add mnemonic */
            str << insn[j].mnemonic;

            /* Add operands */
            if (detail->x86.op_count)
              str << " " <<  insn[j].op_str;

            inst.setDisassembly(str.str());

            /* Refine the size */
            inst.setSize(insn[j].size);

            /* Init the instruction's type */
            inst.setType(this->capstoneInstructionToTritonInstruction(insn[j].id));

            /* Init the instruction's prefix */
            inst.setPrefix(this->capstonePrefixToTritonPrefix(detail->x86.prefix[0]));

            /* Init operands */
            for (triton::uint32 n = 0; n < detail->x86.op_count; n++) {
              triton::extlibs::capstone::cs_x86_op* op = &(detail->x86.operands[n]);
              switch(op->type) {

                case triton::extlibs::capstone::X86_OP_IMM:
                  inst.operands.push_back(triton::arch::OperandWrapper(triton::arch::Immediate(op->imm, op->size)));
                  break;

                case triton::extlibs::capstone::X86_OP_MEM: {
                  triton::arch::MemoryAccess mem;

                  /* Set the size of the memory access */
                  mem.setPair(std::make_pair(((op->size * BYTE_SIZE_BIT) - 1), 0));

                  /* LEA if exists */
                  const triton::arch::Register segment(*this, this->capstoneRegisterToTritonRegister(op->mem.segment));
                  const triton::arch::Register base(*this, this->capstoneRegisterToTritonRegister(op->mem.base));
                  const triton::arch::Register index(*this, this->capstoneRegisterToTritonRegister(op->mem.index));

                  triton::uint32 immsize = (
                                            this->isRegisterValid(base.getId()) ? base.getSize() :
                                            this->isRegisterValid(index.getId()) ? index.getSize() :
                                            this->registerSize()
                                          );

                  triton::arch::Immediate disp(op->mem.disp, immsize);
                  triton::arch::Immediate scale(op->mem.scale, immsize);

                  /* Specify that LEA contains a PC relative */
                  if (base.getId() == pcId)
                    mem.setPcRelative(inst.getNextAddress());

                  mem.setSegmentRegister(segment);
                  mem.setBaseRegister(base);
                  mem.setIndexRegister(index);
                  mem.setDisplacement(disp);
                  mem.setScale(scale);

                  inst.operands.push_back(triton::arch::OperandWrapper(mem));
                  break;
                }

                case triton::extlibs::capstone::X86_OP_REG:
                  inst.operands.push_back(triton::arch::OperandWrapper(triton::arch::Register(*this, this->capstoneRegisterToTritonRegister(op->reg))));
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
          throw triton::exceptions::Disassembly("x86Cpu::disassembly(): Failed to disassemble the given code.");

        triton::extlibs::capstone::cs_close(&handle);
        return;
      }


      triton::uint8 x86Cpu::getConcreteMemoryValue(triton::uint64 addr) const {
        auto it = this->memory.find(addr);
        if (it == this->memory.end())
          return 0x00;
        return it->second;
      }


      triton::uint512 x86Cpu::getConcreteMemoryValue(const triton::arch::MemoryAccess& mem, bool execCallbacks) const {
        triton::uint512 ret = 0;
        triton::uint64 addr = mem.getAddress();
        triton::uint32 size = mem.getSize();

        if (size == 0 || size > DQQWORD_SIZE)
          throw triton::exceptions::Cpu("x86Cpu::getConcreteMemoryValue(): Invalid size memory.");

        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_MEMORY_VALUE, mem);

        for (triton::sint32 i = size-1; i >= 0; i--)
          ret = ((ret << BYTE_SIZE_BIT) | this->getConcreteMemoryValue(addr+i));

        return ret;
      }


      std::vector<triton::uint8> x86Cpu::getConcreteMemoryAreaValue(triton::uint64 baseAddr, triton::usize size, bool execCallbacks) const {
        std::vector<triton::uint8> area;

        for (triton::usize index = 0; index < size; index++) {
          if (execCallbacks && this->callbacks)
            this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_MEMORY_VALUE, MemoryAccess(baseAddr+index, BYTE_SIZE));
          area.push_back(this->getConcreteMemoryValue(baseAddr+index));
        }

        return area;
      }


      triton::uint512 x86Cpu::getConcreteRegisterValue(const triton::arch::Register& reg, bool execCallbacks) const {
        triton::uint512 value = 0;

        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_REGISTER_VALUE, reg);

        switch (reg.getId()) {
          case triton::arch::ID_REG_EAX: return (*((triton::uint32*)(this->eax)));
          case triton::arch::ID_REG_AX:  return (*((triton::uint16*)(this->eax)));
          case triton::arch::ID_REG_AH:  return (*((triton::uint8*)(this->eax+1)));
          case triton::arch::ID_REG_AL:  return (*((triton::uint8*)(this->eax)));

          case triton::arch::ID_REG_EBX: return (*((triton::uint32*)(this->ebx)));
          case triton::arch::ID_REG_BX:  return (*((triton::uint16*)(this->ebx)));
          case triton::arch::ID_REG_BH:  return (*((triton::uint8*)(this->ebx+1)));
          case triton::arch::ID_REG_BL:  return (*((triton::uint8*)(this->ebx)));

          case triton::arch::ID_REG_ECX: return (*((triton::uint32*)(this->ecx)));
          case triton::arch::ID_REG_CX:  return (*((triton::uint16*)(this->ecx)));
          case triton::arch::ID_REG_CH:  return (*((triton::uint8*)(this->ecx+1)));
          case triton::arch::ID_REG_CL:  return (*((triton::uint8*)(this->ecx)));

          case triton::arch::ID_REG_EDX: return (*((triton::uint32*)(this->edx)));
          case triton::arch::ID_REG_DX:  return (*((triton::uint16*)(this->edx)));
          case triton::arch::ID_REG_DH:  return (*((triton::uint8*)(this->edx+1)));
          case triton::arch::ID_REG_DL:  return (*((triton::uint8*)(this->edx)));

          case triton::arch::ID_REG_EDI: return (*((triton::uint32*)(this->edi)));
          case triton::arch::ID_REG_DI:  return (*((triton::uint16*)(this->edi)));
          case triton::arch::ID_REG_DIL: return (*((triton::uint8*)(this->edi)));

          case triton::arch::ID_REG_ESI: return (*((triton::uint32*)(this->esi)));
          case triton::arch::ID_REG_SI:  return (*((triton::uint16*)(this->esi)));
          case triton::arch::ID_REG_SIL: return (*((triton::uint8*)(this->esi)));

          case triton::arch::ID_REG_ESP: return (*((triton::uint32*)(this->esp)));
          case triton::arch::ID_REG_SP:  return (*((triton::uint16*)(this->esp)));
          case triton::arch::ID_REG_SPL: return (*((triton::uint8*)(this->esp)));

          case triton::arch::ID_REG_EBP: return (*((triton::uint32*)(this->ebp)));
          case triton::arch::ID_REG_BP:  return (*((triton::uint16*)(this->ebp)));
          case triton::arch::ID_REG_BPL: return (*((triton::uint8*)(this->ebp)));

          case triton::arch::ID_REG_EIP: return (*((triton::uint32*)(this->eip)));
          case triton::arch::ID_REG_IP:  return (*((triton::uint16*)(this->eip)));

          case triton::arch::ID_REG_EFLAGS: return (*((triton::uint32*)(this->eflags)));

          case triton::arch::ID_REG_MM0:  return (*((triton::uint64*)(this->mm0)));
          case triton::arch::ID_REG_MM1:  return (*((triton::uint64*)(this->mm1)));
          case triton::arch::ID_REG_MM2:  return (*((triton::uint64*)(this->mm2)));
          case triton::arch::ID_REG_MM3:  return (*((triton::uint64*)(this->mm3)));
          case triton::arch::ID_REG_MM4:  return (*((triton::uint64*)(this->mm4)));
          case triton::arch::ID_REG_MM5:  return (*((triton::uint64*)(this->mm5)));
          case triton::arch::ID_REG_MM6:  return (*((triton::uint64*)(this->mm6)));
          case triton::arch::ID_REG_MM7:  return (*((triton::uint64*)(this->mm7)));

          case triton::arch::ID_REG_XMM0: value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm0); return value;
          case triton::arch::ID_REG_XMM1: value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm1); return value;
          case triton::arch::ID_REG_XMM2: value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm2); return value;
          case triton::arch::ID_REG_XMM3: value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm3); return value;
          case triton::arch::ID_REG_XMM4: value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm4); return value;
          case triton::arch::ID_REG_XMM5: value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm5); return value;
          case triton::arch::ID_REG_XMM6: value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm6); return value;
          case triton::arch::ID_REG_XMM7: value = triton::utils::fromBufferToUint<triton::uint128>(this->xmm7); return value;

          case triton::arch::ID_REG_YMM0: value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm0); return value;
          case triton::arch::ID_REG_YMM1: value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm1); return value;
          case triton::arch::ID_REG_YMM2: value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm2); return value;
          case triton::arch::ID_REG_YMM3: value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm3); return value;
          case triton::arch::ID_REG_YMM4: value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm4); return value;
          case triton::arch::ID_REG_YMM5: value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm5); return value;
          case triton::arch::ID_REG_YMM6: value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm6); return value;
          case triton::arch::ID_REG_YMM7: value = triton::utils::fromBufferToUint<triton::uint256>(this->ymm7); return value;

          case triton::arch::ID_REG_MXCSR: return (*((triton::uint32*)(this->mxcsr)));

          case triton::arch::ID_REG_CR0:  return (*((triton::uint32*)(this->cr0)));
          case triton::arch::ID_REG_CR1:  return (*((triton::uint32*)(this->cr1)));
          case triton::arch::ID_REG_CR2:  return (*((triton::uint32*)(this->cr2)));
          case triton::arch::ID_REG_CR3:  return (*((triton::uint32*)(this->cr3)));
          case triton::arch::ID_REG_CR4:  return (*((triton::uint32*)(this->cr4)));
          case triton::arch::ID_REG_CR5:  return (*((triton::uint32*)(this->cr5)));
          case triton::arch::ID_REG_CR6:  return (*((triton::uint32*)(this->cr6)));
          case triton::arch::ID_REG_CR7:  return (*((triton::uint32*)(this->cr7)));
          case triton::arch::ID_REG_CR8:  return (*((triton::uint32*)(this->cr8)));
          case triton::arch::ID_REG_CR9:  return (*((triton::uint32*)(this->cr9)));
          case triton::arch::ID_REG_CR10: return (*((triton::uint32*)(this->cr10)));
          case triton::arch::ID_REG_CR11: return (*((triton::uint32*)(this->cr11)));
          case triton::arch::ID_REG_CR12: return (*((triton::uint32*)(this->cr12)));
          case triton::arch::ID_REG_CR13: return (*((triton::uint32*)(this->cr13)));
          case triton::arch::ID_REG_CR14: return (*((triton::uint32*)(this->cr14)));
          case triton::arch::ID_REG_CR15: return (*((triton::uint32*)(this->cr15)));

          case triton::arch::ID_REG_IE:  return (((*((triton::uint32*)(this->mxcsr))) >> 0) & 1);
          case triton::arch::ID_REG_DE:  return (((*((triton::uint32*)(this->mxcsr))) >> 1) & 1);
          case triton::arch::ID_REG_ZE:  return (((*((triton::uint32*)(this->mxcsr))) >> 2) & 1);
          case triton::arch::ID_REG_OE:  return (((*((triton::uint32*)(this->mxcsr))) >> 3) & 1);
          case triton::arch::ID_REG_UE:  return (((*((triton::uint32*)(this->mxcsr))) >> 4) & 1);
          case triton::arch::ID_REG_PE:  return (((*((triton::uint32*)(this->mxcsr))) >> 5) & 1);
          case triton::arch::ID_REG_DAZ: return (((*((triton::uint32*)(this->mxcsr))) >> 6) & 1);
          case triton::arch::ID_REG_IM:  return (((*((triton::uint32*)(this->mxcsr))) >> 7) & 1);
          case triton::arch::ID_REG_DM:  return (((*((triton::uint32*)(this->mxcsr))) >> 8) & 1);
          case triton::arch::ID_REG_ZM:  return (((*((triton::uint32*)(this->mxcsr))) >> 9) & 1);
          case triton::arch::ID_REG_OM:  return (((*((triton::uint32*)(this->mxcsr))) >> 10) & 1);
          case triton::arch::ID_REG_UM:  return (((*((triton::uint32*)(this->mxcsr))) >> 11) & 1);
          case triton::arch::ID_REG_PM:  return (((*((triton::uint32*)(this->mxcsr))) >> 12) & 1);
          case triton::arch::ID_REG_RL:  return (((*((triton::uint32*)(this->mxcsr))) >> 13) & 1);
          case triton::arch::ID_REG_RH:  return (((*((triton::uint32*)(this->mxcsr))) >> 14) & 1);
          case triton::arch::ID_REG_FZ:  return (((*((triton::uint32*)(this->mxcsr))) >> 15) & 1);

          case triton::arch::ID_REG_CF: return (((*((triton::uint32*)(this->eflags))) >> 0) & 1);
          case triton::arch::ID_REG_PF: return (((*((triton::uint32*)(this->eflags))) >> 2) & 1);
          case triton::arch::ID_REG_AF: return (((*((triton::uint32*)(this->eflags))) >> 4) & 1);
          case triton::arch::ID_REG_ZF: return (((*((triton::uint32*)(this->eflags))) >> 6) & 1);
          case triton::arch::ID_REG_SF: return (((*((triton::uint32*)(this->eflags))) >> 7) & 1);
          case triton::arch::ID_REG_TF: return (((*((triton::uint32*)(this->eflags))) >> 8) & 1);
          case triton::arch::ID_REG_IF: return (((*((triton::uint32*)(this->eflags))) >> 9) & 1);
          case triton::arch::ID_REG_DF: return (((*((triton::uint32*)(this->eflags))) >> 10) & 1);
          case triton::arch::ID_REG_OF: return (((*((triton::uint32*)(this->eflags))) >> 11) & 1);

          case triton::arch::ID_REG_CS: return (*((triton::uint32*)(this->cs)));
          case triton::arch::ID_REG_DS: return (*((triton::uint32*)(this->ds)));
          case triton::arch::ID_REG_ES: return (*((triton::uint32*)(this->es)));
          case triton::arch::ID_REG_FS: return (*((triton::uint32*)(this->fs)));
          case triton::arch::ID_REG_GS: return (*((triton::uint32*)(this->gs)));
          case triton::arch::ID_REG_SS: return (*((triton::uint32*)(this->ss)));

          default:
            throw triton::exceptions::Cpu("x86Cpu::getConcreteRegisterValue(): Invalid register.");
        }

        return value;
      }


      void x86Cpu::setConcreteMemoryValue(triton::uint64 addr, triton::uint8 value) {
        this->memory[addr] = value;
      }


      void x86Cpu::setConcreteMemoryValue(const triton::arch::MemoryAccess& mem, const triton::uint512& value) {
        triton::uint64 addr = mem.getAddress();
        triton::uint32 size = mem.getSize();
        triton::uint512 cv  = value;

        if (cv > mem.getMaxValue())
          throw triton::exceptions::Register("x86Cpu::setConcreteMemoryValue(): You cannot set this concrete value (too big) to this memory access.");

        if (size == 0 || size > DQQWORD_SIZE)
          throw triton::exceptions::Cpu("x86Cpu::setConcreteMemoryValue(): Invalid size memory.");

        for (triton::uint32 i = 0; i < size; i++) {
          this->memory[addr+i] = (cv & 0xff).convert_to<triton::uint8>();
          cv >>= 8;
        }
      }


      void x86Cpu::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const std::vector<triton::uint8>& values) {
        for (triton::usize index = 0; index < values.size(); index++) {
          this->memory[baseAddr+index] = values[index];
        }
      }


      void x86Cpu::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const triton::uint8* area, triton::usize size) {
        for (triton::usize index = 0; index < size; index++) {
          this->memory[baseAddr+index] = area[index];
        }
      }


      void x86Cpu::setConcreteRegisterValue(const triton::arch::Register& reg, const triton::uint512& value) {
        if (value > reg.getMaxValue())
          throw triton::exceptions::Register("x86Cpu::setConcreteRegisterValue(): You cannot set this concrete value (too big) to this register.");

        switch (reg.getId()) {
          case triton::arch::ID_REG_EAX: (*((triton::uint32*)(this->eax)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_AX:  (*((triton::uint16*)(this->eax)))  = value.convert_to<triton::uint16>(); break;
          case triton::arch::ID_REG_AH:  (*((triton::uint8*)(this->eax+1))) = value.convert_to<triton::uint8>(); break;
          case triton::arch::ID_REG_AL:  (*((triton::uint8*)(this->eax)))   = value.convert_to<triton::uint8>(); break;

          case triton::arch::ID_REG_EBX: (*((triton::uint32*)(this->ebx)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_BX:  (*((triton::uint16*)(this->ebx)))  = value.convert_to<triton::uint16>(); break;
          case triton::arch::ID_REG_BH:  (*((triton::uint8*)(this->ebx+1))) = value.convert_to<triton::uint8>(); break;
          case triton::arch::ID_REG_BL:  (*((triton::uint8*)(this->ebx)))   = value.convert_to<triton::uint8>(); break;

          case triton::arch::ID_REG_ECX: (*((triton::uint32*)(this->ecx)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_CX:  (*((triton::uint16*)(this->ecx)))  = value.convert_to<triton::uint16>(); break;
          case triton::arch::ID_REG_CH:  (*((triton::uint8*)(this->ecx+1))) = value.convert_to<triton::uint8>(); break;
          case triton::arch::ID_REG_CL:  (*((triton::uint8*)(this->ecx)))   = value.convert_to<triton::uint8>(); break;

          case triton::arch::ID_REG_EDX: (*((triton::uint32*)(this->edx)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_DX:  (*((triton::uint16*)(this->edx)))  = value.convert_to<triton::uint16>(); break;
          case triton::arch::ID_REG_DH:  (*((triton::uint8*)(this->edx+1))) = value.convert_to<triton::uint8>(); break;
          case triton::arch::ID_REG_DL:  (*((triton::uint8*)(this->edx)))   = value.convert_to<triton::uint8>(); break;

          case triton::arch::ID_REG_EDI: (*((triton::uint32*)(this->edi)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_DI:  (*((triton::uint16*)(this->edi)))  = value.convert_to<triton::uint16>(); break;
          case triton::arch::ID_REG_DIL: (*((triton::uint8*)(this->edi)))   = value.convert_to<triton::uint8>(); break;

          case triton::arch::ID_REG_ESI: (*((triton::uint32*)(this->esi)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_SI:  (*((triton::uint16*)(this->esi)))  = value.convert_to<triton::uint16>(); break;
          case triton::arch::ID_REG_SIL: (*((triton::uint8*)(this->esi)))   = value.convert_to<triton::uint8>(); break;

          case triton::arch::ID_REG_ESP: (*((triton::uint32*)(this->esp)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_SP:  (*((triton::uint16*)(this->esp)))  = value.convert_to<triton::uint16>(); break;
          case triton::arch::ID_REG_SPL: (*((triton::uint8*)(this->esp)))   = value.convert_to<triton::uint8>(); break;

          case triton::arch::ID_REG_EBP: (*((triton::uint32*)(this->ebp)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_BP:  (*((triton::uint16*)(this->ebp)))  = value.convert_to<triton::uint16>(); break;
          case triton::arch::ID_REG_BPL: (*((triton::uint8*)(this->ebp)))   = value.convert_to<triton::uint8>(); break;

          case triton::arch::ID_REG_EIP: (*((triton::uint32*)(this->eip)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_IP:  (*((triton::uint16*)(this->eip)))  = value.convert_to<triton::uint16>(); break;

          case triton::arch::ID_REG_EFLAGS: (*((triton::uint32*)(this->eflags))) = value.convert_to<triton::uint32>(); break;

          case triton::arch::ID_REG_CF: {
            triton::uint32 b = (*((triton::uint32*)(this->eflags)));
            (*((triton::uint32*)(this->eflags))) = !value.is_zero() ? b | (1 << 0) : b & ~(1 << 0);
            break;
          }
          case triton::arch::ID_REG_PF: {
            triton::uint32 b = (*((triton::uint32*)(this->eflags)));
            (*((triton::uint32*)(this->eflags))) = !value.is_zero() ? b | (1 << 2) : b & ~(1 << 2);
            break;
          }
          case triton::arch::ID_REG_AF: {
            triton::uint32 b = (*((triton::uint32*)(this->eflags)));
            (*((triton::uint32*)(this->eflags))) = !value.is_zero() ? b | (1 << 4) : b & ~(1 << 4);
            break;
          }
          case triton::arch::ID_REG_ZF: {
            triton::uint32 b = (*((triton::uint32*)(this->eflags)));
            (*((triton::uint32*)(this->eflags))) = !value.is_zero() ? b | (1 << 6) : b & ~(1 << 6);
            break;
          }
          case triton::arch::ID_REG_SF: {
            triton::uint32 b = (*((triton::uint32*)(this->eflags)));
            (*((triton::uint32*)(this->eflags))) = !value.is_zero() ? b | (1 << 7) : b & ~(1 << 7);
            break;
          }
          case triton::arch::ID_REG_TF: {
            triton::uint32 b = (*((triton::uint32*)(this->eflags)));
            (*((triton::uint32*)(this->eflags))) = !value.is_zero() ? b | (1 << 8) : b & ~(1 << 8);
            break;
          }
          case triton::arch::ID_REG_IF: {
            triton::uint32 b = (*((triton::uint32*)(this->eflags)));
            (*((triton::uint32*)(this->eflags))) = !value.is_zero() ? b | (1 << 9) : b & ~(1 << 9);
            break;
          }
          case triton::arch::ID_REG_DF: {
            triton::uint32 b = (*((triton::uint32*)(this->eflags)));
            (*((triton::uint32*)(this->eflags))) = !value.is_zero() ? b | (1 << 10) : b & ~(1 << 10);
            break;
          }
          case triton::arch::ID_REG_OF: {
            triton::uint32 b = (*((triton::uint32*)(this->eflags)));
            (*((triton::uint32*)(this->eflags))) = !value.is_zero() ? b | (1 << 11) : b & ~(1 << 11);
            break;
          }

          case triton::arch::ID_REG_MM0:  (*((triton::uint64*)(this->mm0))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_MM1:  (*((triton::uint64*)(this->mm1))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_MM2:  (*((triton::uint64*)(this->mm2))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_MM3:  (*((triton::uint64*)(this->mm3))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_MM4:  (*((triton::uint64*)(this->mm4))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_MM5:  (*((triton::uint64*)(this->mm5))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_MM6:  (*((triton::uint64*)(this->mm6))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_MM7:  (*((triton::uint64*)(this->mm7))) = value.convert_to<triton::uint64>(); break;

          case triton::arch::ID_REG_XMM0: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm0); break;
          case triton::arch::ID_REG_XMM1: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm1); break;
          case triton::arch::ID_REG_XMM2: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm2); break;
          case triton::arch::ID_REG_XMM3: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm3); break;
          case triton::arch::ID_REG_XMM4: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm4); break;
          case triton::arch::ID_REG_XMM5: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm5); break;
          case triton::arch::ID_REG_XMM6: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm6); break;
          case triton::arch::ID_REG_XMM7: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->xmm7); break;

          case triton::arch::ID_REG_YMM0: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm0); break;
          case triton::arch::ID_REG_YMM1: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm1); break;
          case triton::arch::ID_REG_YMM2: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm2); break;
          case triton::arch::ID_REG_YMM3: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm3); break;
          case triton::arch::ID_REG_YMM4: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm4); break;
          case triton::arch::ID_REG_YMM5: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm5); break;
          case triton::arch::ID_REG_YMM6: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm6); break;
          case triton::arch::ID_REG_YMM7: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->ymm7); break;

          case triton::arch::ID_REG_MXCSR: (*((triton::uint32*)(this->mxcsr))) = value.convert_to<triton::uint32>(); break;

          case triton::arch::ID_REG_IE: {
            triton::uint32 b = (*((triton::uint32*)(this->mxcsr)));
            (*((triton::uint32*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 0) : b & ~(1 << 0);
            break;
          }
          case triton::arch::ID_REG_DE: {
            triton::uint32 b = (*((triton::uint32*)(this->mxcsr)));
            (*((triton::uint32*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 1) : b & ~(1 << 1);
            break;
          }
          case triton::arch::ID_REG_ZE: {
            triton::uint32 b = (*((triton::uint32*)(this->mxcsr)));
            (*((triton::uint32*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 2) : b & ~(1 << 2);
            break;
          }
          case triton::arch::ID_REG_OE: {
            triton::uint32 b = (*((triton::uint32*)(this->mxcsr)));
            (*((triton::uint32*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 3) : b & ~(1 << 3);
            break;
          }
          case triton::arch::ID_REG_UE: {
            triton::uint32 b = (*((triton::uint32*)(this->mxcsr)));
            (*((triton::uint32*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 4) : b & ~(1 << 4);
            break;
          }
          case triton::arch::ID_REG_PE: {
            triton::uint32 b = (*((triton::uint32*)(this->mxcsr)));
            (*((triton::uint32*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 5) : b & ~(1 << 5);
            break;
          }
          case triton::arch::ID_REG_DAZ: {
            triton::uint32 b = (*((triton::uint32*)(this->mxcsr)));
            (*((triton::uint32*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 6) : b & ~(1 << 6);
            break;
          }
          case triton::arch::ID_REG_IM: {
            triton::uint32 b = (*((triton::uint32*)(this->mxcsr)));
            (*((triton::uint32*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 7) : b & ~(1 << 7);
            break;
          }
          case triton::arch::ID_REG_DM: {
            triton::uint32 b = (*((triton::uint32*)(this->mxcsr)));
            (*((triton::uint32*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 8) : b & ~(1 << 8);
            break;
          }
          case triton::arch::ID_REG_ZM: {
            triton::uint32 b = (*((triton::uint32*)(this->mxcsr)));
            (*((triton::uint32*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 9) : b & ~(1 << 9);
            break;
          }
          case triton::arch::ID_REG_OM: {
            triton::uint32 b = (*((triton::uint32*)(this->mxcsr)));
            (*((triton::uint32*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 10) : b & ~(1 << 10);
            break;
          }
          case triton::arch::ID_REG_UM: {
            triton::uint32 b = (*((triton::uint32*)(this->mxcsr)));
            (*((triton::uint32*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 11) : b & ~(1 << 11);
            break;
          }
          case triton::arch::ID_REG_PM: {
            triton::uint32 b = (*((triton::uint32*)(this->mxcsr)));
            (*((triton::uint32*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 12) : b & ~(1 << 12);
            break;
          }
          case triton::arch::ID_REG_RL: {
            triton::uint32 b = (*((triton::uint32*)(this->mxcsr)));
            (*((triton::uint32*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 13) : b & ~(1 << 13);
            break;
          }
          case triton::arch::ID_REG_RH: {
            triton::uint32 b = (*((triton::uint32*)(this->mxcsr)));
            (*((triton::uint32*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 14) : b & ~(1 << 14);
            break;
          }
          case triton::arch::ID_REG_FZ: {
            triton::uint32 b = (*((triton::uint32*)(this->mxcsr)));
            (*((triton::uint32*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 15) : b & ~(1 << 15);
            break;
          }

          case triton::arch::ID_REG_CR0:  (*((triton::uint32*)(this->cr0)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_CR1:  (*((triton::uint32*)(this->cr1)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_CR2:  (*((triton::uint32*)(this->cr2)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_CR3:  (*((triton::uint32*)(this->cr3)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_CR4:  (*((triton::uint32*)(this->cr4)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_CR5:  (*((triton::uint32*)(this->cr5)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_CR6:  (*((triton::uint32*)(this->cr6)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_CR7:  (*((triton::uint32*)(this->cr7)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_CR8:  (*((triton::uint32*)(this->cr8)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_CR9:  (*((triton::uint32*)(this->cr9)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_CR10: (*((triton::uint32*)(this->cr10))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_CR11: (*((triton::uint32*)(this->cr11))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_CR12: (*((triton::uint32*)(this->cr12))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_CR13: (*((triton::uint32*)(this->cr13))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_CR14: (*((triton::uint32*)(this->cr14))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_CR15: (*((triton::uint32*)(this->cr15))) = value.convert_to<triton::uint32>(); break;

          case triton::arch::ID_REG_CS:  (*((triton::uint32*)(this->cs))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_DS:  (*((triton::uint32*)(this->ds))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_ES:  (*((triton::uint32*)(this->es))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_FS:  (*((triton::uint32*)(this->fs))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_GS:  (*((triton::uint32*)(this->gs))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_SS:  (*((triton::uint32*)(this->ss))) = value.convert_to<triton::uint32>(); break;

          default:
            throw triton::exceptions::Cpu("x86Cpu:setConcreteRegisterValue() - Invalid register.");
        }
      }


      bool x86Cpu::isMemoryMapped(triton::uint64 baseAddr, triton::usize size) {
        for (triton::usize index = 0; index < size; index++) {
          if (this->memory.find(baseAddr + index) == this->memory.end())
            return false;
        }
        return true;
      }


      void x86Cpu::unmapMemory(triton::uint64 baseAddr, triton::usize size) {
        for (triton::usize index = 0; index < size; index++) {
          if (this->memory.find(baseAddr + index) != this->memory.end())
            this->memory.erase(baseAddr + index);
        }
      }

    }; /* x86 namespace */
  }; /* arch namespace */
}; /* triton namespace */

