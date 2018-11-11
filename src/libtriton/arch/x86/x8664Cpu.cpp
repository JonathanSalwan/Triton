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
#include <triton/x8664Cpu.hpp>



namespace triton {
  namespace arch {
    namespace x86 {

      x8664Cpu::x8664Cpu(triton::callbacks::Callbacks* callbacks) : x86Specifications(ARCH_X86_64) {
        this->callbacks = callbacks;
        this->clear();
      }


      x8664Cpu::x8664Cpu(const x8664Cpu& other) : x86Specifications(ARCH_X86_64) {
        this->copy(other);
      }


      x8664Cpu::~x8664Cpu() {
        this->memory.clear();
      }


      void x8664Cpu::copy(const x8664Cpu& other) {
        this->callbacks = other.callbacks;
        this->memory    = other.memory;

        std::memcpy(this->rax,     other.rax,    sizeof(this->rax));
        std::memcpy(this->rbx,     other.rbx,    sizeof(this->rbx));
        std::memcpy(this->rcx,     other.rcx,    sizeof(this->rcx));
        std::memcpy(this->rdx,     other.rdx,    sizeof(this->rdx));
        std::memcpy(this->rdi,     other.rdi,    sizeof(this->rdi));
        std::memcpy(this->rsi,     other.rsi,    sizeof(this->rsi));
        std::memcpy(this->rsp,     other.rsp,    sizeof(this->rsp));
        std::memcpy(this->rbp,     other.rbp,    sizeof(this->rbp));
        std::memcpy(this->rip,     other.rip,    sizeof(this->rip));
        std::memcpy(this->eflags,  other.eflags, sizeof(this->eflags));
        std::memcpy(this->r8,      other.r8,     sizeof(this->r8));
        std::memcpy(this->r9,      other.r9,     sizeof(this->r9));
        std::memcpy(this->r10,     other.r10,    sizeof(this->r10));
        std::memcpy(this->r11,     other.r11,    sizeof(this->r11));
        std::memcpy(this->r12,     other.r12,    sizeof(this->r12));
        std::memcpy(this->r13,     other.r13,    sizeof(this->r13));
        std::memcpy(this->r14,     other.r14,    sizeof(this->r14));
        std::memcpy(this->r15,     other.r15,    sizeof(this->r15));
        std::memcpy(this->mm0,     other.mm0,    sizeof(this->mm0));
        std::memcpy(this->mm1,     other.mm1,    sizeof(this->mm1));
        std::memcpy(this->mm2,     other.mm2,    sizeof(this->mm2));
        std::memcpy(this->mm3,     other.mm3,    sizeof(this->mm3));
        std::memcpy(this->mm4,     other.mm4,    sizeof(this->mm4));
        std::memcpy(this->mm5,     other.mm5,    sizeof(this->mm5));
        std::memcpy(this->mm6,     other.mm6,    sizeof(this->mm6));
        std::memcpy(this->mm7,     other.mm7,    sizeof(this->mm7));
        std::memcpy(this->zmm0,    other.zmm0,   sizeof(this->zmm0));
        std::memcpy(this->zmm1,    other.zmm1,   sizeof(this->zmm1));
        std::memcpy(this->zmm2,    other.zmm2,   sizeof(this->zmm2));
        std::memcpy(this->zmm3,    other.zmm3,   sizeof(this->zmm3));
        std::memcpy(this->zmm4,    other.zmm4,   sizeof(this->zmm4));
        std::memcpy(this->zmm5,    other.zmm5,   sizeof(this->zmm5));
        std::memcpy(this->zmm6,    other.zmm6,   sizeof(this->zmm6));
        std::memcpy(this->zmm7,    other.zmm7,   sizeof(this->zmm7));
        std::memcpy(this->zmm8,    other.zmm8,   sizeof(this->zmm8));
        std::memcpy(this->zmm9,    other.zmm9,   sizeof(this->zmm9));
        std::memcpy(this->zmm10,   other.zmm10,  sizeof(this->zmm10));
        std::memcpy(this->zmm11,   other.zmm11,  sizeof(this->zmm11));
        std::memcpy(this->zmm12,   other.zmm12,  sizeof(this->zmm12));
        std::memcpy(this->zmm13,   other.zmm13,  sizeof(this->zmm13));
        std::memcpy(this->zmm14,   other.zmm14,  sizeof(this->zmm14));
        std::memcpy(this->zmm15,   other.zmm15,  sizeof(this->zmm15));
        std::memcpy(this->zmm16,   other.zmm16,  sizeof(this->zmm16));
        std::memcpy(this->zmm17,   other.zmm17,  sizeof(this->zmm17));
        std::memcpy(this->zmm18,   other.zmm18,  sizeof(this->zmm18));
        std::memcpy(this->zmm19,   other.zmm19,  sizeof(this->zmm19));
        std::memcpy(this->zmm20,   other.zmm20,  sizeof(this->zmm20));
        std::memcpy(this->zmm21,   other.zmm21,  sizeof(this->zmm21));
        std::memcpy(this->zmm22,   other.zmm22,  sizeof(this->zmm22));
        std::memcpy(this->zmm23,   other.zmm23,  sizeof(this->zmm23));
        std::memcpy(this->zmm24,   other.zmm24,  sizeof(this->zmm24));
        std::memcpy(this->zmm25,   other.zmm25,  sizeof(this->zmm25));
        std::memcpy(this->zmm26,   other.zmm26,  sizeof(this->zmm26));
        std::memcpy(this->zmm27,   other.zmm27,  sizeof(this->zmm27));
        std::memcpy(this->zmm28,   other.zmm28,  sizeof(this->zmm28));
        std::memcpy(this->zmm29,   other.zmm29,  sizeof(this->zmm29));
        std::memcpy(this->zmm30,   other.zmm30,  sizeof(this->zmm30));
        std::memcpy(this->zmm31,   other.zmm31,  sizeof(this->zmm31));
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


      void x8664Cpu::clear(void) {
        /* Clear memory */
        this->memory.clear();

        /* Clear registers */
        std::memset(this->rax,     0x00, sizeof(this->rax));
        std::memset(this->rbx,     0x00, sizeof(this->rbx));
        std::memset(this->rcx,     0x00, sizeof(this->rcx));
        std::memset(this->rdx,     0x00, sizeof(this->rdx));
        std::memset(this->rdi,     0x00, sizeof(this->rdi));
        std::memset(this->rsi,     0x00, sizeof(this->rsi));
        std::memset(this->rsp,     0x00, sizeof(this->rsp));
        std::memset(this->rbp,     0x00, sizeof(this->rbp));
        std::memset(this->rip,     0x00, sizeof(this->rip));
        std::memset(this->eflags,  0x00, sizeof(this->eflags));
        std::memset(this->r8,      0x00, sizeof(this->r8));
        std::memset(this->r9,      0x00, sizeof(this->r9));
        std::memset(this->r10,     0x00, sizeof(this->r10));
        std::memset(this->r11,     0x00, sizeof(this->r11));
        std::memset(this->r12,     0x00, sizeof(this->r12));
        std::memset(this->r13,     0x00, sizeof(this->r13));
        std::memset(this->r14,     0x00, sizeof(this->r14));
        std::memset(this->r15,     0x00, sizeof(this->r15));
        std::memset(this->mm0,     0x00, sizeof(this->mm0));
        std::memset(this->mm1,     0x00, sizeof(this->mm1));
        std::memset(this->mm2,     0x00, sizeof(this->mm2));
        std::memset(this->mm3,     0x00, sizeof(this->mm3));
        std::memset(this->mm4,     0x00, sizeof(this->mm4));
        std::memset(this->mm5,     0x00, sizeof(this->mm5));
        std::memset(this->mm6,     0x00, sizeof(this->mm6));
        std::memset(this->mm7,     0x00, sizeof(this->mm7));
        std::memset(this->zmm0,    0x00, sizeof(this->zmm0));
        std::memset(this->zmm1,    0x00, sizeof(this->zmm1));
        std::memset(this->zmm2,    0x00, sizeof(this->zmm2));
        std::memset(this->zmm3,    0x00, sizeof(this->zmm3));
        std::memset(this->zmm4,    0x00, sizeof(this->zmm4));
        std::memset(this->zmm5,    0x00, sizeof(this->zmm5));
        std::memset(this->zmm6,    0x00, sizeof(this->zmm6));
        std::memset(this->zmm7,    0x00, sizeof(this->zmm7));
        std::memset(this->zmm8,    0x00, sizeof(this->zmm8));
        std::memset(this->zmm9,    0x00, sizeof(this->zmm9));
        std::memset(this->zmm10,   0x00, sizeof(this->zmm10));
        std::memset(this->zmm11,   0x00, sizeof(this->zmm11));
        std::memset(this->zmm12,   0x00, sizeof(this->zmm12));
        std::memset(this->zmm13,   0x00, sizeof(this->zmm13));
        std::memset(this->zmm14,   0x00, sizeof(this->zmm14));
        std::memset(this->zmm15,   0x00, sizeof(this->zmm15));
        std::memset(this->zmm16,   0x00, sizeof(this->zmm16));
        std::memset(this->zmm17,   0x00, sizeof(this->zmm17));
        std::memset(this->zmm18,   0x00, sizeof(this->zmm18));
        std::memset(this->zmm19,   0x00, sizeof(this->zmm19));
        std::memset(this->zmm20,   0x00, sizeof(this->zmm20));
        std::memset(this->zmm21,   0x00, sizeof(this->zmm21));
        std::memset(this->zmm22,   0x00, sizeof(this->zmm22));
        std::memset(this->zmm23,   0x00, sizeof(this->zmm23));
        std::memset(this->zmm24,   0x00, sizeof(this->zmm24));
        std::memset(this->zmm25,   0x00, sizeof(this->zmm25));
        std::memset(this->zmm26,   0x00, sizeof(this->zmm26));
        std::memset(this->zmm27,   0x00, sizeof(this->zmm27));
        std::memset(this->zmm28,   0x00, sizeof(this->zmm28));
        std::memset(this->zmm29,   0x00, sizeof(this->zmm29));
        std::memset(this->zmm30,   0x00, sizeof(this->zmm30));
        std::memset(this->zmm31,   0x00, sizeof(this->zmm31));
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


      x8664Cpu& x8664Cpu::operator=(const x8664Cpu& other) {
        this->copy(other);
        return *this;
      }


      triton::arch::endianness_e x8664Cpu::getEndianness(void) const {
        return triton::arch::LE_ENDIANNESS;
      }


      bool x8664Cpu::isFlag(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_AC && regId <= triton::arch::ID_REG_X86_FZ) ? true : false);
      }


      bool x8664Cpu::isRegister(triton::arch::register_e regId) const {
        return (
          this->isGPR(regId)      ||
          this->isMMX(regId)      ||
          this->isSSE(regId)      ||
          this->isAVX256(regId)   ||
          this->isAVX512(regId)   ||
          this->isControl(regId)  ||
          this->isSegment(regId)
        );
      }


      bool x8664Cpu::isRegisterValid(triton::arch::register_e regId) const {
        return (this->isFlag(regId) || this->isRegister(regId));
      }


      bool x8664Cpu::isGPR(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_RAX && regId <= triton::arch::ID_REG_X86_EFLAGS) ? true : false);
      }


      bool x8664Cpu::isMMX(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_MM0 && regId <= triton::arch::ID_REG_X86_MM7) ? true : false);
      }


      bool x8664Cpu::isSSE(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_MXCSR && regId <= triton::arch::ID_REG_X86_XMM15) ? true : false);
      }


      bool x8664Cpu::isAVX256(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_YMM0 && regId <= triton::arch::ID_REG_X86_YMM15) ? true : false);
      }


      bool x8664Cpu::isAVX512(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_ZMM0 && regId <= triton::arch::ID_REG_X86_ZMM31) ? true : false);
      }


      bool x8664Cpu::isControl(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_CR0 && regId <= triton::arch::ID_REG_X86_CR15) ? true : false);
      }


      bool x8664Cpu::isSegment(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_CS && regId <= triton::arch::ID_REG_X86_SS) ? true : false);
      }


      triton::uint32 x8664Cpu::numberOfRegisters(void) const {
        return triton::arch::ID_REG_LAST_ITEM;
      }


      triton::uint32 x8664Cpu::gprSize(void) const {
        return QWORD_SIZE;
      }


      triton::uint32 x8664Cpu::gprBitSize(void) const {
        return QWORD_SIZE_BIT;
      }


      const std::unordered_map<triton::arch::register_e, const triton::arch::Register>& x8664Cpu::getAllRegisters(void) const {
        return this->registers_;
      }


      std::set<const triton::arch::Register*> x8664Cpu::getParentRegisters(void) const {
        std::set<const triton::arch::Register*> ret;

        for (const auto& kv: this->registers_) {
          auto regId = kv.first;
          const auto& reg = kv.second;

          /* Add GPR */
          if (reg.getSize() == this->gprSize())
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

          /* Add AVX-512 */
          else if (this->isAVX512(regId))
            ret.insert(&reg);

          /* Add Control */
          else if (this->isControl(regId))
            ret.insert(&reg);
        }

        return ret;
      }


      const triton::arch::Register& x8664Cpu::getRegister(triton::arch::register_e id) const {
        try {
          return this->registers_.at(id);
        } catch (const std::out_of_range&) {
          throw triton::exceptions::Cpu("x8664Cpu::getRegister(): Invalid register for this architecture.");
        }
      }


      const triton::arch::Register& x8664Cpu::getParentRegister(const triton::arch::Register& reg) const {
        return this->getRegister(reg.getParent());
      }


      const triton::arch::Register& x8664Cpu::getParentRegister(triton::arch::register_e id) const {
        return this->getParentRegister(this->getRegister(id));
      }


      const triton::arch::Register& x8664Cpu::getProgramCounter(void) const {
        return this->getRegister(this->pcId);
      }


      const triton::arch::Register& x8664Cpu::getStackPointer(void) const {
        return this->getRegister(this->spId);
      }


      void x8664Cpu::disassembly(triton::arch::Instruction& inst) const {
        triton::extlibs::capstone::csh       handle;
        triton::extlibs::capstone::cs_insn*  insn;
        triton::usize                        count = 0;

        /* Check if the opcode and opcode' size are defined */
        if (inst.getOpcode() == nullptr || inst.getSize() == 0)
          throw triton::exceptions::Disassembly("x8664Cpu::disassembly(): Opcode and opcodeSize must be definied.");

        /* Open capstone */
        if (triton::extlibs::capstone::cs_open(triton::extlibs::capstone::CS_ARCH_X86, triton::extlibs::capstone::CS_MODE_64, &handle) != triton::extlibs::capstone::CS_ERR_OK)
          throw triton::exceptions::Disassembly("x8664Cpu::disassembly(): Cannot open capstone.");

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
                                            this->gprSize()
                                          );

                  triton::arch::Immediate disp(op->mem.disp, immsize);
                  triton::arch::Immediate scale(op->mem.scale, immsize);

                  /* Specify that LEA contains a PC relative */
                  if (base.getId() == this->pcId)
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
                  throw triton::exceptions::Disassembly("x8664Cpu::disassembly(): Invalid operand.");
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
          /* Free capstone stuffs */
          triton::extlibs::capstone::cs_free(insn, count);
        }
        else
          throw triton::exceptions::Disassembly("x8664Cpu::disassembly(): Failed to disassemble the given code.");

        triton::extlibs::capstone::cs_close(&handle);
        return;
      }


      triton::uint8 x8664Cpu::getConcreteMemoryValue(triton::uint64 addr, bool execCallbacks) const {
        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_MEMORY_VALUE, MemoryAccess(addr, BYTE_SIZE));

        auto it = this->memory.find(addr);
        if (it == this->memory.end())
          return 0x00;

        return it->second;
      }


      triton::uint512 x8664Cpu::getConcreteMemoryValue(const triton::arch::MemoryAccess& mem, bool execCallbacks) const {
        triton::uint512 ret = 0;
        triton::uint64 addr = 0;
        triton::uint32 size = 0;

        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_MEMORY_VALUE, mem);

        addr = mem.getAddress();
        size = mem.getSize();

        if (size == 0 || size > DQQWORD_SIZE)
          throw triton::exceptions::Cpu("x8664Cpu::getConcreteMemoryValue(): Invalid size memory.");

        for (triton::sint32 i = size-1; i >= 0; i--)
          ret = ((ret << BYTE_SIZE_BIT) | this->getConcreteMemoryValue(addr+i, false));

        return ret;
      }


      std::vector<triton::uint8> x8664Cpu::getConcreteMemoryAreaValue(triton::uint64 baseAddr, triton::usize size, bool execCallbacks) const {
        std::vector<triton::uint8> area;

        for (triton::usize index = 0; index < size; index++)
          area.push_back(this->getConcreteMemoryValue(baseAddr+index));

        return area;
      }


      triton::uint512 x8664Cpu::getConcreteRegisterValue(const triton::arch::Register& reg, bool execCallbacks) const {
        triton::uint512 value = 0;

        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_REGISTER_VALUE, reg);

        switch (reg.getId()) {
          case triton::arch::ID_REG_X86_RAX: return (*((triton::uint64*)(this->rax)));
          case triton::arch::ID_REG_X86_EAX: return (*((triton::uint32*)(this->rax)));
          case triton::arch::ID_REG_X86_AX:  return (*((triton::uint16*)(this->rax)));
          case triton::arch::ID_REG_X86_AH:  return (*((triton::uint8*)(this->rax+1)));
          case triton::arch::ID_REG_X86_AL:  return (*((triton::uint8*)(this->rax)));

          case triton::arch::ID_REG_X86_RBX: return (*((triton::uint64*)(this->rbx)));
          case triton::arch::ID_REG_X86_EBX: return (*((triton::uint32*)(this->rbx)));
          case triton::arch::ID_REG_X86_BX:  return (*((triton::uint16*)(this->rbx)));
          case triton::arch::ID_REG_X86_BH:  return (*((triton::uint8*)(this->rbx+1)));
          case triton::arch::ID_REG_X86_BL:  return (*((triton::uint8*)(this->rbx)));

          case triton::arch::ID_REG_X86_RCX: return (*((triton::uint64*)(this->rcx)));
          case triton::arch::ID_REG_X86_ECX: return (*((triton::uint32*)(this->rcx)));
          case triton::arch::ID_REG_X86_CX:  return (*((triton::uint16*)(this->rcx)));
          case triton::arch::ID_REG_X86_CH:  return (*((triton::uint8*)(this->rcx+1)));
          case triton::arch::ID_REG_X86_CL:  return (*((triton::uint8*)(this->rcx)));

          case triton::arch::ID_REG_X86_RDX: return (*((triton::uint64*)(this->rdx)));
          case triton::arch::ID_REG_X86_EDX: return (*((triton::uint32*)(this->rdx)));
          case triton::arch::ID_REG_X86_DX:  return (*((triton::uint16*)(this->rdx)));
          case triton::arch::ID_REG_X86_DH:  return (*((triton::uint8*)(this->rdx+1)));
          case triton::arch::ID_REG_X86_DL:  return (*((triton::uint8*)(this->rdx)));

          case triton::arch::ID_REG_X86_RDI: return (*((triton::uint64*)(this->rdi)));
          case triton::arch::ID_REG_X86_EDI: return (*((triton::uint32*)(this->rdi)));
          case triton::arch::ID_REG_X86_DI:  return (*((triton::uint16*)(this->rdi)));
          case triton::arch::ID_REG_X86_DIL: return (*((triton::uint8*)(this->rdi)));

          case triton::arch::ID_REG_X86_RSI: return (*((triton::uint64*)(this->rsi)));
          case triton::arch::ID_REG_X86_ESI: return (*((triton::uint32*)(this->rsi)));
          case triton::arch::ID_REG_X86_SI:  return (*((triton::uint16*)(this->rsi)));
          case triton::arch::ID_REG_X86_SIL: return (*((triton::uint8*)(this->rsi)));

          case triton::arch::ID_REG_X86_RSP: return (*((triton::uint64*)(this->rsp)));
          case triton::arch::ID_REG_X86_ESP: return (*((triton::uint32*)(this->rsp)));
          case triton::arch::ID_REG_X86_SP:  return (*((triton::uint16*)(this->rsp)));
          case triton::arch::ID_REG_X86_SPL: return (*((triton::uint8*)(this->rsp)));

          case triton::arch::ID_REG_X86_RBP: return (*((triton::uint64*)(this->rbp)));
          case triton::arch::ID_REG_X86_EBP: return (*((triton::uint32*)(this->rbp)));
          case triton::arch::ID_REG_X86_BP:  return (*((triton::uint16*)(this->rbp)));
          case triton::arch::ID_REG_X86_BPL: return (*((triton::uint8*)(this->rbp)));

          case triton::arch::ID_REG_X86_RIP: return (*((triton::uint64*)(this->rip)));
          case triton::arch::ID_REG_X86_EIP: return (*((triton::uint32*)(this->rip)));
          case triton::arch::ID_REG_X86_IP:  return (*((triton::uint16*)(this->rip)));

          case triton::arch::ID_REG_X86_EFLAGS: return (*((triton::uint64*)(this->eflags)));

          case triton::arch::ID_REG_X86_R8:  return (*((triton::uint64*)(this->r8)));
          case triton::arch::ID_REG_X86_R8D: return (*((triton::uint32*)(this->r8)));
          case triton::arch::ID_REG_X86_R8W: return (*((triton::uint16*)(this->r8)));
          case triton::arch::ID_REG_X86_R8B: return (*((triton::uint8*)(this->r8)));

          case triton::arch::ID_REG_X86_R9:  return (*((triton::uint64*)(this->r9)));
          case triton::arch::ID_REG_X86_R9D: return (*((triton::uint32*)(this->r9)));
          case triton::arch::ID_REG_X86_R9W: return (*((triton::uint16*)(this->r9)));
          case triton::arch::ID_REG_X86_R9B: return (*((triton::uint8*)(this->r9)));

          case triton::arch::ID_REG_X86_R10:  return (*((triton::uint64*)(this->r10)));
          case triton::arch::ID_REG_X86_R10D: return (*((triton::uint32*)(this->r10)));
          case triton::arch::ID_REG_X86_R10W: return (*((triton::uint16*)(this->r10)));
          case triton::arch::ID_REG_X86_R10B: return (*((triton::uint8*)(this->r10)));

          case triton::arch::ID_REG_X86_R11:  return (*((triton::uint64*)(this->r11)));
          case triton::arch::ID_REG_X86_R11D: return (*((triton::uint32*)(this->r11)));
          case triton::arch::ID_REG_X86_R11W: return (*((triton::uint16*)(this->r11)));
          case triton::arch::ID_REG_X86_R11B: return (*((triton::uint8*)(this->r11)));

          case triton::arch::ID_REG_X86_R12:  return (*((triton::uint64*)(this->r12)));
          case triton::arch::ID_REG_X86_R12D: return (*((triton::uint32*)(this->r12)));
          case triton::arch::ID_REG_X86_R12W: return (*((triton::uint16*)(this->r12)));
          case triton::arch::ID_REG_X86_R12B: return (*((triton::uint8*)(this->r12)));

          case triton::arch::ID_REG_X86_R13:  return (*((triton::uint64*)(this->r13)));
          case triton::arch::ID_REG_X86_R13D: return (*((triton::uint32*)(this->r13)));
          case triton::arch::ID_REG_X86_R13W: return (*((triton::uint16*)(this->r13)));
          case triton::arch::ID_REG_X86_R13B: return (*((triton::uint8*)(this->r13)));

          case triton::arch::ID_REG_X86_R14:  return (*((triton::uint64*)(this->r14)));
          case triton::arch::ID_REG_X86_R14D: return (*((triton::uint32*)(this->r14)));
          case triton::arch::ID_REG_X86_R14W: return (*((triton::uint16*)(this->r14)));
          case triton::arch::ID_REG_X86_R14B: return (*((triton::uint8*)(this->r14)));

          case triton::arch::ID_REG_X86_R15:  return (*((triton::uint64*)(this->r15)));
          case triton::arch::ID_REG_X86_R15D: return (*((triton::uint32*)(this->r15)));
          case triton::arch::ID_REG_X86_R15W: return (*((triton::uint16*)(this->r15)));
          case triton::arch::ID_REG_X86_R15B: return (*((triton::uint8*)(this->r15)));

          case triton::arch::ID_REG_X86_MM0:  return (*((triton::uint64*)(this->mm0)));
          case triton::arch::ID_REG_X86_MM1:  return (*((triton::uint64*)(this->mm1)));
          case triton::arch::ID_REG_X86_MM2:  return (*((triton::uint64*)(this->mm2)));
          case triton::arch::ID_REG_X86_MM3:  return (*((triton::uint64*)(this->mm3)));
          case triton::arch::ID_REG_X86_MM4:  return (*((triton::uint64*)(this->mm4)));
          case triton::arch::ID_REG_X86_MM5:  return (*((triton::uint64*)(this->mm5)));
          case triton::arch::ID_REG_X86_MM6:  return (*((triton::uint64*)(this->mm6)));
          case triton::arch::ID_REG_X86_MM7:  return (*((triton::uint64*)(this->mm7)));

          case triton::arch::ID_REG_X86_XMM0:  value = triton::utils::fromBufferToUint<triton::uint128>(this->zmm0);  return value;
          case triton::arch::ID_REG_X86_XMM1:  value = triton::utils::fromBufferToUint<triton::uint128>(this->zmm1);  return value;
          case triton::arch::ID_REG_X86_XMM2:  value = triton::utils::fromBufferToUint<triton::uint128>(this->zmm2);  return value;
          case triton::arch::ID_REG_X86_XMM3:  value = triton::utils::fromBufferToUint<triton::uint128>(this->zmm3);  return value;
          case triton::arch::ID_REG_X86_XMM4:  value = triton::utils::fromBufferToUint<triton::uint128>(this->zmm4);  return value;
          case triton::arch::ID_REG_X86_XMM5:  value = triton::utils::fromBufferToUint<triton::uint128>(this->zmm5);  return value;
          case triton::arch::ID_REG_X86_XMM6:  value = triton::utils::fromBufferToUint<triton::uint128>(this->zmm6);  return value;
          case triton::arch::ID_REG_X86_XMM7:  value = triton::utils::fromBufferToUint<triton::uint128>(this->zmm7);  return value;
          case triton::arch::ID_REG_X86_XMM8:  value = triton::utils::fromBufferToUint<triton::uint128>(this->zmm8);  return value;
          case triton::arch::ID_REG_X86_XMM9:  value = triton::utils::fromBufferToUint<triton::uint128>(this->zmm9);  return value;
          case triton::arch::ID_REG_X86_XMM10: value = triton::utils::fromBufferToUint<triton::uint128>(this->zmm10); return value;
          case triton::arch::ID_REG_X86_XMM11: value = triton::utils::fromBufferToUint<triton::uint128>(this->zmm11); return value;
          case triton::arch::ID_REG_X86_XMM12: value = triton::utils::fromBufferToUint<triton::uint128>(this->zmm12); return value;
          case triton::arch::ID_REG_X86_XMM13: value = triton::utils::fromBufferToUint<triton::uint128>(this->zmm13); return value;
          case triton::arch::ID_REG_X86_XMM14: value = triton::utils::fromBufferToUint<triton::uint128>(this->zmm14); return value;
          case triton::arch::ID_REG_X86_XMM15: value = triton::utils::fromBufferToUint<triton::uint128>(this->zmm15); return value;

          case triton::arch::ID_REG_X86_YMM0:  value = triton::utils::fromBufferToUint<triton::uint256>(this->zmm0);  return value;
          case triton::arch::ID_REG_X86_YMM1:  value = triton::utils::fromBufferToUint<triton::uint256>(this->zmm1);  return value;
          case triton::arch::ID_REG_X86_YMM2:  value = triton::utils::fromBufferToUint<triton::uint256>(this->zmm2);  return value;
          case triton::arch::ID_REG_X86_YMM3:  value = triton::utils::fromBufferToUint<triton::uint256>(this->zmm3);  return value;
          case triton::arch::ID_REG_X86_YMM4:  value = triton::utils::fromBufferToUint<triton::uint256>(this->zmm4);  return value;
          case triton::arch::ID_REG_X86_YMM5:  value = triton::utils::fromBufferToUint<triton::uint256>(this->zmm5);  return value;
          case triton::arch::ID_REG_X86_YMM6:  value = triton::utils::fromBufferToUint<triton::uint256>(this->zmm6);  return value;
          case triton::arch::ID_REG_X86_YMM7:  value = triton::utils::fromBufferToUint<triton::uint256>(this->zmm7);  return value;
          case triton::arch::ID_REG_X86_YMM8:  value = triton::utils::fromBufferToUint<triton::uint256>(this->zmm8);  return value;
          case triton::arch::ID_REG_X86_YMM9:  value = triton::utils::fromBufferToUint<triton::uint256>(this->zmm9);  return value;
          case triton::arch::ID_REG_X86_YMM10: value = triton::utils::fromBufferToUint<triton::uint256>(this->zmm10); return value;
          case triton::arch::ID_REG_X86_YMM11: value = triton::utils::fromBufferToUint<triton::uint256>(this->zmm11); return value;
          case triton::arch::ID_REG_X86_YMM12: value = triton::utils::fromBufferToUint<triton::uint256>(this->zmm12); return value;
          case triton::arch::ID_REG_X86_YMM13: value = triton::utils::fromBufferToUint<triton::uint256>(this->zmm13); return value;
          case triton::arch::ID_REG_X86_YMM14: value = triton::utils::fromBufferToUint<triton::uint256>(this->zmm14); return value;
          case triton::arch::ID_REG_X86_YMM15: value = triton::utils::fromBufferToUint<triton::uint256>(this->zmm15); return value;

          case triton::arch::ID_REG_X86_ZMM0:  value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm0);  return value;
          case triton::arch::ID_REG_X86_ZMM1:  value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm1);  return value;
          case triton::arch::ID_REG_X86_ZMM2:  value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm2);  return value;
          case triton::arch::ID_REG_X86_ZMM3:  value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm3);  return value;
          case triton::arch::ID_REG_X86_ZMM4:  value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm4);  return value;
          case triton::arch::ID_REG_X86_ZMM5:  value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm5);  return value;
          case triton::arch::ID_REG_X86_ZMM6:  value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm6);  return value;
          case triton::arch::ID_REG_X86_ZMM7:  value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm7);  return value;
          case triton::arch::ID_REG_X86_ZMM8:  value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm8);  return value;
          case triton::arch::ID_REG_X86_ZMM9:  value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm9);  return value;
          case triton::arch::ID_REG_X86_ZMM10: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm10); return value;
          case triton::arch::ID_REG_X86_ZMM11: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm11); return value;
          case triton::arch::ID_REG_X86_ZMM12: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm12); return value;
          case triton::arch::ID_REG_X86_ZMM13: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm13); return value;
          case triton::arch::ID_REG_X86_ZMM14: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm14); return value;
          case triton::arch::ID_REG_X86_ZMM15: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm15); return value;
          case triton::arch::ID_REG_X86_ZMM16: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm16); return value;
          case triton::arch::ID_REG_X86_ZMM17: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm17); return value;
          case triton::arch::ID_REG_X86_ZMM18: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm18); return value;
          case triton::arch::ID_REG_X86_ZMM19: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm19); return value;
          case triton::arch::ID_REG_X86_ZMM20: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm20); return value;
          case triton::arch::ID_REG_X86_ZMM21: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm21); return value;
          case triton::arch::ID_REG_X86_ZMM22: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm22); return value;
          case triton::arch::ID_REG_X86_ZMM23: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm23); return value;
          case triton::arch::ID_REG_X86_ZMM24: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm24); return value;
          case triton::arch::ID_REG_X86_ZMM25: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm25); return value;
          case triton::arch::ID_REG_X86_ZMM26: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm26); return value;
          case triton::arch::ID_REG_X86_ZMM27: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm27); return value;
          case triton::arch::ID_REG_X86_ZMM28: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm28); return value;
          case triton::arch::ID_REG_X86_ZMM29: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm29); return value;
          case triton::arch::ID_REG_X86_ZMM30: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm30); return value;
          case triton::arch::ID_REG_X86_ZMM31: value = triton::utils::fromBufferToUint<triton::uint512>(this->zmm31); return value;

          case triton::arch::ID_REG_X86_MXCSR: return (*((triton::uint64*)(this->mxcsr)));

          case triton::arch::ID_REG_X86_CR0:  return (*((triton::uint64*)(this->cr0)));
          case triton::arch::ID_REG_X86_CR1:  return (*((triton::uint64*)(this->cr1)));
          case triton::arch::ID_REG_X86_CR2:  return (*((triton::uint64*)(this->cr2)));
          case triton::arch::ID_REG_X86_CR3:  return (*((triton::uint64*)(this->cr3)));
          case triton::arch::ID_REG_X86_CR4:  return (*((triton::uint64*)(this->cr4)));
          case triton::arch::ID_REG_X86_CR5:  return (*((triton::uint64*)(this->cr5)));
          case triton::arch::ID_REG_X86_CR6:  return (*((triton::uint64*)(this->cr6)));
          case triton::arch::ID_REG_X86_CR7:  return (*((triton::uint64*)(this->cr7)));
          case triton::arch::ID_REG_X86_CR8:  return (*((triton::uint64*)(this->cr8)));
          case triton::arch::ID_REG_X86_CR9:  return (*((triton::uint64*)(this->cr9)));
          case triton::arch::ID_REG_X86_CR10: return (*((triton::uint64*)(this->cr10)));
          case triton::arch::ID_REG_X86_CR11: return (*((triton::uint64*)(this->cr11)));
          case triton::arch::ID_REG_X86_CR12: return (*((triton::uint64*)(this->cr12)));
          case triton::arch::ID_REG_X86_CR13: return (*((triton::uint64*)(this->cr13)));
          case triton::arch::ID_REG_X86_CR14: return (*((triton::uint64*)(this->cr14)));
          case triton::arch::ID_REG_X86_CR15: return (*((triton::uint64*)(this->cr15)));

          case triton::arch::ID_REG_X86_IE:  return (((*((triton::uint64*)(this->mxcsr))) >> 0) & 1);
          case triton::arch::ID_REG_X86_DE:  return (((*((triton::uint64*)(this->mxcsr))) >> 1) & 1);
          case triton::arch::ID_REG_X86_ZE:  return (((*((triton::uint64*)(this->mxcsr))) >> 2) & 1);
          case triton::arch::ID_REG_X86_OE:  return (((*((triton::uint64*)(this->mxcsr))) >> 3) & 1);
          case triton::arch::ID_REG_X86_UE:  return (((*((triton::uint64*)(this->mxcsr))) >> 4) & 1);
          case triton::arch::ID_REG_X86_PE:  return (((*((triton::uint64*)(this->mxcsr))) >> 5) & 1);
          case triton::arch::ID_REG_X86_DAZ: return (((*((triton::uint64*)(this->mxcsr))) >> 6) & 1);
          case triton::arch::ID_REG_X86_IM:  return (((*((triton::uint64*)(this->mxcsr))) >> 7) & 1);
          case triton::arch::ID_REG_X86_DM:  return (((*((triton::uint64*)(this->mxcsr))) >> 8) & 1);
          case triton::arch::ID_REG_X86_ZM:  return (((*((triton::uint64*)(this->mxcsr))) >> 9) & 1);
          case triton::arch::ID_REG_X86_OM:  return (((*((triton::uint64*)(this->mxcsr))) >> 10) & 1);
          case triton::arch::ID_REG_X86_UM:  return (((*((triton::uint64*)(this->mxcsr))) >> 11) & 1);
          case triton::arch::ID_REG_X86_PM:  return (((*((triton::uint64*)(this->mxcsr))) >> 12) & 1);
          case triton::arch::ID_REG_X86_RL:  return (((*((triton::uint64*)(this->mxcsr))) >> 13) & 1);
          case triton::arch::ID_REG_X86_RH:  return (((*((triton::uint64*)(this->mxcsr))) >> 14) & 1);
          case triton::arch::ID_REG_X86_FZ:  return (((*((triton::uint64*)(this->mxcsr))) >> 15) & 1);

          case triton::arch::ID_REG_X86_CF:  return (((*((triton::uint64*)(this->eflags))) >> 0) & 1);
          case triton::arch::ID_REG_X86_PF:  return (((*((triton::uint64*)(this->eflags))) >> 2) & 1);
          case triton::arch::ID_REG_X86_AF:  return (((*((triton::uint64*)(this->eflags))) >> 4) & 1);
          case triton::arch::ID_REG_X86_ZF:  return (((*((triton::uint64*)(this->eflags))) >> 6) & 1);
          case triton::arch::ID_REG_X86_SF:  return (((*((triton::uint64*)(this->eflags))) >> 7) & 1);
          case triton::arch::ID_REG_X86_TF:  return (((*((triton::uint64*)(this->eflags))) >> 8) & 1);
          case triton::arch::ID_REG_X86_IF:  return (((*((triton::uint64*)(this->eflags))) >> 9) & 1);
          case triton::arch::ID_REG_X86_DF:  return (((*((triton::uint64*)(this->eflags))) >> 10) & 1);
          case triton::arch::ID_REG_X86_OF:  return (((*((triton::uint64*)(this->eflags))) >> 11) & 1);
          case triton::arch::ID_REG_X86_NT:  return (((*((triton::uint64*)(this->eflags))) >> 14) & 1);
          case triton::arch::ID_REG_X86_RF:  return (((*((triton::uint64*)(this->eflags))) >> 16) & 1);
          case triton::arch::ID_REG_X86_VM:  return (((*((triton::uint64*)(this->eflags))) >> 17) & 1);
          case triton::arch::ID_REG_X86_AC:  return (((*((triton::uint64*)(this->eflags))) >> 18) & 1);
          case triton::arch::ID_REG_X86_VIF: return (((*((triton::uint64*)(this->eflags))) >> 19) & 1);
          case triton::arch::ID_REG_X86_VIP: return (((*((triton::uint64*)(this->eflags))) >> 20) & 1);
          case triton::arch::ID_REG_X86_ID:  return (((*((triton::uint64*)(this->eflags))) >> 21) & 1);

          case triton::arch::ID_REG_X86_CS: return (*((triton::uint64*)(this->cs)));
          case triton::arch::ID_REG_X86_DS: return (*((triton::uint64*)(this->ds)));
          case triton::arch::ID_REG_X86_ES: return (*((triton::uint64*)(this->es)));
          case triton::arch::ID_REG_X86_FS: return (*((triton::uint64*)(this->fs)));
          case triton::arch::ID_REG_X86_GS: return (*((triton::uint64*)(this->gs)));
          case triton::arch::ID_REG_X86_SS: return (*((triton::uint64*)(this->ss)));

          default:
            throw triton::exceptions::Cpu("x8664Cpu::getConcreteRegisterValue(): Invalid register.");
        }

        return value;
      }


      void x8664Cpu::setConcreteMemoryValue(triton::uint64 addr, triton::uint8 value) {
        if (this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_MEMORY_VALUE, MemoryAccess(addr, BYTE_SIZE), value);
        this->memory[addr] = value;
      }


      void x8664Cpu::setConcreteMemoryValue(const triton::arch::MemoryAccess& mem, const triton::uint512& value) {
        triton::uint64 addr = mem.getAddress();
        triton::uint32 size = mem.getSize();
        triton::uint512 cv  = value;

        if (cv > mem.getMaxValue())
          throw triton::exceptions::Register("x8664Cpu::setConcreteMemoryValue(): You cannot set this concrete value (too big) to this memory access.");

        if (size == 0 || size > DQQWORD_SIZE)
          throw triton::exceptions::Cpu("x8664Cpu::setConcreteMemoryValue(): Invalid size memory.");

        if (this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_MEMORY_VALUE, mem, value);

        for (triton::uint32 i = 0; i < size; i++) {
          this->memory[addr+i] = (cv & 0xff).convert_to<triton::uint8>();
          cv >>= 8;
        }
      }


      void x8664Cpu::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const std::vector<triton::uint8>& values) {
        for (triton::usize index = 0; index < values.size(); index++) {
          this->setConcreteMemoryValue(baseAddr+index, values[index]);
        }
      }


      void x8664Cpu::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const triton::uint8* area, triton::usize size) {
        for (triton::usize index = 0; index < size; index++) {
          this->setConcreteMemoryValue(baseAddr+index, area[index]);
        }
      }


      void x8664Cpu::setConcreteRegisterValue(const triton::arch::Register& reg, const triton::uint512& value) {
        if (value > reg.getMaxValue())
          throw triton::exceptions::Register("x8664Cpu::setConcreteRegisterValue(): You cannot set this concrete value (too big) to this register.");

        if (this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_REGISTER_VALUE, reg, value);

        switch (reg.getId()) {
          case triton::arch::ID_REG_X86_RAX: (*((triton::uint64*)(this->rax)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_EAX: (*((triton::uint32*)(this->rax)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_X86_AX:  (*((triton::uint16*)(this->rax)))  = value.convert_to<triton::uint16>(); break;
          case triton::arch::ID_REG_X86_AH:  (*((triton::uint8*)(this->rax+1))) = value.convert_to<triton::uint8>(); break;
          case triton::arch::ID_REG_X86_AL:  (*((triton::uint8*)(this->rax)))   = value.convert_to<triton::uint8>(); break;

          case triton::arch::ID_REG_X86_RBX: (*((triton::uint64*)(this->rbx)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_EBX: (*((triton::uint32*)(this->rbx)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_X86_BX:  (*((triton::uint16*)(this->rbx)))  = value.convert_to<triton::uint16>(); break;
          case triton::arch::ID_REG_X86_BH:  (*((triton::uint8*)(this->rbx+1))) = value.convert_to<triton::uint8>(); break;
          case triton::arch::ID_REG_X86_BL:  (*((triton::uint8*)(this->rbx)))   = value.convert_to<triton::uint8>(); break;

          case triton::arch::ID_REG_X86_RCX: (*((triton::uint64*)(this->rcx)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_ECX: (*((triton::uint32*)(this->rcx)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_X86_CX:  (*((triton::uint16*)(this->rcx)))  = value.convert_to<triton::uint16>(); break;
          case triton::arch::ID_REG_X86_CH:  (*((triton::uint8*)(this->rcx+1))) = value.convert_to<triton::uint8>(); break;
          case triton::arch::ID_REG_X86_CL:  (*((triton::uint8*)(this->rcx)))   = value.convert_to<triton::uint8>(); break;

          case triton::arch::ID_REG_X86_RDX: (*((triton::uint64*)(this->rdx)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_EDX: (*((triton::uint32*)(this->rdx)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_X86_DX:  (*((triton::uint16*)(this->rdx)))  = value.convert_to<triton::uint16>(); break;
          case triton::arch::ID_REG_X86_DH:  (*((triton::uint8*)(this->rdx+1))) = value.convert_to<triton::uint8>(); break;
          case triton::arch::ID_REG_X86_DL:  (*((triton::uint8*)(this->rdx)))   = value.convert_to<triton::uint8>(); break;

          case triton::arch::ID_REG_X86_RDI: (*((triton::uint64*)(this->rdi)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_EDI: (*((triton::uint32*)(this->rdi)))  = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_X86_DI:  (*((triton::uint16*)(this->rdi)))  = value.convert_to<triton::uint16>(); break;
          case triton::arch::ID_REG_X86_DIL: (*((triton::uint8*)(this->rdi)))   = value.convert_to<triton::uint8>(); break;

          case triton::arch::ID_REG_X86_RSI: (*((triton::uint64*)(this->rsi))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_ESI: (*((triton::uint32*)(this->rsi))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_X86_SI:  (*((triton::uint16*)(this->rsi))) = value.convert_to<triton::uint16>(); break;
          case triton::arch::ID_REG_X86_SIL: (*((triton::uint8*)(this->rsi)))  = value.convert_to<triton::uint8>(); break;

          case triton::arch::ID_REG_X86_RSP: (*((triton::uint64*)(this->rsp))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_ESP: (*((triton::uint32*)(this->rsp))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_X86_SP:  (*((triton::uint16*)(this->rsp))) = value.convert_to<triton::uint16>(); break;
          case triton::arch::ID_REG_X86_SPL: (*((triton::uint8*)(this->rsp)))  = value.convert_to<triton::uint8>(); break;

          case triton::arch::ID_REG_X86_RBP: (*((triton::uint64*)(this->rbp))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_EBP: (*((triton::uint32*)(this->rbp))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_X86_BP:  (*((triton::uint16*)(this->rbp))) = value.convert_to<triton::uint16>(); break;
          case triton::arch::ID_REG_X86_BPL: (*((triton::uint8*)(this->rbp)))  = value.convert_to<triton::uint8>(); break;

          case triton::arch::ID_REG_X86_RIP: (*((triton::uint64*)(this->rip))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_EIP: (*((triton::uint32*)(this->rip))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_X86_IP:  (*((triton::uint16*)(this->rip))) = value.convert_to<triton::uint16>(); break;

          case triton::arch::ID_REG_X86_EFLAGS: (*((triton::uint64*)(this->eflags))) = value.convert_to<triton::uint64>(); break;

          case triton::arch::ID_REG_X86_CF: {
            triton::uint64 b = (*((triton::uint64*)(this->eflags)));
            (*((triton::uint64*)(this->eflags))) = !value.is_zero() ? b | (1 << 0) : b & ~(1 << 0);
            break;
          }
          case triton::arch::ID_REG_X86_PF: {
            triton::uint64 b = (*((triton::uint64*)(this->eflags)));
            (*((triton::uint64*)(this->eflags))) = !value.is_zero() ? b | (1 << 2) : b & ~(1 << 2);
            break;
          }
          case triton::arch::ID_REG_X86_AF: {
            triton::uint64 b = (*((triton::uint64*)(this->eflags)));
            (*((triton::uint64*)(this->eflags))) = !value.is_zero() ? b | (1 << 4) : b & ~(1 << 4);
            break;
          }
          case triton::arch::ID_REG_X86_ZF: {
            triton::uint64 b = (*((triton::uint64*)(this->eflags)));
            (*((triton::uint64*)(this->eflags))) = !value.is_zero() ? b | (1 << 6) : b & ~(1 << 6);
            break;
          }
          case triton::arch::ID_REG_X86_SF: {
            triton::uint64 b = (*((triton::uint64*)(this->eflags)));
            (*((triton::uint64*)(this->eflags))) = !value.is_zero() ? b | (1 << 7) : b & ~(1 << 7);
            break;
          }
          case triton::arch::ID_REG_X86_TF: {
            triton::uint64 b = (*((triton::uint64*)(this->eflags)));
            (*((triton::uint64*)(this->eflags))) = !value.is_zero() ? b | (1 << 8) : b & ~(1 << 8);
            break;
          }
          case triton::arch::ID_REG_X86_IF: {
            triton::uint64 b = (*((triton::uint64*)(this->eflags)));
            (*((triton::uint64*)(this->eflags))) = !value.is_zero() ? b | (1 << 9) : b & ~(1 << 9);
            break;
          }
          case triton::arch::ID_REG_X86_DF: {
            triton::uint64 b = (*((triton::uint64*)(this->eflags)));
            (*((triton::uint64*)(this->eflags))) = !value.is_zero() ? b | (1 << 10) : b & ~(1 << 10);
            break;
          }
          case triton::arch::ID_REG_X86_OF: {
            triton::uint64 b = (*((triton::uint64*)(this->eflags)));
            (*((triton::uint64*)(this->eflags))) = !value.is_zero() ? b | (1 << 11) : b & ~(1 << 11);
            break;
          }
          case triton::arch::ID_REG_X86_NT: {
            triton::uint64 b = (*((triton::uint64*)(this->eflags)));
            (*((triton::uint64*)(this->eflags))) = !value.is_zero() ? b | (1 << 14) : b & ~(1 << 14);
            break;
          }
          case triton::arch::ID_REG_X86_RF: {
            triton::uint64 b = (*((triton::uint64*)(this->eflags)));
            (*((triton::uint64*)(this->eflags))) = !value.is_zero() ? b | (1 << 16) : b & ~(1 << 16);
            break;
          }
          case triton::arch::ID_REG_X86_VM: {
            triton::uint64 b = (*((triton::uint64*)(this->eflags)));
            (*((triton::uint64*)(this->eflags))) = !value.is_zero() ? b | (1 << 17) : b & ~(1 << 17);
            break;
          }
          case triton::arch::ID_REG_X86_AC: {
            triton::uint64 b = (*((triton::uint64*)(this->eflags)));
            (*((triton::uint64*)(this->eflags))) = !value.is_zero() ? b | (1 << 18) : b & ~(1 << 18);
            break;
          }
          case triton::arch::ID_REG_X86_VIF: {
            triton::uint64 b = (*((triton::uint64*)(this->eflags)));
            (*((triton::uint64*)(this->eflags))) = !value.is_zero() ? b | (1 << 19) : b & ~(1 << 19);
            break;
          }
          case triton::arch::ID_REG_X86_VIP: {
            triton::uint64 b = (*((triton::uint64*)(this->eflags)));
            (*((triton::uint64*)(this->eflags))) = !value.is_zero() ? b | (1 << 20) : b & ~(1 << 20);
            break;
          }
          case triton::arch::ID_REG_X86_ID: {
            triton::uint64 b = (*((triton::uint64*)(this->eflags)));
            (*((triton::uint64*)(this->eflags))) = !value.is_zero() ? b | (1 << 21) : b & ~(1 << 21);
            break;
          }

          case triton::arch::ID_REG_X86_R8:  (*((triton::uint64*)(this->r8))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_R8D: (*((triton::uint32*)(this->r8))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_X86_R8W: (*((triton::uint16*)(this->r8))) = value.convert_to<triton::uint16>(); break;
          case triton::arch::ID_REG_X86_R8B: (*((triton::uint8*)(this->r8)))  = value.convert_to<triton::uint8>(); break;

          case triton::arch::ID_REG_X86_R9:  (*((triton::uint64*)(this->r9))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_R9D: (*((triton::uint32*)(this->r9))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_X86_R9W: (*((triton::uint16*)(this->r9))) = value.convert_to<triton::uint16>(); break;
          case triton::arch::ID_REG_X86_R9B: (*((triton::uint8*)(this->r9)))  = value.convert_to<triton::uint8>(); break;

          case triton::arch::ID_REG_X86_R10:  (*((triton::uint64*)(this->r10))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_R10D: (*((triton::uint32*)(this->r10))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_X86_R10W: (*((triton::uint16*)(this->r10))) = value.convert_to<triton::uint16>(); break;
          case triton::arch::ID_REG_X86_R10B: (*((triton::uint8*)(this->r10)))  = value.convert_to<triton::uint8>(); break;

          case triton::arch::ID_REG_X86_R11:  (*((triton::uint64*)(this->r11))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_R11D: (*((triton::uint32*)(this->r11))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_X86_R11W: (*((triton::uint16*)(this->r11))) = value.convert_to<triton::uint16>(); break;
          case triton::arch::ID_REG_X86_R11B: (*((triton::uint8*)(this->r11)))  = value.convert_to<triton::uint8>(); break;

          case triton::arch::ID_REG_X86_R12:  (*((triton::uint64*)(this->r12))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_R12D: (*((triton::uint32*)(this->r12))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_X86_R12W: (*((triton::uint16*)(this->r12))) = value.convert_to<triton::uint16>(); break;
          case triton::arch::ID_REG_X86_R12B: (*((triton::uint8*)(this->r12)))  = value.convert_to<triton::uint8>(); break;

          case triton::arch::ID_REG_X86_R13:  (*((triton::uint64*)(this->r13))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_R13D: (*((triton::uint32*)(this->r13))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_X86_R13W: (*((triton::uint16*)(this->r13))) = value.convert_to<triton::uint16>(); break;
          case triton::arch::ID_REG_X86_R13B: (*((triton::uint8*)(this->r13)))  = value.convert_to<triton::uint8>(); break;

          case triton::arch::ID_REG_X86_R14:  (*((triton::uint64*)(this->r14))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_R14D: (*((triton::uint32*)(this->r14))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_X86_R14W: (*((triton::uint16*)(this->r14))) = value.convert_to<triton::uint16>(); break;
          case triton::arch::ID_REG_X86_R14B: (*((triton::uint8*)(this->r14)))  = value.convert_to<triton::uint8>(); break;

          case triton::arch::ID_REG_X86_R15:  (*((triton::uint64*)(this->r15))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_R15D: (*((triton::uint32*)(this->r15))) = value.convert_to<triton::uint32>(); break;
          case triton::arch::ID_REG_X86_R15W: (*((triton::uint16*)(this->r15))) = value.convert_to<triton::uint16>(); break;
          case triton::arch::ID_REG_X86_R15B: (*((triton::uint8*)(this->r15)))  = value.convert_to<triton::uint8>(); break;

          case triton::arch::ID_REG_X86_MM0:  (*((triton::uint64*)(this->mm0))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_MM1:  (*((triton::uint64*)(this->mm1))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_MM2:  (*((triton::uint64*)(this->mm2))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_MM3:  (*((triton::uint64*)(this->mm3))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_MM4:  (*((triton::uint64*)(this->mm4))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_MM5:  (*((triton::uint64*)(this->mm5))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_MM6:  (*((triton::uint64*)(this->mm6))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_MM7:  (*((triton::uint64*)(this->mm7))) = value.convert_to<triton::uint64>(); break;

          case triton::arch::ID_REG_X86_XMM0:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->zmm0); break;
          case triton::arch::ID_REG_X86_XMM1:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->zmm1); break;
          case triton::arch::ID_REG_X86_XMM2:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->zmm2); break;
          case triton::arch::ID_REG_X86_XMM3:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->zmm3); break;
          case triton::arch::ID_REG_X86_XMM4:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->zmm4); break;
          case triton::arch::ID_REG_X86_XMM5:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->zmm5); break;
          case triton::arch::ID_REG_X86_XMM6:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->zmm6); break;
          case triton::arch::ID_REG_X86_XMM7:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->zmm7); break;
          case triton::arch::ID_REG_X86_XMM8:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->zmm8); break;
          case triton::arch::ID_REG_X86_XMM9:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->zmm9); break;
          case triton::arch::ID_REG_X86_XMM10: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->zmm10); break;
          case triton::arch::ID_REG_X86_XMM11: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->zmm11); break;
          case triton::arch::ID_REG_X86_XMM12: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->zmm12); break;
          case triton::arch::ID_REG_X86_XMM13: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->zmm13); break;
          case triton::arch::ID_REG_X86_XMM14: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->zmm14); break;
          case triton::arch::ID_REG_X86_XMM15: triton::utils::fromUintToBuffer(value.convert_to<triton::uint128>(), this->zmm15); break;

          case triton::arch::ID_REG_X86_YMM0:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->zmm0); break;
          case triton::arch::ID_REG_X86_YMM1:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->zmm1); break;
          case triton::arch::ID_REG_X86_YMM2:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->zmm2); break;
          case triton::arch::ID_REG_X86_YMM3:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->zmm3); break;
          case triton::arch::ID_REG_X86_YMM4:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->zmm4); break;
          case triton::arch::ID_REG_X86_YMM5:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->zmm5); break;
          case triton::arch::ID_REG_X86_YMM6:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->zmm6); break;
          case triton::arch::ID_REG_X86_YMM7:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->zmm7); break;
          case triton::arch::ID_REG_X86_YMM8:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->zmm8); break;
          case triton::arch::ID_REG_X86_YMM9:  triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->zmm9); break;
          case triton::arch::ID_REG_X86_YMM10: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->zmm10); break;
          case triton::arch::ID_REG_X86_YMM11: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->zmm11); break;
          case triton::arch::ID_REG_X86_YMM12: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->zmm12); break;
          case triton::arch::ID_REG_X86_YMM13: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->zmm13); break;
          case triton::arch::ID_REG_X86_YMM14: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->zmm14); break;
          case triton::arch::ID_REG_X86_YMM15: triton::utils::fromUintToBuffer(value.convert_to<triton::uint256>(), this->zmm15); break;

          case triton::arch::ID_REG_X86_ZMM0:  triton::utils::fromUintToBuffer(value, this->zmm0); break;
          case triton::arch::ID_REG_X86_ZMM1:  triton::utils::fromUintToBuffer(value, this->zmm1); break;
          case triton::arch::ID_REG_X86_ZMM2:  triton::utils::fromUintToBuffer(value, this->zmm2); break;
          case triton::arch::ID_REG_X86_ZMM3:  triton::utils::fromUintToBuffer(value, this->zmm3); break;
          case triton::arch::ID_REG_X86_ZMM4:  triton::utils::fromUintToBuffer(value, this->zmm4); break;
          case triton::arch::ID_REG_X86_ZMM5:  triton::utils::fromUintToBuffer(value, this->zmm5); break;
          case triton::arch::ID_REG_X86_ZMM6:  triton::utils::fromUintToBuffer(value, this->zmm6); break;
          case triton::arch::ID_REG_X86_ZMM7:  triton::utils::fromUintToBuffer(value, this->zmm7); break;
          case triton::arch::ID_REG_X86_ZMM8:  triton::utils::fromUintToBuffer(value, this->zmm8); break;
          case triton::arch::ID_REG_X86_ZMM9:  triton::utils::fromUintToBuffer(value, this->zmm9); break;
          case triton::arch::ID_REG_X86_ZMM10: triton::utils::fromUintToBuffer(value, this->zmm10); break;
          case triton::arch::ID_REG_X86_ZMM11: triton::utils::fromUintToBuffer(value, this->zmm11); break;
          case triton::arch::ID_REG_X86_ZMM12: triton::utils::fromUintToBuffer(value, this->zmm12); break;
          case triton::arch::ID_REG_X86_ZMM13: triton::utils::fromUintToBuffer(value, this->zmm13); break;
          case triton::arch::ID_REG_X86_ZMM14: triton::utils::fromUintToBuffer(value, this->zmm14); break;
          case triton::arch::ID_REG_X86_ZMM15: triton::utils::fromUintToBuffer(value, this->zmm15); break;
          case triton::arch::ID_REG_X86_ZMM16: triton::utils::fromUintToBuffer(value, this->zmm16); break;
          case triton::arch::ID_REG_X86_ZMM17: triton::utils::fromUintToBuffer(value, this->zmm17); break;
          case triton::arch::ID_REG_X86_ZMM18: triton::utils::fromUintToBuffer(value, this->zmm18); break;
          case triton::arch::ID_REG_X86_ZMM19: triton::utils::fromUintToBuffer(value, this->zmm19); break;
          case triton::arch::ID_REG_X86_ZMM20: triton::utils::fromUintToBuffer(value, this->zmm20); break;
          case triton::arch::ID_REG_X86_ZMM21: triton::utils::fromUintToBuffer(value, this->zmm21); break;
          case triton::arch::ID_REG_X86_ZMM22: triton::utils::fromUintToBuffer(value, this->zmm22); break;
          case triton::arch::ID_REG_X86_ZMM23: triton::utils::fromUintToBuffer(value, this->zmm23); break;
          case triton::arch::ID_REG_X86_ZMM24: triton::utils::fromUintToBuffer(value, this->zmm24); break;
          case triton::arch::ID_REG_X86_ZMM25: triton::utils::fromUintToBuffer(value, this->zmm25); break;
          case triton::arch::ID_REG_X86_ZMM26: triton::utils::fromUintToBuffer(value, this->zmm26); break;
          case triton::arch::ID_REG_X86_ZMM27: triton::utils::fromUintToBuffer(value, this->zmm27); break;
          case triton::arch::ID_REG_X86_ZMM28: triton::utils::fromUintToBuffer(value, this->zmm28); break;
          case triton::arch::ID_REG_X86_ZMM29: triton::utils::fromUintToBuffer(value, this->zmm29); break;
          case triton::arch::ID_REG_X86_ZMM30: triton::utils::fromUintToBuffer(value, this->zmm30); break;
          case triton::arch::ID_REG_X86_ZMM31: triton::utils::fromUintToBuffer(value, this->zmm31); break;

          case triton::arch::ID_REG_X86_MXCSR: (*((triton::uint64*)(this->mxcsr))) = value.convert_to<triton::uint64>(); break;

          case triton::arch::ID_REG_X86_IE: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 0) : b & ~(1 << 0);
            break;
          }
          case triton::arch::ID_REG_X86_DE: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 1) : b & ~(1 << 1);
            break;
          }
          case triton::arch::ID_REG_X86_ZE: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 2) : b & ~(1 << 2);
            break;
          }
          case triton::arch::ID_REG_X86_OE: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 3) : b & ~(1 << 3);
            break;
          }
          case triton::arch::ID_REG_X86_UE: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 4) : b & ~(1 << 4);
            break;
          }
          case triton::arch::ID_REG_X86_PE: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 5) : b & ~(1 << 5);
            break;
          }
          case triton::arch::ID_REG_X86_DAZ: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 6) : b & ~(1 << 6);
            break;
          }
          case triton::arch::ID_REG_X86_IM: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 7) : b & ~(1 << 7);
            break;
          }
          case triton::arch::ID_REG_X86_DM: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 8) : b & ~(1 << 8);
            break;
          }
          case triton::arch::ID_REG_X86_ZM: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 9) : b & ~(1 << 9);
            break;
          }
          case triton::arch::ID_REG_X86_OM: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 10) : b & ~(1 << 10);
            break;
          }
          case triton::arch::ID_REG_X86_UM: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 11) : b & ~(1 << 11);
            break;
          }
          case triton::arch::ID_REG_X86_PM: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 12) : b & ~(1 << 12);
            break;
          }
          case triton::arch::ID_REG_X86_RL: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 13) : b & ~(1 << 13);
            break;
          }
          case triton::arch::ID_REG_X86_RH: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 14) : b & ~(1 << 14);
            break;
          }
          case triton::arch::ID_REG_X86_FZ: {
            triton::uint64 b = (*((triton::uint64*)(this->mxcsr)));
            (*((triton::uint64*)(this->mxcsr))) = !value.is_zero() ? b | (1 << 15) : b & ~(1 << 15);
            break;
          }

          case triton::arch::ID_REG_X86_CR0:  (*((triton::uint64*)(this->cr0)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_CR1:  (*((triton::uint64*)(this->cr1)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_CR2:  (*((triton::uint64*)(this->cr2)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_CR3:  (*((triton::uint64*)(this->cr3)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_CR4:  (*((triton::uint64*)(this->cr4)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_CR5:  (*((triton::uint64*)(this->cr5)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_CR6:  (*((triton::uint64*)(this->cr6)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_CR7:  (*((triton::uint64*)(this->cr7)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_CR8:  (*((triton::uint64*)(this->cr8)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_CR9:  (*((triton::uint64*)(this->cr9)))  = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_CR10: (*((triton::uint64*)(this->cr10))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_CR11: (*((triton::uint64*)(this->cr11))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_CR12: (*((triton::uint64*)(this->cr12))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_CR13: (*((triton::uint64*)(this->cr13))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_CR14: (*((triton::uint64*)(this->cr14))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_CR15: (*((triton::uint64*)(this->cr15))) = value.convert_to<triton::uint64>(); break;

          case triton::arch::ID_REG_X86_CS:  (*((triton::uint64*)(this->cs))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_DS:  (*((triton::uint64*)(this->ds))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_ES:  (*((triton::uint64*)(this->es))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_FS:  (*((triton::uint64*)(this->fs))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_GS:  (*((triton::uint64*)(this->gs))) = value.convert_to<triton::uint64>(); break;
          case triton::arch::ID_REG_X86_SS:  (*((triton::uint64*)(this->ss))) = value.convert_to<triton::uint64>(); break;

          default:
            throw triton::exceptions::Cpu("x8664Cpu:setConcreteRegisterValue(): Invalid register.");
        }
      }


      bool x8664Cpu::isMemoryMapped(triton::uint64 baseAddr, triton::usize size) {
        for (triton::usize index = 0; index < size; index++) {
          if (this->memory.find(baseAddr + index) == this->memory.end())
            return false;
        }
        return true;
      }


      void x8664Cpu::unmapMemory(triton::uint64 baseAddr, triton::usize size) {
        for (triton::usize index = 0; index < size; index++) {
          if (this->memory.find(baseAddr + index) != this->memory.end())
            this->memory.erase(baseAddr + index);
        }
      }

    }; /* x86 namespace */
  }; /* arch namespace */
}; /* triton namespace */
