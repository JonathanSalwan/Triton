#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <functional>
#include <triton/context.hpp>
#include <triton/x86Specifications.hpp>
#include <LIEF/ELF.hpp>
#include <fmt/format.h>
#include <sstream>
#include <iomanip>

#define DEBUG 0

std::string getMemoryString(const triton::Context& ctx, triton::uint64 addr) {
    std::string s;
    size_t index = 0;

    while (auto value = ctx.getConcreteMemoryValue(addr + index)) {
        char c = static_cast<char>(value);
        if (std::isprint(c)) {
            s += c;
        }
        index++;
    }

    return s;
}

std::string getFormatString(const triton::Context& ctx, triton::uint64 addr) {
    std::string s = getMemoryString(ctx, addr);
    // Implement string replacements here if needed
    return s;
}

triton::uint64 strlenHandler(triton::Context& ctx) {
    if constexpr (DEBUG) {
        std::cout << "[+] Strlen hooked" << std::endl;
    }
    auto arg1 = getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.x86_rdi).convert_to<triton::uint64>());
    return arg1.length();
}



triton::uint64 printfHandler(triton::Context& ctx) {
    if constexpr (DEBUG) {
        std::cout << "[+] printf hooked" << std::endl;
    }
    auto format_str = getFormatString(ctx, ctx.getConcreteRegisterValue(ctx.registers.x86_rdi).convert_to<triton::uint64>());
    auto arg1 = ctx.getConcreteRegisterValue(ctx.registers.x86_rsi);

    std::stringstream ss;
    size_t pos = format_str.find("%ld");
    if (pos != std::string::npos) {
        ss << format_str.substr(0, pos) << arg1 << format_str.substr(pos + 3);
    } else {
        ss << format_str;
    }

    std::string formatted_str = ss.str();
    std::cout << formatted_str << std::endl;
    return formatted_str.length();
}

triton::uint64 libcMainHandler(triton::Context& ctx) {
    if constexpr (DEBUG) {
        std::cout << "[+] __libc_start_main hooked" << std::endl;
    }

    auto main = ctx.getConcreteRegisterValue(ctx.registers.x86_rdi);

    ctx.setConcreteRegisterValue(ctx.registers.x86_rsp,
        ctx.getConcreteRegisterValue(ctx.registers.x86_rsp) - 8);

    auto ret2main = triton::arch::MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.x86_rsp).convert_to<triton::uint64>(), 8);
    ctx.setConcreteMemoryValue(ret2main, main);

    ctx.concretizeRegister(ctx.registers.x86_rdi);
    ctx.concretizeRegister(ctx.registers.x86_rsi);

    std::vector<std::string> argvs = {"sample_1", "my_first_arg"};

    triton::uint64 base = 0x20000000;
    std::vector<triton::uint64> addrs;

    for (const auto& argv : argvs) {
        addrs.push_back(base);
        ctx.setConcreteMemoryAreaValue(base, reinterpret_cast<const triton::uint8*>(argv.c_str()), argv.length() + 1);
        base += argv.length() + 1;
    }

    triton::uint64 argc = argvs.size();
    triton::uint64 argv = base;
    for (const auto& addr : addrs) {
        ctx.setConcreteMemoryValue(triton::arch::MemoryAccess(base, 8), addr);
        base += 8;
    }

    ctx.setConcreteRegisterValue(ctx.registers.x86_rdi, argc);
    ctx.setConcreteRegisterValue(ctx.registers.x86_rsi, argv);

    return 0;
}

struct CustomRelocation {
    std::string name;
    std::function<triton::uint64(triton::Context&)> handler;
    triton::uint64 address;
};

std::vector<CustomRelocation> customRelocation = {
    {"strlen", strlenHandler, 0x10000000},
    {"printf", printfHandler, 0x10000001},
    {"__libc_start_main", libcMainHandler, 0x10000002},
};

void hookingHandler(triton::Context& ctx) {
    auto pc = ctx.getConcreteRegisterValue(ctx.registers.x86_rip);
    for (const auto& rel : customRelocation) {
        if (rel.address == pc) {
            auto ret_value = rel.handler(ctx);
            ctx.setConcreteRegisterValue(ctx.registers.x86_rax, ret_value);

            auto ret_addr = ctx.getConcreteMemoryValue(triton::arch::MemoryAccess(
                ctx.getConcreteRegisterValue(ctx.registers.x86_rsp).convert_to<triton::uint64>(), 8));

            ctx.setConcreteRegisterValue(ctx.registers.x86_rip, ret_addr);
            ctx.setConcreteRegisterValue(ctx.registers.x86_rsp,
                ctx.getConcreteRegisterValue(ctx.registers.x86_rsp) + 8);
        }
    }
}

void emulate(triton::Context& ctx, triton::uint64 pc) {
    if constexpr (DEBUG) {
        std::cout << "[+] Starting emulation." << std::endl;
    }

    while (pc) {
        auto opcode = ctx.getConcreteMemoryAreaValue(pc, 16);

        triton::arch::Instruction instruction;
        instruction.setOpcode(opcode.data(), opcode.size());
        instruction.setAddress(pc);

        ctx.processing(instruction);
        if constexpr (DEBUG) {
            std::cout << instruction << std::endl;
        }

        if (instruction.getType() == triton::arch::x86::ID_INS_HLT || instruction.getType() == triton::arch::x86::ID_INS_RET) { // add ID_INS_RET too maybe? see issue https://github.com/JonathanSalwan/Triton/issues/912
            break;
        }

        hookingHandler(ctx);

        pc = ctx.getConcreteRegisterValue(ctx.registers.x86_rip).convert_to<triton::uint64>();
    }
    if constexpr (DEBUG) {
        std::cout << "[+] Emulation done." << std::endl;
    }
}

std::unique_ptr<LIEF::ELF::Binary> loadBinary(triton::Context& ctx, const std::string& path) {
    std::unique_ptr<LIEF::ELF::Binary> binary = LIEF::ELF::Parser::parse(path);
    if (!binary) {
        throw std::runtime_error("Failed to parse ELF binary");
    }

    for (const auto& segment : binary->segments()) {
        if (segment.type() != LIEF::ELF::Segment::TYPE::LOAD) {
            continue;
        }
        triton::uint64 vaddr = segment.virtual_address();
        const auto& content = segment.content(); // This is now a span<const uint8_t>
        if constexpr (DEBUG) {
            std::cout << "[+] Loading 0x" << std::hex << vaddr << " - 0x" << (vaddr + content.size()) << std::endl;
        }

        // Use data() and size() methods of span
        ctx.setConcreteMemoryAreaValue(vaddr, content.data(), content.size());
    }

    return binary;
}

void makeRelocation(triton::Context& ctx, const LIEF::ELF::Binary& binary) {
    for (const auto& pltgot_entry : binary.pltgot_relocations()) {
        const std::string& symbolName = pltgot_entry.symbol()->name();
        triton::uint64 symbolRelo = pltgot_entry.address();
        for (const auto& crel : customRelocation) {
            if (symbolName == crel.name) {
                if constexpr (DEBUG) {
                    std::cout << "[+] Hooking " << symbolName << std::endl;
                }
                ctx.setConcreteMemoryValue(triton::arch::MemoryAccess(symbolRelo, 8), crel.address);
            }
        }
    }
}

int main(int argc, char* argv[]) {
    if (argc != 2) {
        std::cerr << "Usage: " << argv[0] << " <path_to_binary>" << std::endl;
        return 1;
    }

    triton::Context ctx;
    ctx.setArchitecture(triton::arch::ARCH_X86_64);

    std::unique_ptr<LIEF::ELF::Binary> binary;
    try {
        binary = loadBinary(ctx, argv[1]);
    } catch (const std::exception& e) {
        std::cerr << "Error loading binary: " << e.what() << std::endl;
        return 1;
    }

    makeRelocation(ctx, *binary);

    ctx.setConcreteRegisterValue(ctx.registers.x86_rbp, 0x7fffffff);
    ctx.setConcreteRegisterValue(ctx.registers.x86_rsp, 0x6fffffff);

    triton::uint64 entrypoint = binary->entrypoint();
    emulate(ctx, entrypoint);

    return 0;
}