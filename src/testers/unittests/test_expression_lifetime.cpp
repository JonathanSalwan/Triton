/*
** Copyright (C) - Triton
** This program is under the terms of the Apache License 2.0.
*/

#include <atomic>
#include <cstddef>
#include <cstdio>
#include <cstdlib>
#include <new>

#include <triton/context.hpp>
#include <triton/instruction.hpp>

/*
 * Counts the bytes allocated with operator new and not freed yet. Where the library does
 * not use the operator new of this executable (a Windows DLL), nothing is counted and the
 * test is skipped.
 */
namespace {
  constexpr std::size_t HEADER = alignof(std::max_align_t);
  constexpr int SKIPPED = 77;

  std::atomic<long long> liveBytes{0};
  std::atomic<unsigned long long> allocations{0};
}

void* operator new(std::size_t size) {
  auto* block = static_cast<unsigned char*>(std::malloc(size + HEADER));
  if (block == nullptr)
    throw std::bad_alloc();
  *reinterpret_cast<std::size_t*>(block) = size;
  liveBytes += static_cast<long long>(size);
  allocations++;
  return block + HEADER;
}

void operator delete(void* ptr) noexcept {
  if (ptr == nullptr)
    return;
  auto* block = static_cast<unsigned char*>(ptr) - HEADER;
  liveBytes -= static_cast<long long>(*reinterpret_cast<std::size_t*>(block));
  std::free(block);
}

void operator delete(void* ptr, std::size_t) noexcept {
  operator delete(ptr);
}


int main() {
  /* mov rax, 0; add rax, rcx: each instruction replaces the previous expressions, so nothing stays alive */
  const char* code[] = {"\x48\xc7\xc0\x00\x00\x00\x00", "\x48\x01\xc8"};
  const triton::uint32 size[] = {7, 3};
  const unsigned count = 200000;

  triton::Context ctx(triton::arch::ARCH_X86_64);
  for (unsigned index = 0; index < 1000; index++) {
    triton::arch::Instruction inst(code[index % 2], size[index % 2]);
    ctx.processing(inst);
  }

  long long before = liveBytes;
  unsigned long long counted = allocations;
  for (unsigned index = 0; index < count; index++) {
    triton::arch::Instruction inst(code[index % 2], size[index % 2]);
    ctx.processing(inst);
  }

  if (allocations - counted < count) {
    std::printf("SKIP: the library does not allocate with this executable's operator new\n");
    return SKIPPED;
  }

  /* Without sweeping the dead entries of the expression map, this grows by about 3.5 KB per instruction */
  long long grown = liveBytes - before;
  std::printf("%u instructions: %lld bytes still allocated (%lld per instruction)\n", count, grown, grown / count);
  if (grown > 64 * 1024 * 1024) {
    std::printf("FAIL: dead symbolic expressions are not released\n");
    return 1;
  }

  std::printf("PASS\n");
  return 0;
}
