
#ifndef  __SMT2LIB_UTILS__
#define  __SMT2LIB_UTILS__

#include <sstream>
#include <stdint.h>
#include <string>

std::string     smt2lib_bv(uint64_t value, uint64_t size);
std::string     smt2lib_declare(uint64_t idSymVar, uint64_t BitVecSize);
std::string     smt2lib_extract(uint64_t regSize);

#endif  /* !__SMTLIB2_UTILS__ */

