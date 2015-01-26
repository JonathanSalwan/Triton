
#ifndef   __SOLVERENGINE_H__
#define   __SOLVERENGINE_H__

/* decl */
std::string     smt2lib_bv(UINT64 value, UINT64 size);
std::string     smt2lib_declare(UINT64 idSymVar, UINT64 BitVecSize);
std::string     smt2lib_extract(UINT64 regSize);


#endif     /* !__SOLVERENGINE_H__ */
