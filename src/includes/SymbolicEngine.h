
#ifndef   __SYMBOLICENGINE_H__
#define   __SYMBOLICENGINE_H__

#include "pin.H"



/* Symbolic element */
class symbolicElement {

  private:
    std::stringstream   *source;
    std::stringstream   *destination;
    std::stringstream   *expression;
    UINT64              id;


  public:
    UINT32        isTainted;
    std::string   getExpression();
    std::string   getSource();
    UINT64        getID();

    symbolicElement(std::stringstream &dst, std::stringstream &src, UINT64 id);
    ~symbolicElement();

};

/* Symbolic Engine */
class SymbolicEngine {

  private:

    /* symbolic expression ID */
    UINT64 uniqueID;

    /* Number of symbolic variables used */
    UINT64 numberOfSymVar;

    /* 
     * Addresses <-> symbolic expression 
     * item1: memory address
     * item2: reference ID
     */
    std::list< std::pair<UINT64, UINT64> > memoryReference;

    /*
     * Addresses <-> Z3 Symbolic Variable
     * item1: memory address
     * item2: symbolic variable ID
     */
    std::list< std::pair<UINT64, UINT64> > symVarMemoryReference;

    /* List of variables decl in smt2lib */
    std::list<std::string> smt2libVarDeclList;

    /* List of symbolic elements ID */
    std::list<symbolicElement *> symbolicList;


  public:

    /* Symbolic trace */
    UINT64 symbolicReg[25];

    INT32               isMemoryReference(UINT64 addr);
    UINT64              getUniqueID();
    UINT64              getUniqueSymVarID();
    VOID                addMemoryReference(UINT64 mem, UINT64 id);
    VOID                addSmt2LibVarDecl(UINT64 symVarID, UINT64 readSize);
    VOID                addSymVarMemoryReference(UINT64 mem, UINT64 symVarID);
    VOID                setSymbolicReg(UINT64 reg, UINT64 referenceID);
    symbolicElement     *getElementFromId(UINT64 id);
    std::string         getSmt2LibVarsDecl();
    symbolicElement     *newSymbolicElement(std::stringstream &src);

    SymbolicEngine();
    ~SymbolicEngine();

};

#endif     /* !__SYMBOLICENGINE_H__ */

