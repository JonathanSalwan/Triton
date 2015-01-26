
#ifndef   __SYMBOLICENGINE_H__
#define   __SYMBOLICENGINE_H__

#include "pin.H"

/* Symbolic element */
class symbolicElement {

  public:
    std::stringstream   *symSrc;
    std::stringstream   *symDst;
    std::stringstream   *symExpr;
    UINT32              isTainted;
    UINT64              uniqueID;

    symbolicElement(std::stringstream &dst, std::stringstream &src, UINT64 uniqueID);
    ~symbolicElement();

};


#endif     /* !__SYMBOLICENGINE_H__ */
