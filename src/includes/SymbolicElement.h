#ifndef SYMBOLICELEMENT_H
#define SYMBOLICELEMENT_H

#include <stdint.h>

#include <sstream>
#include <string>

#include "TritonTypes.h"


/* Symbolic element */
class SymbolicElement {

  private:
    std::string         *comment;
    std::stringstream   *destination;
    std::stringstream   *expression;
    std::stringstream   *source;
    uint64              id;


  public:
    bool                isTainted;

    std::string         getID2Str(void);
    std::string         *getComment(void);
    std::stringstream   *getDestination(void);
    std::stringstream   *getExpression(void);
    std::stringstream   *getSource(void);
    uint64              getID(void);
    void                setSrcExpr(std::stringstream &src);

    SymbolicElement(std::stringstream &dst, std::stringstream &src, uint64 id);
    SymbolicElement(std::stringstream &dst, std::stringstream &src, uint64 id, std::string &comment);
    ~SymbolicElement();
};

#endif /* !_SYMBOLICELEMENT_H_ */
