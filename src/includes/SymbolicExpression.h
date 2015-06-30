#ifndef SYMBOLICEXPRESSION_H
#define SYMBOLICEXPRESSION_H

#include <stdint.h>

#include <sstream>
#include <string>

#include "TritonTypes.h"


/* Symbolic expression */
class SymbolicExpression {

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

    SymbolicExpression(std::stringstream &dst, std::stringstream &src, uint64 id);
    SymbolicExpression(std::stringstream &dst, std::stringstream &src, uint64 id, std::string &comment);
    ~SymbolicExpression();
};

#endif /* !_SYMBOLICEXPRESSION_H_ */
