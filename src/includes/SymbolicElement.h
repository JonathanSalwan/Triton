#ifndef _SYMBOLICELEMENT_H_
#define _SYMBOLICELEMENT_H_

#include <stdint.h>

#include <sstream>
#include <string>


/* Symbolic element */
class SymbolicElement {

  private:
    std::string         *comment;
    std::stringstream   *destination;
    std::stringstream   *expression;
    std::stringstream   *source;
    uint64_t            id;


  public:
    bool                isTainted;

    std::string         getID2Str(void);
    std::string         *getComment(void);
    std::stringstream   *getDestination(void);
    std::stringstream   *getExpression(void);
    std::stringstream   *getSource(void);
    uint64_t            getID(void);
    void                setSrcExpr(std::stringstream &src);

    SymbolicElement(std::stringstream &dst, std::stringstream &src, uint64_t id);
    SymbolicElement(std::stringstream &dst, std::stringstream &src, uint64_t id, std::string &comment);
    ~SymbolicElement();
};

#endif /* !_SYMBOLICELEMENT_H_ */
