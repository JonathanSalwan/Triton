#ifndef _SYMBOLICELEMENT_H_
#define _SYMBOLICELEMENT_H_

#include <stdint.h>

#include <sstream>
#include <string>


/* Symbolic element */
class SymbolicElement {

  private:
    std::stringstream   *destination;
    std::stringstream   *expression;
    std::stringstream   *source;
    uint64_t            id;


  public:
    bool                isTainted;

    std::stringstream   *getExpression();
    std::stringstream   *getSource();
    uint64_t            getID();

    SymbolicElement(std::stringstream &dst, std::stringstream &src, uint64_t id);
    ~SymbolicElement();
};

#endif /* !_SYMBOLICELEMENT_H_ */
