#ifndef _SYMBOLICELEMENT_H_
#define _SYMBOLICELEMENT_H_

#include <stdint.h>

#include <sstream>
#include <string>


/* Symbolic element */
class symbolicElement {

  private:
    std::stringstream   *destination;
    std::stringstream   *expression;
    std::stringstream   *source;
    uint64_t            id;


  public:
    std::string   getExpression();
    std::string   getSource();
    uint32_t      isTainted;
    uint64_t      getID();

    symbolicElement(std::stringstream &dst, std::stringstream &src, uint64_t id);
    ~symbolicElement();
};

#endif /* !_SYMBOLICELEMENT_H_ */
