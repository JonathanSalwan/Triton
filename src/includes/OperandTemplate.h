#ifndef _OPERANDTEMPLATE_H_
#define _OPERANDTEMPLATE_H_

#include <stdexcept>
#include <string>


class OperandTemplate {
  public:
    virtual ~OperandTemplate() { }

    /* Must be used when the combination of operands doesn't match the instruction.
     * Throw a runtime error. */
    static void stop(std::string);

};

#endif // _OPERANDTEMPLATE_H_
