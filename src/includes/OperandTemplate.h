#ifndef OPERANDTEMPLATE_H
#define OPERANDTEMPLATE_H

#include <stdexcept>
#include <string>


class OperandTemplate {
  public:
    virtual ~OperandTemplate() { }

    /* Must be used when the combination of operands doesn't match the instruction.
     * Throw a runtime error. */
    static void stop(std::string);

};

#endif // OPERANDTEMPLATE_H
