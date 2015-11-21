/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#ifndef SMODEL_H
#define SMODEL_H

#include <string>

#include "TritonTypes.h"


class Smodel
{
  private:
    /* Variable name */
    std::string name;
    /* Variable value */
    __uint      value;

  public:
    std::string getName(void);
    __uint      getValue(void);

    Smodel(std::string name, __uint value);
    ~Smodel();
};

#endif /* !SMODEL_H */
#endif /* LIGHT_VERSION */

