/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef   SMODEL_H
#define   SMODEL_H

#include <string>

#include "TritonTypes.h"


class Smodel
{
  private:
    /* Variable name */
    std::string name;
    /* Variable value */
    uint64      value;

  public:
    std::string getName(void);
    uint64      getValue(void);

    Smodel(std::string name, uint64 value);
    ~Smodel();
};

#endif     /* !SMODEL_H */
