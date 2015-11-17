/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef   BITSVECTOR_H
#define   BITSVECTOR_H

#include <utility>
#include "TritonTypes.h"


/*
 * This class is used to deal with registers as bits vector.
 */

class BitsVector
{
  protected:
    reg_size high;
    reg_size low;

  public:
    std::pair<reg_size, reg_size>   getPair(void);
    reg_size                      getHigh(void);
    reg_size                      getLow(void);
    reg_size                      getVectorSize(void);
    void                        setHigh(reg_size v);
    void                        setLow(reg_size v);
    void                        setPair(std::pair<reg_size, reg_size> p);

    BitsVector();
    BitsVector(reg_size high, reg_size low);
    BitsVector(const BitsVector &copy);
    ~BitsVector();
};


#endif     /* !BITSVECTOR_H */
