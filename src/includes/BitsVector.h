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
    __uint high;
    __uint low;

  public:
    std::pair<__uint, __uint>   getPair(void);
    __uint                      getHigh(void);
    __uint                      getLow(void);
    __uint                      getVectorSize(void);
    void                        setHigh(__uint v);
    void                        setLow(__uint v);
    void                        setPair(std::pair<__uint, __uint> p);

    BitsVector();
    BitsVector(__uint high, __uint low);
    BitsVector(const BitsVector &copy);
    ~BitsVector();
};


#endif     /* !BITSVECTOR_H */
