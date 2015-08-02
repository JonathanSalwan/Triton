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
    uint64 high;
    uint64 low;

  public:
    std::pair<uint64, uint64>   getPair(void);
    uint64                      getHigh(void);
    uint64                      getLow(void);
    uint64                      getVectorSize(void);
    void                        setHigh(uint64 v);
    void                        setLow(uint64 v);
    void                        setPair(std::pair<uint64, uint64> p);

    BitsVector();
    BitsVector(uint64 high, uint64 low);
    BitsVector(const BitsVector &copy);
    ~BitsVector();
};


#endif     /* !BITSVECTOR_H */
