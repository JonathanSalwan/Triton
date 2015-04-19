#ifndef _PINCONVERTER_H_
#define _PINCONVERTER_H_

#include "pin.H"

#include "Registers.h"

namespace PINConverter {

/* Utilities functions which help to make the transition between the ids of registers
 * coming from the DBI framework and the Triton's ones.
 * Used by several classes and modules dedicated to Pin. */


uint64_t convertDBIReg2TritonReg(uint64_t regID);

/* Convert a Triton register to a Pin register.
 * Besides, it can return only 64 bits wised registers.
 */
uint64_t convertTritonReg2DBIReg(uint64_t regID);

}

#endif //_PINCONVERTER_H_
