#ifndef PINCONVERTER_H
#define PINCONVERTER_H

#include "pin.H"

#include "Registers.h"
#include "TritonTypes.h"


namespace PINConverter {

/* Utilities functions which help to make the transition between the ids of registers
 * coming from the DBI framework and the Triton's ones.
 * Used by several classes and modules dedicated to Pin. */


uint64 convertDBIReg2TritonReg(uint64 regID);

/* Convert a Triton register to a Pin register.
 * Besides, it can return only 64 bits wised registers.
 */
uint64 convertTritonReg2DBIReg(uint64 regID);

}

#endif //_PINCONVERTER_H_
