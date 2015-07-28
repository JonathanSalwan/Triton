/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef PINCONVERTER_H
#define PINCONVERTER_H

#include "pin.H"

#include "Registers.h"
#include "TritonTypes.h"

#include <string>

namespace PINConverter {
  /* Utilities functions which help to make the transition between the ids of registers
   * coming from the DBI framework and the Triton's ones.
   * Used by several classes and modules dedicated to Pin. */

  /* Converts a Pin register to a Triton register */
  uint64 convertDBIReg2TritonReg(uint64 regID);

  /* Converts a Triton register to a Pin register.
   * Besides, it can return only 64 bits wised registers.
   */
  uint64 convertTritonReg2DBIReg(uint64 regID);

  /* Converts a Triton register to string.
   * Besides, it can return only 64 bits wised registers.
   */
  std::string getRegisterName(uint64 regID);
}

#endif //_PINCONVERTER_H_
