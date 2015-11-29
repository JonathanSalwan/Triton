/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef PINCONVERTER_H
#define PINCONVERTER_H

#include <string>
#include <utility>

#include "pin.H"

#include "Registers.h"
#include "TritonTypes.h"


namespace PINConverter {
  /* Utilities functions which help to make the transition between the ids of registers
   * coming from the DBI framework and the Triton's ones.
   * Used by several classes and modules dedicated to Pin. */

  /* Converts a Pin register to a Triton register */
  __uint convertDBIReg2TritonReg(__uint regID);

  /* Converts a Triton register to a Pin register.
   * Besides, it can return only 64 bits wised registers.
   */
  __uint convertTritonReg2DBIReg(__uint regID);

  /* Converts a Triton register to string.
   * Besides, it can return only 64 bits wised registers.
   */
  std::string getRegisterName(__uint regID);

  /* Returns the bits vector of the register */
  std::pair<__uint, __uint> convertDBIReg2BitsVector(__uint pinRegID);
}

#endif //_PINCONVERTER_H_
