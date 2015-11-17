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
#include <utility>

namespace PINConverter {
  /* Utilities functions which help to make the transition between the ids of registers
   * coming from the DBI framework and the Triton's ones.
   * Used by several classes and modules dedicated to Pin. */

  /* Converts a Pin register to a Triton register */
  reg_size convertDBIReg2TritonReg(reg_size regID);

  /* Converts a Triton register to a Pin register.
   * Besides, it can return only 64 bits wised registers.
   */
  reg_size convertTritonReg2DBIReg(reg_size regID);

  /* Converts a Triton register to string.
   * Besides, it can return only 64 bits wised registers.
   */
  std::string getRegisterName(reg_size regID);

  /* Returns the bits vector of the register */
  std::pair<reg_size, reg_size> convertDBIReg2BitsVector(reg_size pinRegID);
}

#endif //_PINCONVERTER_H_
