/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <PinUtils.h>


/* Returns the base address of the instruction */
__uint getBaseAddress(__uint address) {
  RTN rtn;
  SEC sec;
  IMG img;
  rtn = RTN_FindByAddress(address);
  if (RTN_Valid(rtn)) {
    sec = RTN_Sec(rtn);
    if (SEC_Valid(sec)) {
      img = SEC_Img(sec);
      if (IMG_Valid(img)) {
        return IMG_LowAddress(img);
      }
    }
  }
  return 0;
}


/* Returns the image name of the instruction */
std::string getImageName(__uint address) {
  RTN rtn;
  SEC sec;
  IMG img;
  rtn = RTN_FindByAddress(address);
  if (RTN_Valid(rtn)) {
    sec = RTN_Sec(rtn);
    if (SEC_Valid(sec)) {
      img = SEC_Img(sec);
      if (IMG_Valid(img)) {
        return IMG_Name(img);
      }
    }
  }
  return "";
}


/* Returns the offset of the instruction */
__uint getInsOffset(__uint address) {
  __uint base = getBaseAddress(address);
  if (base == 0)
    return 0;
  return address - base;
}

