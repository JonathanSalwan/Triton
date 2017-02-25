//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

/* libTriton */
#include <triton/api.hpp>
#include <triton/x86Specifications.hpp>

/* pintool */
#include "utils.hpp"



namespace tracer {
  namespace pintool {

    triton::__uint getBaseAddress(triton::__uint address) {
      RTN rtn;
      SEC sec;
      IMG img;
      PIN_LockClient();
      rtn = RTN_FindByAddress(address);
      PIN_UnlockClient();
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


    std::string getImageName(triton::__uint address) {
      RTN rtn;
      SEC sec;
      IMG img;
      PIN_LockClient();
      rtn = RTN_FindByAddress(address);
      PIN_UnlockClient();
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


    triton::__uint getInsOffset(triton::__uint address) {
      triton::__uint base = tracer::pintool::getBaseAddress(address);
      if (base == 0)
        return 0;
      return address - base;
    }


    std::string getRoutineName(triton::__uint address) {
      RTN rtn;
      PIN_LockClient();
      rtn = RTN_FindByAddress(address);
      PIN_UnlockClient();
      if (RTN_Valid(rtn)) {
        return RTN_Name(rtn);
      }
      return "";
    }

  };
};

