//
//  Jonathan Salwan - 2015-01-24
// 
//  http://shell-storm.org
//  http://twitter.com/JonathanSalwan
// 
//  This program is free software: you can redistribute it and/or modify
//  it under the terms of the GNU General Public License as published by
//  the Free Software  Foundation, either  version 3 of  the License, or
//  (at your option) any later version.
//

#include "pin.H"
#include "dse.h"



VOID Image(IMG img, VOID *v)
{
  RTN unlockRTN = RTN_FindByName(img, KnobStartAnalysis.Value().c_str());
  RTN taintParamsRTN = RTN_FindByName(img, "check"); /* TODO: generique */

  if (RTN_Valid(unlockRTN)){
    RTN_Open(unlockRTN);
    RTN_InsertCall(unlockRTN, IPOINT_BEFORE, (AFUNPTR)unlockAnalysis, IARG_END);
    RTN_InsertCall(unlockRTN, IPOINT_AFTER, (AFUNPTR)lockAnalysis, IARG_END);
    RTN_Close(unlockRTN);
  }

  if (RTN_Valid(taintParamsRTN)){
    RTN_Open(taintParamsRTN);
    RTN_InsertCall(taintParamsRTN, IPOINT_BEFORE, (AFUNPTR)taintParams, IARG_CONTEXT, IARG_END);
    RTN_Close(taintParamsRTN);
  } 
}

