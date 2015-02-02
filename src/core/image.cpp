
#include "pin.H"
#include "Triton.h"

#include "analysis/FormatString.h"


VOID Image(IMG img, VOID *v)
{
  /* This callback is used to lock and unlock the analysis */
  /* Mainly used to target an area */
  RTN unlockRTN = RTN_FindByName(img, KnobStartAnalysis.Value().c_str());
  if (RTN_Valid(unlockRTN)){
    RTN_Open(unlockRTN);
    RTN_InsertCall(unlockRTN,
                   IPOINT_BEFORE,
                   (AFUNPTR)unlockAnalysis,
                   IARG_PTR,
                   &_analysisStatus,
                   IARG_CONTEXT,
                   IARG_END);

    RTN_InsertCall(unlockRTN,
                   IPOINT_AFTER,
                   (AFUNPTR)lockAnalysis,
                   IARG_PTR,
                   &_analysisStatus,
                   IARG_CONTEXT,
                   IARG_END);

    RTN_Close(unlockRTN);
  }

  /* TODO: Must be deleted but currently used for test */
  //RTN taintParamsRTN = RTN_FindByName(img, "check"); /* TODO: generique */
  //if (RTN_Valid(taintParamsRTN)){
  //  RTN_Open(taintParamsRTN);
  //  RTN_InsertCall(taintParamsRTN,
  //                 IPOINT_BEFORE,
  //                 (AFUNPTR)taintParams,
  //                 IARG_CONTEXT,
  //                 IARG_PTR,
  //                 taintEngine,
  //                 IARG_END);
  //  RTN_Close(taintParamsRTN);
  //}

  /* Add callback if KnobDetectFormatString is enable */
  if (KnobDetectFormatString){
    RTN printfRTN = RTN_FindByName(img, "printf"); /* TODO: Maybe use a list of vulnerable functions */
    if (RTN_Valid(printfRTN)){
      RTN_Open(printfRTN);
      RTN_InsertCall(printfRTN,
                     IPOINT_BEFORE,
                     (AFUNPTR)formatStringBugAnalysis,
                     IARG_ADDRINT, RTN_Address(printfRTN),
                     IARG_REG_VALUE, REG_RDI,
                     IARG_END);
      RTN_Close(printfRTN);
    }
  }

}

