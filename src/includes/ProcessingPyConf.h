/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#ifndef   PROCESSINGPYCONF_H
#define   PROCESSINGPYCONF_H

#include "AnalysisProcessor.h"
#include "IRBuilder.h"
#include "Inst.h"
#include "PINContextHandler.h"
#include "PythonBindings.h"
#include "Trigger.h"
#include "TritonPyObject.h"

class ProcessingPyConf
{
  private:
    AnalysisProcessor   *ap;
    Trigger             *analysisTrigger;

  public:
    ProcessingPyConf(AnalysisProcessor *ap, Trigger *analysisTrigger);
    ~ProcessingPyConf();

    void applyConfBeforeProcessing(IRBuilder *irb);
    void applyConfAfterProcessing(IRBuilder *irb);

    void callbackAfter(Inst *inst);
    void callbackBefore(Inst *inst);
    void callbackBeforeIRProc(IRBuilder *irb);
    void callbackFini(void);
    void callbackRoutine(__uint threadId, PyObject *callback);
    void callbackSignals(__uint threadId, sint32 sig);
    void callbackSyscallEntry(__uint threadId, __uint std);
    void callbackSyscallExit(__uint threadId, __uint std);
    void callbackImageLoad(string imagePath, __uint imageBase, __uint imageSize);

    void startAnalysisFromAddr(__uint addr);
    void startAnalysisFromOffset(__uint offset);
    void stopAnalysisFromAddr(__uint addr);
    void stopAnalysisFromOffset(__uint offset);

    void taintMemFromAddr(__uint addr);
    void taintRegFromAddr(__uint addr);
    void untaintMemFromAddr(__uint addr);
    void untaintRegFromAddr(__uint addr);
};

#endif     /* !__PROCESSINGPYCONF_H__ */
