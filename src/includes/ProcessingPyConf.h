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

    void callbackAfter(Inst *inst, AnalysisProcessor *ap);
    void callbackBefore(Inst *inst, AnalysisProcessor *ap);
    void callbackBeforeIRProc(IRBuilder *irb, AnalysisProcessor *ap);
    void callbackFini(void);
    void callbackRoutine(uint64 threadId, PyObject *callback);
    void callbackSignals(uint64 threadId, sint32 sig);
    void callbackSyscallEntry(uint64 threadId, uint64 std);
    void callbackSyscallExit(uint64 threadId, uint64 std);

    void startAnalysisFromAddr(IRBuilder *irb);
    void startAnalysisFromOffset(IRBuilder *irb);
    void stopAnalysisFromAddr(IRBuilder *irb);
    void stopAnalysisFromOffset(IRBuilder *irb);

    void taintMemFromAddr(IRBuilder *irb);
    void taintRegFromAddr(IRBuilder *irb);
    void untaintMemFromAddr(IRBuilder *irb);
    void untaintRegFromAddr(IRBuilder *irb);
};

#endif     /* !__PROCESSINGPYCONF_H__ */
