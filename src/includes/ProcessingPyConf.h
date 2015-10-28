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
    void applyConfAfterProcessing(Inst *inst);

    void callbackAfter(Inst *inst, AnalysisProcessor *ap);
    void callbackBefore(Inst *inst, AnalysisProcessor *ap);
    void callbackBeforeIRProc(IRBuilder *irb, AnalysisProcessor *ap);
    void callbackFini(void);
    void callbackRoutine(uint64 threadId, PyObject *callback);
    void callbackSignals(uint64 threadId, sint32 sig);
    void callbackSyscallEntry(uint64 threadId, uint64 std);
    void callbackSyscallExit(uint64 threadId, uint64 std);
    void callbackImageLoad(string imagePath, uint64 imageBase, uint64 imageSize);

    void startAnalysisFromAddr(uint64 addr);
    void startAnalysisFromOffset(uint64 offset);
    void stopAnalysisFromAddr(uint64 addr);
    void stopAnalysisFromOffset(uint64 offset);

    void taintMemFromAddr(uint64 addr);
    void taintRegFromAddr(uint64 addr);
    void untaintMemFromAddr(uint64 addr);
    void untaintRegFromAddr(uint64 addr);
};

#endif     /* !__PROCESSINGPYCONF_H__ */
