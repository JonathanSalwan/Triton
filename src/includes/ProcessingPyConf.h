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
    void callbackRoutine(reg_size threadId, PyObject *callback);
    void callbackSignals(reg_size threadId, sint32 sig);
    void callbackSyscallEntry(reg_size threadId, reg_size std);
    void callbackSyscallExit(reg_size threadId, reg_size std);
    void callbackImageLoad(string imagePath, reg_size imageBase, reg_size imageSize);

    void startAnalysisFromAddr(reg_size addr);
    void startAnalysisFromOffset(reg_size offset);
    void stopAnalysisFromAddr(reg_size addr);
    void stopAnalysisFromOffset(reg_size offset);

    void taintMemFromAddr(reg_size addr);
    void taintRegFromAddr(reg_size addr);
    void untaintMemFromAddr(reg_size addr);
    void untaintRegFromAddr(reg_size addr);
};

#endif     /* !__PROCESSINGPYCONF_H__ */
