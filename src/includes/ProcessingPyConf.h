
#ifndef   __PROCESSINGPYCONF_H__
#define   __PROCESSINGPYCONF_H__

#include "AnalysisProcessor.h"
#include "IRBuilder.h"
#include "PINContextHandler.h"
#include "PythonBindings.h"
#include "Trigger.h"

class ProcessingPyConf
{
  private:
    AnalysisProcessor   *ap;
    Trigger             *analysisTrigger;

  public:
    ProcessingPyConf(AnalysisProcessor *ap, Trigger *analysisTrigger);
    ~ProcessingPyConf();

    void applyConfAfter(IRBuilder *irb, CONTEXT *ctx, THREADID threadId);
    void applyConfBefore(IRBuilder *irb, CONTEXT *ctx, THREADID threadId);
    void callbackAfter(IRBuilder *irb, THREADID threadId);
    void callbackBefore(IRBuilder *irb, THREADID threadId);
    void startAnalysisFromAddr(IRBuilder *irb);
    void stopAnalysisFromAddr(IRBuilder *irb);
    void taintRegFromAddr(IRBuilder *irb);
    void untaintRegFromAddr(IRBuilder *irb);
};

#endif     /* !__PROCESSINGPYCONF_H__ */
