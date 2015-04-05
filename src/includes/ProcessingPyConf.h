
#ifndef   __PROCESSINGPYCONF_H__
#define   __PROCESSINGPYCONF_H__

#include "AnalysisProcessor.h"
#include "IRBuilder.h"
#include "Inst.h"
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

    void applyConfBeforeProcessing(IRBuilder *irb, CONTEXT *ctx, THREADID threadId);

    void callbackAfter(Inst *inst, const ContextHandler &ctxH);
    void callbackBefore(IRBuilder *irb, const ContextHandler &ctxH);

    void startAnalysisFromAddr(IRBuilder *irb);
    void stopAnalysisFromAddr(IRBuilder *irb);

    void taintRegFromAddr(IRBuilder *irb);
    void untaintRegFromAddr(IRBuilder *irb);
};

#endif     /* !__PROCESSINGPYCONF_H__ */
