
#ifndef   __SIGNALS_H__
#define   __SIGNALS_H__

#include "pin.H"

BOOL catchSignal(THREADID tid, INT32 sig, CONTEXT *ctx, BOOL hasHandler, const EXCEPTION_INFO *pExceptInfo, VOID *v);

#endif     /* !__SIGNALS_H__ */

