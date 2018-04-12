//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_DLLEXPORT_H
#define TRITON_DLLEXPORT_H

#if defined _WIN32 || defined __CYGWIN__
  #ifdef BUILDING_DLL
    #ifdef __GNUC__
      #define TRITON_EXPORT __attribute__ ((dllexport))
    #else
      #define TRITON_EXPORT __declspec(dllexport) // Note: actually gcc seems to also supports this syntax.
    #endif
  #else
    #ifdef __GNUC__
      #define TRITON_EXPORT __attribute__ ((dllimport))
    #else
      #define TRITON_EXPORT
    #endif
  #endif
#else
  #if __GNUC__ >= 4
    #define TRITON_EXPORT __attribute__ ((visibility ("default")))
  #else
    #define TRITON_EXPORT
  #endif
#endif

#endif /* TRITON_DLLEXPORT_H */
