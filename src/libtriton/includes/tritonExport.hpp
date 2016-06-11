//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITONEXPORT_H
#define TRITONEXPORT_H

#if defined(_WIN32) || defined(WIN32) || defined(__WIN32__)
  // Defined by CMake
  #ifdef defined(triton_EXPORTS)
    #define TRITON_EXPORT __declspec(dllexport)
  #else
    #define TRITON_EXPORT __declspec(dllimport)
  #endif
#elif defined(__GNUC__)
  #define TRITON_EXPORT __attribute__((visibility("default")))
#else
  #define TRITON_EXPORT
#endif

#endif /* TRITONEXPORT_H */
