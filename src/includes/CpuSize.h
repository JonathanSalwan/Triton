/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef   CPUSIZE_H
#define   CPUSIZE_H

#define BYTE_SIZE         1   // In byte
#define BYTE_SIZE_BIT     8   // In bits

#define WORD_SIZE         2   // In byte
#define WORD_SIZE_BIT     16  // In bits

#define DWORD_SIZE        4   // In byte
#define DWORD_SIZE_BIT    32  // In bits

#define QWORD_SIZE        8   // In byte
#define QWORD_SIZE_BIT    64  // In byte

#define DQWORD_SIZE       16   // In byte
#define DQWORD_SIZE_BIT   128  // In byte

#define REG_SIZE          QWORD_SIZE      // In byte
#define REG_SIZE_BIT      QWORD_SIZE_BIT  // In bits

#define FLAG_SIZE_BIT     1               // In bits

#define SSE_REG_SIZE      DQWORD_SIZE     // In byte
#define SSE_REG_SIZE_BIT  DQWORD_SIZE_BIT // In bits

#endif     /* !CPUSIZE_H */
