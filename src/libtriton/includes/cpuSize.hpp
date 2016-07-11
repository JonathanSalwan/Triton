//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_CPUSIZE_H
#define TRITON_CPUSIZE_H

/*! Returns the FLAG size in bit. */
#define FLAG_SIZE_BIT 1

/*! Returns the BYTE size in byte. */
#define BYTE_SIZE 1

/*! Returns the BYTE size in bit. */
#define BYTE_SIZE_BIT 8

/*! Returns the WORD size in byte. */
#define WORD_SIZE 2

/*! Returns the WORD size in bit. */
#define WORD_SIZE_BIT 16

/*! Returns the DWORD size in byte. */
#define DWORD_SIZE 4

/*! Returns the DWORD size in bit. */
#define DWORD_SIZE_BIT 32

/*! Returns the QWORD size in byte. */
#define QWORD_SIZE 8

/*! Returns the QWORD size in bit. */
#define QWORD_SIZE_BIT 64

/*! Returns the DQWORD size in byte. */
#define DQWORD_SIZE 16

/*! Returns the DQWORD size in bit. */
#define DQWORD_SIZE_BIT 128

/*! Returns the QQWORD size in byte. */
#define QQWORD_SIZE 32

/*! Returns the QQWORD size in bit. */
#define QQWORD_SIZE_BIT 256

/*! Returns the DQQWORD size in byte. */
#define DQQWORD_SIZE 64

/*! Returns the DQQWORD size in bit. */
#define DQQWORD_SIZE_BIT 512

/*! Returns the max bits supported */
#define MAX_BITS_SUPPORTED DQQWORD_SIZE_BIT

#endif /* TRITON_CPUSIZE_H */
