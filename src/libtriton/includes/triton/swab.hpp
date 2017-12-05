//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_SWAB_H
#define TRITON_SWAB_H

#include <triton/tritonTypes.hpp>

#define ___constant_swab16(x) ((triton::uint16)(                                 \
                                   (((triton::uint16)(x) & (triton::uint16)0x00ffU) << 8) |          \
                                   (((triton::uint16)(x) & (triton::uint16)0xff00U) >> 8)))

#define ___constant_swab32(x) ((triton::uint32)(             \
                                   (((triton::uint32)(x) & (triton::uint32)0x000000ffUL) << 24) |        \
                                   (((triton::uint32)(x) & (triton::uint32)0x0000ff00UL) <<  8) |        \
                                   (((triton::uint32)(x) & (triton::uint32)0x00ff0000UL) >>  8) |        \
                                   (((triton::uint32)(x) & (triton::uint32)0xff000000UL) >> 24)))

#define ___constant_swab64(x) ((triton::uint64)(             \
                                   (((triton::uint64)(x) & (triton::uint64)0x00000000000000ffULL) << 56) |   \
                                   (((triton::uint64)(x) & (triton::uint64)0x000000000000ff00ULL) << 40) |   \
                                   (((triton::uint64)(x) & (triton::uint64)0x0000000000ff0000ULL) << 24) |   \
                                   (((triton::uint64)(x) & (triton::uint64)0x00000000ff000000ULL) <<  8) |   \
                                   (((triton::uint64)(x) & (triton::uint64)0x000000ff00000000ULL) >>  8) |   \
                                   (((triton::uint64)(x) & (triton::uint64)0x0000ff0000000000ULL) >> 24) |   \
                                   (((triton::uint64)(x) & (triton::uint64)0x00ff000000000000ULL) >> 40) |   \
                                   (((triton::uint64)(x) & (triton::uint64)0xff00000000000000ULL) >> 56)))

#define ___constant_swahw32(x) ((triton::uint32)(            \
                                    (((triton::uint32)(x) & (triton::uint32)0x0000ffffUL) << 16) |        \
                                    (((triton::uint32)(x) & (triton::uint32)0xffff0000UL) >> 16)))

#define ___constant_swahb32(x) ((triton::uint32)(            \
                                    (((triton::uint32)(x) & (triton::uint32)0x00ff00ffUL) << 8) |     \
                                    (((triton::uint32)(x) & (triton::uint32)0xff00ff00UL) >> 8)))

#define swab16(x) (___constant_swab16(x))

#define swab32(x) (___constant_swab32(x))

#define swab64(x) (___constant_swab64(x))

#endif /* TRITON_SWAB_H */
