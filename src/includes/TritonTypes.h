/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#ifndef   TRITONTYPES_H
#define   TRITONTYPES_H
#include <boost/multiprecision/cpp_int.hpp>
#include <boost/numeric/conversion/cast.hpp>
#define BIT_MAX 512

typedef unsigned char                       uint8;
typedef unsigned short                      uint16;
typedef unsigned int                        uint32;
typedef unsigned long long                  uint64;
typedef boost::multiprecision::uint128_t    uint128;
typedef boost::multiprecision::uint512_t    uint512;

typedef signed char                         sint8;
typedef signed short                        sint16;
typedef signed int                          sint32;
typedef signed long long                    sint64;
typedef boost::multiprecision::int128_t     sint128;
typedef boost::multiprecision::int512_t     sint512;


#endif     /* !TRITONTYPES_H */
