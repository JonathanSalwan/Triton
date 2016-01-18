//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITONTYPES_H
#define TRITONTYPES_H

#include <boost/multiprecision/cpp_int.hpp>
#include <boost/numeric/conversion/cast.hpp>



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

    //! unisgned char
    typedef unsigned char uint8;

    //! unisgned short
    typedef unsigned short uint16;

    //! unisgned int
    typedef unsigned int uint32;

    //! unisgned long long
    typedef unsigned long long uint64;

    //! uint128_t
    typedef boost::multiprecision::uint128_t uint128;

    //! uint256_t
    typedef boost::multiprecision::uint256_t uint256;

    //! uint512_t
    typedef boost::multiprecision::uint512_t uint512;

    //! signed char
    typedef signed char sint8;

    //! signed short
    typedef signed short sint16;

    //! signed int
    typedef signed int sint32;

    //! signed long long
    typedef signed long long sint64;

    //! int128_t
    typedef boost::multiprecision::int128_t sint128;

    //! int256_t
    typedef boost::multiprecision::int256_t sint256;

    //! int512_t
    typedef boost::multiprecision::int512_t sint512;


    #if defined(__x86_64__) || defined(_M_X64)
    //! unsigned long long if the arch is 64-bits.
    typedef unsigned long long __uint;

    //! signed long long if the arch is 64-bits.
    typedef signed long long __sint;
    #endif

    #if defined(__i386) || defined(_M_IX86)
    //! unsigned int if the arch is 32-bits.
    typedef unsigned int __uint;

    //! signed int if the arch is 32-bits.
    typedef signed int __sint;
    #endif

/*! @} End of triton namespace */
}; /* triton namespace */

#endif /* TRITONTYPES_H */

