//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITONTYPES_H
#define TRITONTYPES_H

#include <cstdint>
#include <boost/multiprecision/cpp_int.hpp>
#include <boost/numeric/conversion/cast.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

    //! unisgned 8-bits
    typedef std::uint8_t uint8;

    //! unisgned 16-bits
    typedef std::uint16_t uint16;

    //! unisgned 32-bits
    typedef std::uint32_t uint32;

    //! unisgned 64-bits
    typedef std::uint64_t uint64;

    //! unsigned 128-bits
    typedef boost::multiprecision::uint128_t uint128;

    //! unsigned 256-bits
    typedef boost::multiprecision::uint256_t uint256;

    //! unsigned 512-bits
    typedef boost::multiprecision::uint512_t uint512;

    //! signed 8-bits
    typedef std::int8_t sint8;

    //! signed 16-bits
    typedef std::int16_t sint16;

    //! signed 32-bits
    typedef std::int32_t sint32;

    //! signed 64-bits
    typedef std::int64_t sint64;

    //! signed 128-bits
    typedef boost::multiprecision::int128_t sint128;

    //! signed 256-bits
    typedef boost::multiprecision::int256_t sint256;

    //! signed 512-bits
    typedef boost::multiprecision::int512_t sint512;

    //! unsigned MAX_INT 32 or 64 bits according to the CPU.
    typedef std::size_t usize;

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

