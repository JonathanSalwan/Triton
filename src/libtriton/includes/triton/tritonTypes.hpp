//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITONTYPES_H
#define TRITONTYPES_H

#include <cstdint>

#include <triton/uintwide_t.h>


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

    //! unsigned 80-bits
    //typedef math::wide_integer::uintwide_t<static_cast<size_t>(UINT32_C(96)), std::uint32_t> uint80;
    typedef math::wide_integer::uintwide_t<static_cast<size_t>(UINT32_C(80)), std::uint16_t> uint80;

    //! unsigned 128-bits
    typedef math::wide_integer::uint128_t uint128;

    //! unsigned 256-bits
    typedef math::wide_integer::uint256_t uint256;

    //! unsigned 512-bits
    typedef math::wide_integer::uint512_t uint512;

    //! signed 8-bits
    typedef std::int8_t sint8;

    //! signed 16-bits
    typedef std::int16_t sint16;

    //! signed 32-bits
    typedef std::int32_t sint32;

    //! signed 64-bits
    typedef std::int64_t sint64;

    //! signed 128-bits
    typedef math::wide_integer::int128_t sint128;

    //! signed 256-bits
    typedef math::wide_integer::int256_t sint256;

    //! signed 512-bits
    typedef math::wide_integer::int512_t sint512;

    //! unsigned MAX_INT 32 or 64 bits according to the CPU.
    typedef std::size_t usize;

    #if defined(__x86_64__) || defined(_M_X64)  || defined(__aarch64__)
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

    /*! \class IdentityHash
    *   \brief Used as a hash function in hash tables containers (std::unordered_map, robin_map).
    */
    template<typename T>
    class IdentityHash
    {
    public:
      //! Returns the key as is.
      T operator()(const T& key) const { return key; }
    };

/*! @} End of triton namespace */
}; /* triton namespace */

#endif /* TRITONTYPES_H */
