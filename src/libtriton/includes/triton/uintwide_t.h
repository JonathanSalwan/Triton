///////////////////////////////////////////////////////////////////
//  Copyright Christopher Kormanyos 1999 - 2022.                 //
//  Distributed under the Boost Software License,                //
//  Version 1.0. (See accompanying file LICENSE_1_0.txt          //
//  or copy at http://www.boost.org/LICENSE_1_0.txt)             //
///////////////////////////////////////////////////////////////////

#ifndef UINTWIDE_T_2018_10_02_H // NOLINT(llvm-header-guard)
  #define UINTWIDE_T_2018_10_02_H

  #include <algorithm>
  #include <array>
  #if defined(__GNUC__) || defined(__clang__)
  #if defined(WIDE_INTEGER_HAS_LIMB_TYPE_UINT64)
  #include <cinttypes>
  #endif
  #endif
  #if !defined(WIDE_INTEGER_DISABLE_FLOAT_INTEROP)
  #include <cmath>
  #endif
  #include <cstddef>
  #include <cstdint>
  #include <cstdlib>
  #include <cstring>
  #include <initializer_list>
  #if !defined(WIDE_INTEGER_DISABLE_IOSTREAM)
  #include <iomanip>
  #include <istream>
  #endif
  #include <iterator>
  #include <limits>
  #if !defined(WIDE_INTEGER_DISABLE_IMPLEMENT_UTIL_DYNAMIC_ARRAY)
  #include <memory>
  #endif
  #if !defined(WIDE_INTEGER_DISABLE_IOSTREAM)
  #include <ostream>
  #include <sstream>
  #endif
  #include <type_traits>

  #if (defined(__clang__) && (__clang_major__ <= 9))
  #define WIDE_INTEGER_NUM_LIMITS_CLASS_TYPE struct // NOLINT(cppcoreguidelines-macro-usage)
  #else
  #define WIDE_INTEGER_NUM_LIMITS_CLASS_TYPE class  // NOLINT(cppcoreguidelines-macro-usage)
  #endif

  #if defined(_MSC_VER)
    #if (_MSC_VER >= 1900) && defined(_HAS_CXX20) && (_HAS_CXX20 != 0)
      #define WIDE_INTEGER_CONSTEXPR constexpr               // NOLINT(cppcoreguidelines-macro-usage)
      #define WIDE_INTEGER_CONSTEXPR_IS_COMPILE_TIME_CONST 1 // NOLINT(cppcoreguidelines-macro-usage)
      #define WIDE_INTEGER_NODISCARD [[nodiscard]]           // NOLINT(cppcoreguidelines-macro-usage)
    #else
      #define WIDE_INTEGER_CONSTEXPR
      #define WIDE_INTEGER_CONSTEXPR_IS_COMPILE_TIME_CONST 0 // NOLINT(cppcoreguidelines-macro-usage)
      #define WIDE_INTEGER_NODISCARD
    #endif
  #else
    #if (defined(__cplusplus) && (__cplusplus >= 201402L))
      #if defined(__AVR__) && (!defined(__GNUC__) || (defined(__GNUC__) && (__GNUC__ > 6)))
      #define WIDE_INTEGER_CONSTEXPR constexpr               // NOLINT(cppcoreguidelines-macro-usage)
      #define WIDE_INTEGER_CONSTEXPR_IS_COMPILE_TIME_CONST 1 // NOLINT(cppcoreguidelines-macro-usage)
      #define WIDE_INTEGER_NODISCARD [[nodiscard]]           // NOLINT(cppcoreguidelines-macro-usage)
      #elif (defined(__cpp_lib_constexpr_algorithms) && (__cpp_lib_constexpr_algorithms>=201806))
        #if defined(__clang__)
          #if (__clang_major__ > 9)
          #define WIDE_INTEGER_CONSTEXPR constexpr               // NOLINT(cppcoreguidelines-macro-usage)
          #define WIDE_INTEGER_CONSTEXPR_IS_COMPILE_TIME_CONST 1 // NOLINT(cppcoreguidelines-macro-usage)
          #define WIDE_INTEGER_NODISCARD [[nodiscard]]           // NOLINT(cppcoreguidelines-macro-usage)
          #else
          #define WIDE_INTEGER_CONSTEXPR
          #define WIDE_INTEGER_CONSTEXPR_IS_COMPILE_TIME_CONST 0 // NOLINT(cppcoreguidelines-macro-usage)
          #define WIDE_INTEGER_NODISCARD
          #endif
        #else
        #define WIDE_INTEGER_CONSTEXPR constexpr               // NOLINT(cppcoreguidelines-macro-usage)
        #define WIDE_INTEGER_CONSTEXPR_IS_COMPILE_TIME_CONST 1 // NOLINT(cppcoreguidelines-macro-usage)
        #define WIDE_INTEGER_NODISCARD [[nodiscard]]           // NOLINT(cppcoreguidelines-macro-usage)
        #endif
      #elif (defined(__clang__) && (__clang_major__ >= 10)) && (defined(__cplusplus) && (__cplusplus > 201703L))
        #if defined(__x86_64__)
        #define WIDE_INTEGER_CONSTEXPR constexpr               // NOLINT(cppcoreguidelines-macro-usage)
        #define WIDE_INTEGER_CONSTEXPR_IS_COMPILE_TIME_CONST 1 // NOLINT(cppcoreguidelines-macro-usage)
        #define WIDE_INTEGER_NODISCARD [[nodiscard]]           // NOLINT(cppcoreguidelines-macro-usage)
        #else
        #define WIDE_INTEGER_CONSTEXPR
        #define WIDE_INTEGER_CONSTEXPR_IS_COMPILE_TIME_CONST 0 // NOLINT(cppcoreguidelines-macro-usage)
        #define WIDE_INTEGER_NODISCARD
        #endif
      #else
      #define WIDE_INTEGER_CONSTEXPR
      #define WIDE_INTEGER_CONSTEXPR_IS_COMPILE_TIME_CONST 0 // NOLINT(cppcoreguidelines-macro-usage)
      #define WIDE_INTEGER_NODISCARD
      #endif
    #else
      #define WIDE_INTEGER_CONSTEXPR
      #define WIDE_INTEGER_CONSTEXPR_IS_COMPILE_TIME_CONST 0 // NOLINT(cppcoreguidelines-macro-usage)
      #define WIDE_INTEGER_NODISCARD
    #endif
  #endif

  #if defined(WIDE_INTEGER_NAMESPACE_BEGIN) || defined(WIDE_INTEGER_NAMESPACE_END)
    #error internal pre-processor macro already defined
  #endif

  #if defined(WIDE_INTEGER_NAMESPACE)
    #define WIDE_INTEGER_NAMESPACE_BEGIN namespace WIDE_INTEGER_NAMESPACE {   // NOLINT(cppcoreguidelines-macro-usage)
    #define WIDE_INTEGER_NAMESPACE_END } // namespace WIDE_INTEGER_NAMESPACE  // NOLINT(cppcoreguidelines-macro-usage)
  #else
    #define WIDE_INTEGER_NAMESPACE_BEGIN
    #define WIDE_INTEGER_NAMESPACE_END
  #endif

  #if !defined(WIDE_INTEGER_DISABLE_IMPLEMENT_UTIL_DYNAMIC_ARRAY)

  WIDE_INTEGER_NAMESPACE_BEGIN

  namespace util {

  template<typename ValueType,
           typename AllocatorType = std::allocator<ValueType>,
           typename SizeType      = std::size_t,
           typename DiffType      = std::ptrdiff_t>
  class dynamic_array;

  template<typename ValueType,
           typename AllocatorType,
           typename SizeType,
           typename DiffType>
  class dynamic_array
  {
  public:
    // Type definitions.
    using allocator_type         = typename std::allocator_traits<AllocatorType>::template rebind_alloc<ValueType>;
    using value_type             = typename allocator_type::value_type;
    using reference              =       value_type&;
    using const_reference        = const value_type&;
    using iterator               =       value_type*;
    using const_iterator         = const value_type*;
    using pointer                =       value_type*;
    using const_pointer          = const value_type*;
    using size_type              =       SizeType;
    using difference_type        =       DiffType;
    using reverse_iterator       =       std::reverse_iterator<iterator>;
    using const_reverse_iterator =       std::reverse_iterator<const_iterator>;

    // Constructors.
    constexpr dynamic_array() : elem_count(0U),
                                elems     (nullptr) { }

    explicit WIDE_INTEGER_CONSTEXPR dynamic_array(      size_type count,
                                                        const_reference v = value_type(),
                                                  const allocator_type& a = allocator_type())
      : elem_count(count),
        elems     (nullptr)
    {
      allocator_type my_a(a);

      if(elem_count > 0U)
      {
        elems = std::allocator_traits<allocator_type>::allocate(my_a, elem_count);
      }

      iterator it = begin();

      while(it != end())
      {
        std::allocator_traits<allocator_type>::construct(my_a, it, v);

        ++it;
      }
    }

    WIDE_INTEGER_CONSTEXPR dynamic_array(const dynamic_array& other)
      : elem_count(other.size()),
        elems     (nullptr)
    {
      allocator_type my_a;

      if(elem_count > 0U)
      {
        elems = std::allocator_traits<allocator_type>::allocate(my_a, elem_count);
      }

      std::copy(other.elems, other.elems + elem_count, elems);
    }

    template<typename input_iterator>
    WIDE_INTEGER_CONSTEXPR dynamic_array(input_iterator first,
                                         input_iterator last,
                                         const allocator_type& a = allocator_type())
      : elem_count(static_cast<size_type>(std::distance(first, last))),
        elems     (nullptr)
    {
      allocator_type my_a(a);

      if(elem_count > 0U)
      {
        elems = std::allocator_traits<allocator_type>::allocate(my_a, elem_count);
      }

      std::copy(first, last, elems);
    }

    WIDE_INTEGER_CONSTEXPR dynamic_array(std::initializer_list<value_type> lst,
                                         const allocator_type& a = allocator_type())
      : elem_count(lst.size()),
        elems     (nullptr)
    {
      allocator_type my_a(a);

      if(elem_count > 0U)
      {
        elems = std::allocator_traits<allocator_type>::allocate(my_a, elem_count);
      }

      std::copy(lst.begin(), lst.end(), elems);
    }

    // Move constructor.
    WIDE_INTEGER_CONSTEXPR dynamic_array(dynamic_array&& other) noexcept : elem_count(other.elem_count),
                                                                           elems     (other.elems)
    {
      other.elem_count = 0U;
      other.elems      = nullptr;
    }

    // Destructor.
    WIDE_INTEGER_CONSTEXPR virtual ~dynamic_array()
    {
      pointer p = elems; // NOLINT(altera-id-dependent-backward-branch)

      using local_allocator_traits_type = std::allocator_traits<allocator_type>;

      allocator_type my_a;

      while(p != elems + elem_count) // NOLINT(altera-id-dependent-backward-branch)
      {
        local_allocator_traits_type::destroy(my_a, p);

        ++p;
      }

      // Destroy the elements and deallocate the range.
      local_allocator_traits_type::deallocate(my_a, elems, elem_count);
    }

    // Assignment operator.
    WIDE_INTEGER_CONSTEXPR auto operator=(const dynamic_array& other) -> dynamic_array&
    {
      if(this != &other)
      {
        std::copy(other.elems,
                  other.elems + (std::min)(elem_count, other.elem_count),
                  elems);
      }

      return *this;
    }

    // Move assignment operator.
    WIDE_INTEGER_CONSTEXPR auto operator=(dynamic_array&& other) noexcept -> dynamic_array&
    {
      // Destroy the elements and deallocate the range.
      pointer p = elems; // NOLINT(altera-id-dependent-backward-branch)

      using local_allocator_traits_type = std::allocator_traits<allocator_type>;

      allocator_type my_a;

      while(p != elems + elem_count) // NOLINT(altera-id-dependent-backward-branch)
      {
        local_allocator_traits_type::destroy(my_a, p);

        ++p;
      }

      local_allocator_traits_type::deallocate(my_a, elems, elem_count);

      elem_count = other.elem_count;
      elems      = other.elems;

      other.elem_count = 0U;
      other.elems      = nullptr;

      return *this;
    }

    // Iterator members:
    WIDE_INTEGER_CONSTEXPR auto begin  ()       -> iterator               { return elems; }
    WIDE_INTEGER_CONSTEXPR auto end    ()       -> iterator               { return elems + elem_count; }
    WIDE_INTEGER_CONSTEXPR auto begin  () const -> const_iterator         { return elems; }
    WIDE_INTEGER_CONSTEXPR auto end    () const -> const_iterator         { return elems + elem_count; }
    WIDE_INTEGER_CONSTEXPR auto cbegin () const -> const_iterator         { return elems; }
    WIDE_INTEGER_CONSTEXPR auto cend   () const -> const_iterator         { return elems + elem_count; }
    WIDE_INTEGER_CONSTEXPR auto rbegin ()       -> reverse_iterator       { return reverse_iterator(elems + elem_count); }
    WIDE_INTEGER_CONSTEXPR auto rend   ()       -> reverse_iterator       { return reverse_iterator(elems); }
    WIDE_INTEGER_CONSTEXPR auto rbegin () const -> const_reverse_iterator { return const_reverse_iterator(elems + elem_count); }
    WIDE_INTEGER_CONSTEXPR auto rend   () const -> const_reverse_iterator { return const_reverse_iterator(elems); }
    WIDE_INTEGER_CONSTEXPR auto crbegin() const -> const_reverse_iterator { return const_reverse_iterator(elems + elem_count); }
    WIDE_INTEGER_CONSTEXPR auto crend  () const -> const_reverse_iterator { return const_reverse_iterator(elems); }

    // Raw pointer access.
    WIDE_INTEGER_CONSTEXPR auto data()       -> pointer       { return elems; }
    WIDE_INTEGER_CONSTEXPR auto data() const -> const_pointer { return elems; }

    // Size and capacity.
    constexpr auto size    () const -> size_type { return  elem_count; }
    constexpr auto max_size() const -> size_type { return  elem_count; }
    constexpr auto empty   () const -> bool      { return (elem_count == 0U); }

    // Element access members.
    WIDE_INTEGER_CONSTEXPR auto operator[](const size_type i)       -> reference       { return elems[i]; }
    WIDE_INTEGER_CONSTEXPR auto operator[](const size_type i) const -> const_reference { return elems[i]; }

    WIDE_INTEGER_CONSTEXPR auto front()       -> reference       { return elems[0U]; }
    WIDE_INTEGER_CONSTEXPR auto front() const -> const_reference { return elems[0U]; }

    WIDE_INTEGER_CONSTEXPR auto back()       -> reference       { return ((elem_count > static_cast<size_type>(0U)) ? elems[elem_count - 1U] : elems[0U]); }
    WIDE_INTEGER_CONSTEXPR auto back() const -> const_reference { return ((elem_count > static_cast<size_type>(0U)) ? elems[elem_count - 1U] : elems[0U]); }

    WIDE_INTEGER_CONSTEXPR auto at(const size_type i)       -> reference       { return ((i < elem_count) ? elems[i] : elems[0U]); }
    WIDE_INTEGER_CONSTEXPR auto at(const size_type i) const -> const_reference { return ((i < elem_count) ? elems[i] : elems[0U]); }

    // Element manipulation members.
    WIDE_INTEGER_CONSTEXPR void fill(const value_type& v)
    {
      std::fill_n(begin(), elem_count, v);
    }

    WIDE_INTEGER_CONSTEXPR void swap(dynamic_array& other)
    {
      if(this != &other)
      {
        pointer tmp_elems = elems;

        elems = other.elems;
        other.elems = tmp_elems;

        std::swap(elem_count, other.elem_count);
      }
    }

    WIDE_INTEGER_CONSTEXPR void swap(dynamic_array&& other)
    {
      pointer tmp_elems = elems;

      elems = other.elems;
      other.elems = tmp_elems;

      std::swap(elem_count, other.elem_count);
    }

  private:
    mutable size_type elem_count; // NOLINT(readability-identifier-naming)
    pointer           elems;      // NOLINT(readability-identifier-naming,altera-id-dependent-backward-branch)
  };

  template<typename ValueType, typename AllocatorType>
  WIDE_INTEGER_CONSTEXPR auto operator==(const dynamic_array<ValueType, AllocatorType>& lhs,
                                         const dynamic_array<ValueType, AllocatorType>& rhs) -> bool
  {
    bool left_and_right_are_equal = false;

    const bool sizes_are_equal = (lhs.size() == rhs.size());

    if(sizes_are_equal)
    {
      using size_type = typename dynamic_array<ValueType, AllocatorType>::size_type;

      const bool size_of_left_is_zero = (lhs.size() == static_cast<size_type>(0U));

      left_and_right_are_equal =
        (size_of_left_is_zero || std::equal(lhs.cbegin(), lhs.cend(), rhs.cbegin()));
    }
    else
    {
      ;
    }

    return left_and_right_are_equal;
  }

  template<typename ValueType, typename AllocatorType>
  WIDE_INTEGER_CONSTEXPR auto operator<(const dynamic_array<ValueType, AllocatorType>& lhs,
                                        const dynamic_array<ValueType, AllocatorType>& rhs) -> bool
  {
    using size_type = typename dynamic_array<ValueType, AllocatorType>::size_type;

    const bool size_of_left_is_zero = (lhs.size() == static_cast<size_type>(0U));

    bool b_result { };

    if(size_of_left_is_zero)
    {
      const bool size_of_right_is_zero = (rhs.size() == static_cast<size_type>(0U));

      b_result = (!size_of_right_is_zero);
    }
    else
    {
      if(size_of_left_is_zero)
      {
        const bool size_of_right_is_zero = (rhs.size() == static_cast<size_type>(0U));

        b_result = (!size_of_right_is_zero);
      }
      else
      {
        const size_type count = (std::min)(lhs.size(), rhs.size());

        b_result= std::lexicographical_compare(lhs.cbegin(),
                                               lhs.cbegin() + count,
                                               rhs.cbegin(),
                                               rhs.cbegin() + count);
      }
    }

    return b_result;
  }

  template<typename ValueType, typename AllocatorType>
  WIDE_INTEGER_CONSTEXPR auto operator!=(const dynamic_array<ValueType, AllocatorType>& lhs,
                                         const dynamic_array<ValueType, AllocatorType>& rhs) -> bool
  {
    return (!(lhs == rhs));
  }

  template<typename ValueType, typename AllocatorType>
  WIDE_INTEGER_CONSTEXPR auto operator>(const dynamic_array<ValueType, AllocatorType>& lhs,
                                        const dynamic_array<ValueType, AllocatorType>& rhs) -> bool
  {
    return (rhs < lhs);
  }

  template<typename ValueType, typename AllocatorType>
  WIDE_INTEGER_CONSTEXPR auto operator>=(const dynamic_array<ValueType, AllocatorType>& lhs,
                                         const dynamic_array<ValueType, AllocatorType>& rhs) -> bool
  {
    return (!(lhs < rhs));
  }

  template<typename ValueType, typename AllocatorType>
  WIDE_INTEGER_CONSTEXPR auto operator<=(const dynamic_array<ValueType, AllocatorType>& lhs,
                                         const dynamic_array<ValueType, AllocatorType>& rhs) -> bool
  {
    return (!(rhs < lhs));
  }

  template<typename ValueType, typename AllocatorType>
  WIDE_INTEGER_CONSTEXPR void swap(dynamic_array<ValueType, AllocatorType>& x,
                                   dynamic_array<ValueType, AllocatorType>& y)
  {
    x.swap(y);
  }

  } // namespace util

  WIDE_INTEGER_NAMESPACE_END

  WIDE_INTEGER_NAMESPACE_BEGIN

  #if(__cplusplus >= 201703L)
  namespace math::wide_integer::detail {
  #else
  namespace math { namespace wide_integer { namespace detail { // NOLINT(modernize-concat-nested-namespaces)
  #endif

  using util::dynamic_array;

  #if(__cplusplus >= 201703L)
  } // namespace math::wide_integer::detail
  #else
  } // namespace detail
  } // namespace wide_integer
  } // namespace math
  #endif

  WIDE_INTEGER_NAMESPACE_END

  #else

  #include <util/utility/util_dynamic_array.h>

  WIDE_INTEGER_NAMESPACE_BEGIN

  #if(__cplusplus >= 201703L)
  namespace math::wide_integer::detail {
  #else
  namespace math { namespace wide_integer { namespace detail { // NOLINT(modernize-concat-nested-namespaces)
  #endif

  using util::dynamic_array;

  #if(__cplusplus >= 201703L)
  } // namespace math::wide_integer::detail
  #else
  } // namespace detail
  } // namespace wide_integer
  } // namespace math
  #endif

  WIDE_INTEGER_NAMESPACE_END

  #endif

  WIDE_INTEGER_NAMESPACE_BEGIN

  #if(__cplusplus >= 201703L)
  namespace math::wide_integer {
  #else
  namespace math { namespace wide_integer { // NOLINT(modernize-concat-nested-namespaces)
  #endif

  namespace detail {

  using size_t    = std::uint32_t;
  using ptrdiff_t = std::int32_t;

  static_assert((  (std::numeric_limits<size_t>::digits        >= std::numeric_limits<std::uint16_t>::digits)
                && (std::numeric_limits<ptrdiff_t>::digits + 1 >= std::numeric_limits<std::uint16_t>::digits)),
                "Error: size type and pointer difference type must be at least 16 bits in width (or wider)");

  template<const size_t Width2> struct verify_power_of_two // NOLINT(altera-struct-pack-align)
  {
    // TBD: Which powers should be checked if size_t is not 32 bits?
    static constexpr bool conditional_value =
         (Width2 == static_cast<size_t>(1ULL <<  0U)) || (Width2 == static_cast<size_t>(1ULL <<  1U)) || (Width2 == static_cast<size_t>(1ULL <<  2U)) || (Width2 == static_cast<size_t>(1ULL <<  3U))
      || (Width2 == static_cast<size_t>(1ULL <<  4U)) || (Width2 == static_cast<size_t>(1ULL <<  5U)) || (Width2 == static_cast<size_t>(1ULL <<  6U)) || (Width2 == static_cast<size_t>(1ULL <<  7U))
      || (Width2 == static_cast<size_t>(1ULL <<  8U)) || (Width2 == static_cast<size_t>(1ULL <<  9U)) || (Width2 == static_cast<size_t>(1ULL << 10U)) || (Width2 == static_cast<size_t>(1ULL << 11U))
      || (Width2 == static_cast<size_t>(1ULL << 12U)) || (Width2 == static_cast<size_t>(1ULL << 13U)) || (Width2 == static_cast<size_t>(1ULL << 14U)) || (Width2 == static_cast<size_t>(1ULL << 15U))
      || (Width2 == static_cast<size_t>(1ULL << 16U)) || (Width2 == static_cast<size_t>(1ULL << 17U)) || (Width2 == static_cast<size_t>(1ULL << 18U)) || (Width2 == static_cast<size_t>(1ULL << 19U))
      || (Width2 == static_cast<size_t>(1ULL << 20U)) || (Width2 == static_cast<size_t>(1ULL << 21U)) || (Width2 == static_cast<size_t>(1ULL << 22U)) || (Width2 == static_cast<size_t>(1ULL << 23U))
      || (Width2 == static_cast<size_t>(1ULL << 24U)) || (Width2 == static_cast<size_t>(1ULL << 25U)) || (Width2 == static_cast<size_t>(1ULL << 26U)) || (Width2 == static_cast<size_t>(1ULL << 27U))
      || (Width2 == static_cast<size_t>(1ULL << 28U)) || (Width2 == static_cast<size_t>(1ULL << 29U)) || (Width2 == static_cast<size_t>(1ULL << 30U)) || (Width2 == static_cast<size_t>(1ULL << 31U))
      ;
  };

  template<const size_t BitCount,
           typename EnableType = void>
  struct uint_type_helper
  {
    #if defined(WIDE_INTEGER_HAS_LIMB_TYPE_UINT64)
    static_assert((   ((BitCount >= 8U) && (BitCount <= 128U)) // NOLINT(cppcoreguidelines-avoid-magic-numbers,readability-magic-numbers)
                   && (verify_power_of_two<BitCount>::conditional_value)),
                  "Error: uint_type_helper is not intended to be used for this BitCount");
    #else
    static_assert((   ((BitCount >= 8U) && (BitCount <= 64U)) // NOLINT(cppcoreguidelines-avoid-magic-numbers,readability-magic-numbers)
                   && (verify_power_of_two<BitCount>::conditional_value)),
                  "Error: uint_type_helper is not intended to be used for this BitCount");
    #endif

    using exact_unsigned_type = std::uintmax_t;
  };

  template<const size_t BitCount> struct uint_type_helper<BitCount, typename std::enable_if<                     (BitCount <=   8U)>::type> { using exact_unsigned_type = std::uint8_t;      using fast_unsigned_type = std::uint_fast8_t;  using fast_signed_type = std::int_fast8_t;  }; // NOLINT(cppcoreguidelines-avoid-magic-numbers,readability-magic-numbers)
  template<const size_t BitCount> struct uint_type_helper<BitCount, typename std::enable_if<(BitCount >=  9U) && (BitCount <=  16U)>::type> { using exact_unsigned_type = std::uint16_t;     using fast_unsigned_type = std::uint_fast16_t; using fast_signed_type = std::int_fast16_t; }; // NOLINT(cppcoreguidelines-avoid-magic-numbers,readability-magic-numbers)
  template<const size_t BitCount> struct uint_type_helper<BitCount, typename std::enable_if<(BitCount >= 17U) && (BitCount <=  32U)>::type> { using exact_unsigned_type = std::uint32_t;     using fast_unsigned_type = std::uint_fast32_t; using fast_signed_type = std::int_fast32_t; }; // NOLINT(cppcoreguidelines-avoid-magic-numbers,readability-magic-numbers)
  template<const size_t BitCount> struct uint_type_helper<BitCount, typename std::enable_if<(BitCount >= 33U) && (BitCount <=  64U)>::type> { using exact_unsigned_type = std::uint64_t;     using fast_unsigned_type = std::uint_fast64_t; using fast_signed_type = std::int_fast64_t; }; // NOLINT(cppcoreguidelines-avoid-magic-numbers,readability-magic-numbers)
  #if defined(WIDE_INTEGER_HAS_LIMB_TYPE_UINT64)
  template<const size_t BitCount> struct uint_type_helper<BitCount, typename std::enable_if<(BitCount >= 65U) && (BitCount <= 128U)>::type> { using exact_unsigned_type = unsigned __int128; using fast_unsigned_type = unsigned __int128;  using fast_signed_type = signed __int128;   }; // NOLINT(cppcoreguidelines-avoid-magic-numbers,readability-magic-numbers)
  #endif

  using unsigned_fast_type = typename uint_type_helper<static_cast<size_t>(std::numeric_limits<size_t   >::digits + 0)>::fast_unsigned_type;
  using   signed_fast_type = typename uint_type_helper<static_cast<size_t>(std::numeric_limits<ptrdiff_t>::digits + 1)>::fast_signed_type;

  #if !defined(WIDE_INTEGER_DISABLE_FLOAT_INTEROP)
  namespace my_own {

  template<typename FloatingPointType> WIDE_INTEGER_CONSTEXPR auto frexp   (FloatingPointType x, int* expptr) -> typename std::enable_if<((std::is_floating_point<FloatingPointType>::value) && ( std::numeric_limits<FloatingPointType>::is_iec559)), FloatingPointType>::type;
  template<typename FloatingPointType> WIDE_INTEGER_CONSTEXPR auto frexp   (FloatingPointType x, int* expptr) -> typename std::enable_if<((std::is_floating_point<FloatingPointType>::value) && (!std::numeric_limits<FloatingPointType>::is_iec559)), FloatingPointType>::type;
  template<typename FloatingPointType> WIDE_INTEGER_CONSTEXPR auto isfinite(FloatingPointType x)              -> typename std::enable_if<((std::is_floating_point<FloatingPointType>::value) && ( std::numeric_limits<FloatingPointType>::is_iec559)), bool>::type;
  template<typename FloatingPointType> WIDE_INTEGER_CONSTEXPR auto isfinite(FloatingPointType x)              -> typename std::enable_if<((std::is_floating_point<FloatingPointType>::value) && (!std::numeric_limits<FloatingPointType>::is_iec559)), bool>::type;

  } // namespace my_own
  #endif

  } // namespace detail

  using detail::size_t;
  using detail::ptrdiff_t;
  using detail::unsigned_fast_type;
  using detail::signed_fast_type;

  // Forward declaration of the uintwide_t template class.
  template<const size_t Width2,
           typename LimbType = std::uint32_t,
           typename AllocatorType = void,
           const bool IsSigned = false>
  class uintwide_t;

  // Forward declarations of non-member binary add, sub, mul, div, mod of (uintwide_t op uintwide_t).
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator+(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator-(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator*(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator/(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator%(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;

  // Forward declarations of non-member binary logic operations of (uintwide_t op uintwide_t).
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator| (const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator^ (const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator& (const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;

  // Forward declarations of non-member binary add, sub, mul, div, mod of (uintwide_t op IntegralType).
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator+(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator-(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator*(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator/(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;

  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned>
  constexpr auto operator%(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<(   ( std::is_integral<IntegralType>::value)
                                                                                                                                              && (!std::is_unsigned<IntegralType>::value)),
                                                                                                                                              uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;

  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned>
  WIDE_INTEGER_CONSTEXPR auto operator%(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<(   (std::is_integral   <IntegralType>::value)
                                                                                                                                                           && (std::is_unsigned   <IntegralType>::value)
                                                                                                                                                           && (std::numeric_limits<IntegralType>::digits <= std::numeric_limits<LimbType>::digits)),
                                                                                                                                                           typename uintwide_t<Width2, LimbType, AllocatorType, IsSigned>::limb_type>::type;

  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned>
  constexpr auto operator%(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<(   (std::is_integral   <IntegralType>::value)
                                                                                                                                              && (std::is_unsigned   <IntegralType>::value)
                                                                                                                                              && (std::numeric_limits<IntegralType>::digits > std::numeric_limits<LimbType>::digits)),
                                                                                                                                              uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;

  // Forward declarations of non-member binary add, sub, mul, div, mod of (IntegralType op uintwide_t).
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator+(const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator-(const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator*(const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator/(const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator%(const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;

  #if !defined(WIDE_INTEGER_DISABLE_FLOAT_INTEROP)
  // Forward declarations of non-member binary add, sub, mul, div, mod of (uintwide_t op FloatingPointType).
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator+(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const FloatingPointType& f) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator-(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const FloatingPointType& f) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator*(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const FloatingPointType& f) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator/(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const FloatingPointType& f) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator%(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const FloatingPointType& f) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;

  // Forward declarations of non-member binary add, sub, mul, div, mod of (FloatingPointType op uintwide_t).
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator+(const FloatingPointType& f, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator-(const FloatingPointType& f, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator*(const FloatingPointType& f, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator/(const FloatingPointType& f, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator%(const FloatingPointType& f, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;
  #endif

  // Forward declarations of non-member binary logic operations of (uintwide_t op IntegralType).
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator|(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator^(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator&(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;

  // Forward declarations of non-member binary binary logic operations of (IntegralType op uintwide_t).
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator|(const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator^(const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator&(const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type;

  // Forward declarations of non-member shift functions of (uintwide_t shift IntegralType).
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator<<(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType n) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type; // NOLINT(readability-avoid-const-params-in-decls)
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator>>(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType n) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type; // NOLINT(readability-avoid-const-params-in-decls)

  // Forward declarations of non-member comparison functions of (uintwide_t cmp uintwide_t).
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator==(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> bool;
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator!=(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> bool;
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator> (const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> bool;
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator< (const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> bool;
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator>=(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> bool;
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator<=(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> bool;

  // Forward declarations of non-member comparison functions of (uintwide_t cmp IntegralType).
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator==(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, bool>::type;
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator!=(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, bool>::type;
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator> (const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, bool>::type;
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator< (const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, bool>::type;
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator>=(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, bool>::type;
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator<=(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, bool>::type;

  // Forward declarations of non-member comparison functions of (IntegralType cmp uintwide_t).
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator==(const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, bool>::type;
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator!=(const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, bool>::type;
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator> (const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, bool>::type;
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator< (const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, bool>::type;
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator>=(const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, bool>::type;
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator<=(const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, bool>::type;

  #if !defined(WIDE_INTEGER_DISABLE_FLOAT_INTEROP)
  // Non-member comparison functions of (uintwide_t cmp FloatingPointType).
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator==(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const FloatingPointType& f) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, bool>::type;
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator!=(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const FloatingPointType& f) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, bool>::type;
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator> (const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const FloatingPointType& f) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, bool>::type;
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator< (const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const FloatingPointType& f) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, bool>::type;
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator>=(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const FloatingPointType& f) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, bool>::type;
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator<=(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const FloatingPointType& f) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, bool>::type;

  // Non-member comparison functions of (FloatingPointType cmp uintwide_t).
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator==(const FloatingPointType& f, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, bool>::type;
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator!=(const FloatingPointType& f, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, bool>::type;
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator> (const FloatingPointType& f, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, bool>::type;
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator< (const FloatingPointType& f, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, bool>::type;
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator>=(const FloatingPointType& f, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, bool>::type;
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator<=(const FloatingPointType& f, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, bool>::type;
  #endif

  #if !defined(WIDE_INTEGER_DISABLE_IOSTREAM)

  // Forward declarations of I/O streaming functions.
  template<typename char_type,
           typename traits_type,
           const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  auto operator<<(std::basic_ostream<char_type, traits_type>& out,
                                     const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& x) -> std::basic_ostream<char_type, traits_type>&;

  template<typename char_type,
           typename traits_type,
           const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  auto operator>>(std::basic_istream<char_type, traits_type>& in,
                  uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& x) -> std::basic_istream<char_type, traits_type>&;

  #endif

  // Forward declarations of various number-theoretical tools.
  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  WIDE_INTEGER_CONSTEXPR void swap(uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& x,
                                   uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& y);

  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  WIDE_INTEGER_CONSTEXPR auto lsb(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& x) -> unsigned_fast_type;

  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  WIDE_INTEGER_CONSTEXPR auto msb(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& x) -> unsigned_fast_type;

  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  constexpr auto abs(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& x) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;

  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  WIDE_INTEGER_CONSTEXPR auto sqrt(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& m) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;

  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  WIDE_INTEGER_CONSTEXPR auto cbrt(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& m) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;

  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  WIDE_INTEGER_CONSTEXPR auto rootk(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& m, const std::uint_fast8_t k) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned>; // NOLINT(readability-avoid-const-params-in-decls)

  template<typename OtherUnsignedIntegralTypeP,
           const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  WIDE_INTEGER_CONSTEXPR auto pow(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& b, const OtherUnsignedIntegralTypeP& p) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;

  template<typename OtherUnsignedIntegralTypeP,
           typename OtherUnsignedIntegralTypeM,
           const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  WIDE_INTEGER_CONSTEXPR auto powm(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& b,
                                   const OtherUnsignedIntegralTypeP&    p,
                                   const OtherUnsignedIntegralTypeM&    m) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;

  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  WIDE_INTEGER_CONSTEXPR auto gcd(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& a,
                                  const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& b) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;

  template<typename UnsignedShortType>
  WIDE_INTEGER_CONSTEXPR auto gcd(const UnsignedShortType& u, const UnsignedShortType& v) -> typename std::enable_if<(   (std::is_integral<UnsignedShortType>::value)
                                                                                                                      && (std::is_unsigned<UnsignedShortType>::value)), UnsignedShortType>::type;

  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  WIDE_INTEGER_CONSTEXPR auto lcm(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& a,
                                  const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& b) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;

  template<typename UnsignedShortType>
  WIDE_INTEGER_CONSTEXPR auto lcm(const UnsignedShortType& a, const UnsignedShortType& b) -> typename std::enable_if<(   (std::is_integral<UnsignedShortType>::value)
                                                                                                                      && (std::is_unsigned<UnsignedShortType>::value)), UnsignedShortType>::type;

  template<const size_t Width2,
           typename LimbType = std::uint32_t,
           typename AllocatorType = void,
           const bool IsSigned = false>
  class default_random_engine;

  template<const size_t Width2,
           typename LimbType = std::uint32_t,
           typename AllocatorType = void,
           const bool IsSigned = false>
  class uniform_int_distribution;

  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  constexpr auto operator==(const uniform_int_distribution<Width2, LimbType, AllocatorType, IsSigned>& lhs,
                            const uniform_int_distribution<Width2, LimbType, AllocatorType, IsSigned>& rhs) -> bool;

  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  constexpr auto operator!=(const uniform_int_distribution<Width2, LimbType, AllocatorType, IsSigned>& lhs,
                            const uniform_int_distribution<Width2, LimbType, AllocatorType, IsSigned>& rhs) -> bool;

  template<typename DistributionType,
           typename GeneratorType,
           const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  auto miller_rabin(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& n,
                    const unsigned_fast_type                                     number_of_trials, // NOLINT(readability-avoid-const-params-in-decls)
                          DistributionType&                                      distribution,
                          GeneratorType&                                         generator) -> bool;

  #if(__cplusplus >= 201703L)
  } // namespace math::wide_integer
  #else
  } // namespace wide_integer
  } // namespace math
  #endif

  WIDE_INTEGER_NAMESPACE_END

  namespace std
  {
    // Forward declaration of specialization of std::numeric_limits<uintwide_t>.
    #if defined(WIDE_INTEGER_NAMESPACE)
    template<const WIDE_INTEGER_NAMESPACE::math::wide_integer::size_t Width2,
             typename LimbType,
             typename AllocatorType,
             const bool IsSigned>
    WIDE_INTEGER_NUM_LIMITS_CLASS_TYPE numeric_limits<WIDE_INTEGER_NAMESPACE::math::wide_integer::uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>;
    #else
    template<const ::math::wide_integer::size_t Width2,
             typename LimbType,
             typename AllocatorType,
             const bool IsSigned>
    WIDE_INTEGER_NUM_LIMITS_CLASS_TYPE numeric_limits<::math::wide_integer::uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>;
    #endif
  } // namespace std

  WIDE_INTEGER_NAMESPACE_BEGIN

  #if(__cplusplus >= 201703L)
  namespace math::wide_integer::detail {
  #else
  namespace math { namespace wide_integer { namespace detail { // NOLINT(modernize-concat-nested-namespaces)
  #endif

  template<typename MyType,
           const size_t MySize,
           typename MyAlloc>
  class fixed_dynamic_array final : public detail::dynamic_array<MyType, MyAlloc, size_t, ptrdiff_t>
  {
  private:
    using base_class_type = detail::dynamic_array<MyType, MyAlloc, size_t, ptrdiff_t>;

  public:
    static constexpr auto static_size() -> typename base_class_type::size_type { return MySize; }

    explicit WIDE_INTEGER_CONSTEXPR fixed_dynamic_array(const typename base_class_type::size_type       s = MySize,
                                                        const typename base_class_type::value_type&     v = typename base_class_type::value_type(),
                                                        const typename base_class_type::allocator_type& a = typename base_class_type::allocator_type())
      : base_class_type(MySize, typename base_class_type::value_type(), a)
    {
      std::fill(base_class_type::begin(),
                base_class_type::begin() + (std::min)(MySize, static_cast<typename base_class_type::size_type>(s)),
                v);
    }

    constexpr fixed_dynamic_array(const fixed_dynamic_array& other_array)
      : base_class_type(static_cast<const base_class_type&>(other_array)) { }

    WIDE_INTEGER_CONSTEXPR fixed_dynamic_array(std::initializer_list<typename base_class_type::value_type> lst)
      : base_class_type(MySize)
    {
      std::copy(lst.begin(),
                lst.begin() + (std::min)(static_cast<typename base_class_type::size_type>(lst.size()), MySize),
                base_class_type::begin());
    }

    constexpr fixed_dynamic_array(fixed_dynamic_array&& other_array) noexcept
      : base_class_type(static_cast<base_class_type&&>(other_array)) { }

    WIDE_INTEGER_CONSTEXPR auto operator=(const fixed_dynamic_array& other_array) -> fixed_dynamic_array& // NOLINT(cert-oop54-cpp)
    {
      base_class_type::operator=(static_cast<const base_class_type&>(other_array));

      return *this;
    }

    WIDE_INTEGER_CONSTEXPR auto operator=(fixed_dynamic_array&& other_array) noexcept -> fixed_dynamic_array&
    {
      base_class_type::operator=(static_cast<base_class_type&&>(other_array));

      return *this;
    }

    WIDE_INTEGER_CONSTEXPR ~fixed_dynamic_array() override = default;
  };

  template<typename MyType,
           const size_t MySize>
  class fixed_static_array final : public std::array<MyType, static_cast<std::size_t>(MySize)>
  {
  private:
    using base_class_type = std::array<MyType, static_cast<std::size_t>(MySize)>;

  public:
    using size_type  = size_t;
    using value_type = typename base_class_type::value_type;

    static constexpr auto static_size() -> size_type { return MySize; }

    constexpr fixed_static_array() = default;

    explicit WIDE_INTEGER_CONSTEXPR fixed_static_array(const size_type   s,
                                                       const value_type& v = value_type())
    {
      if(s < static_size())
      {
        std::fill(base_class_type::begin(),     base_class_type::begin() + s, v);
        std::fill(base_class_type::begin() + s, base_class_type::end(),       value_type());
      }
      else
      {
        base_class_type::fill(v);
      }
    }

    WIDE_INTEGER_CONSTEXPR fixed_static_array(const fixed_static_array&) = default;
    WIDE_INTEGER_CONSTEXPR fixed_static_array(fixed_static_array&&) noexcept = default;

    WIDE_INTEGER_CONSTEXPR ~fixed_static_array() = default;

    WIDE_INTEGER_CONSTEXPR auto operator=(const fixed_static_array& other_array) -> fixed_static_array& = default;
    WIDE_INTEGER_CONSTEXPR auto operator=(fixed_static_array&& other_array) noexcept -> fixed_static_array& = default;

    WIDE_INTEGER_CONSTEXPR auto operator[](const size_type i)       -> typename base_class_type::reference       { return base_class_type::operator[](static_cast<typename base_class_type::size_type>(i)); }
    WIDE_INTEGER_CONSTEXPR auto operator[](const size_type i) const -> typename base_class_type::const_reference { return base_class_type::operator[](static_cast<typename base_class_type::size_type>(i)); }
  };

  template<const size_t Width2> struct verify_power_of_two_times_granularity_one_sixty_fourth // NOLINT(altera-struct-pack-align)
  {
    // List of numbers used to identify the form 2^n times 1...63.
    static constexpr bool conditional_value =
       (   verify_power_of_two<static_cast<size_t>(Width2 /  1U)>::conditional_value || verify_power_of_two<static_cast<size_t>(Width2 /  3U)>::conditional_value
        || verify_power_of_two<static_cast<size_t>(Width2 /  5U)>::conditional_value || verify_power_of_two<static_cast<size_t>(Width2 /  7U)>::conditional_value
        || verify_power_of_two<static_cast<size_t>(Width2 /  9U)>::conditional_value || verify_power_of_two<static_cast<size_t>(Width2 / 11U)>::conditional_value
        || verify_power_of_two<static_cast<size_t>(Width2 / 13U)>::conditional_value || verify_power_of_two<static_cast<size_t>(Width2 / 15U)>::conditional_value
        || verify_power_of_two<static_cast<size_t>(Width2 / 17U)>::conditional_value || verify_power_of_two<static_cast<size_t>(Width2 / 19U)>::conditional_value
        || verify_power_of_two<static_cast<size_t>(Width2 / 21U)>::conditional_value || verify_power_of_two<static_cast<size_t>(Width2 / 23U)>::conditional_value
        || verify_power_of_two<static_cast<size_t>(Width2 / 25U)>::conditional_value || verify_power_of_two<static_cast<size_t>(Width2 / 27U)>::conditional_value
        || verify_power_of_two<static_cast<size_t>(Width2 / 29U)>::conditional_value || verify_power_of_two<static_cast<size_t>(Width2 / 31U)>::conditional_value
        || verify_power_of_two<static_cast<size_t>(Width2 / 33U)>::conditional_value || verify_power_of_two<static_cast<size_t>(Width2 / 35U)>::conditional_value
        || verify_power_of_two<static_cast<size_t>(Width2 / 37U)>::conditional_value || verify_power_of_two<static_cast<size_t>(Width2 / 39U)>::conditional_value
        || verify_power_of_two<static_cast<size_t>(Width2 / 41U)>::conditional_value || verify_power_of_two<static_cast<size_t>(Width2 / 43U)>::conditional_value
        || verify_power_of_two<static_cast<size_t>(Width2 / 45U)>::conditional_value || verify_power_of_two<static_cast<size_t>(Width2 / 47U)>::conditional_value
        || verify_power_of_two<static_cast<size_t>(Width2 / 49U)>::conditional_value || verify_power_of_two<static_cast<size_t>(Width2 / 51U)>::conditional_value
        || verify_power_of_two<static_cast<size_t>(Width2 / 53U)>::conditional_value || verify_power_of_two<static_cast<size_t>(Width2 / 55U)>::conditional_value
        || verify_power_of_two<static_cast<size_t>(Width2 / 57U)>::conditional_value || verify_power_of_two<static_cast<size_t>(Width2 / 59U)>::conditional_value
        || verify_power_of_two<static_cast<size_t>(Width2 / 61U)>::conditional_value || verify_power_of_two<static_cast<size_t>(Width2 / 63U)>::conditional_value);
  };

  template<typename UnsignedIntegralType>
  inline WIDE_INTEGER_CONSTEXPR auto lsb_helper(const UnsignedIntegralType& u) -> unsigned_fast_type;

  template<typename UnsignedIntegralType>
  inline WIDE_INTEGER_CONSTEXPR auto msb_helper(const UnsignedIntegralType& u) -> unsigned_fast_type;

  template<>
  inline WIDE_INTEGER_CONSTEXPR auto msb_helper<std::uint32_t>(const std::uint32_t& u) -> unsigned_fast_type;

  template<>
  inline WIDE_INTEGER_CONSTEXPR auto msb_helper<std::uint16_t>(const std::uint16_t& u) -> unsigned_fast_type;

  template<>
  inline WIDE_INTEGER_CONSTEXPR auto msb_helper<std::uint8_t>(const std::uint8_t& u) -> unsigned_fast_type;

  // Use a local implementation of string copy.
  inline WIDE_INTEGER_CONSTEXPR auto strcpy_unsafe(char* dst, const char* src) -> char*
  {
    while((*dst++ = *src++) != static_cast<char>('\0')) { ; } // NOLINT(cppcoreguidelines-pro-bounds-pointer-arithmetic)

    return dst;
  }

  // Use a local implementation of string length.
  inline WIDE_INTEGER_CONSTEXPR auto strlen_unsafe(const char* p_str) -> unsigned_fast_type
  {
    const char* p_str_copy{};

    for(p_str_copy = p_str; (*p_str_copy != static_cast<char>('\0')); ++p_str_copy) { ; } // NOLINT(cppcoreguidelines-pro-bounds-pointer-arithmetic,altera-id-dependent-backward-branch)

    return static_cast<unsigned_fast_type>(p_str_copy - p_str);
  }

  template<typename UnsignedShortType,
           typename UnsignedLargeType = typename detail::uint_type_helper<static_cast<size_t>(std::numeric_limits<UnsignedShortType>::digits * 2)>::exact_unsigned_type>
  constexpr auto make_lo(const UnsignedLargeType& u) -> UnsignedShortType
  {
    // From an unsigned integral input parameter of type UnsignedLargeType,
    // extract the low part of it. The type of the extracted
    // low part is UnsignedShortType, which has half the width of UnsignedLargeType.

    using local_ushort_type = UnsignedShortType;
    using local_ularge_type = UnsignedLargeType;

    // Compile-time checks.
    #if defined(WIDE_INTEGER_HAS_LIMB_TYPE_UINT64)
    static_assert(((sizeof(local_ushort_type) * 2U) == sizeof(local_ularge_type)),
                   "Error: Please check the characteristics of the template parameters UnsignedShortType and UnsignedLargeType");
    #else
    static_assert((    ( std::numeric_limits<local_ushort_type>::is_integer)
                   &&  ( std::numeric_limits<local_ularge_type>::is_integer)
                   &&  (!std::numeric_limits<local_ushort_type>::is_signed)
                   &&  (!std::numeric_limits<local_ularge_type>::is_signed)
                   &&  ((sizeof(local_ushort_type) * 2U) == sizeof(local_ularge_type))),
                   "Error: Please check the characteristics of the template parameters UnsignedShortType and UnsignedLargeType");
    #endif

    return static_cast<local_ushort_type>(u);
  }

  template<typename UnsignedShortType,
           typename UnsignedLargeType = typename detail::uint_type_helper<static_cast<size_t>(std::numeric_limits<UnsignedShortType>::digits * 2)>::exact_unsigned_type>
  constexpr auto make_hi(const UnsignedLargeType& u) -> UnsignedShortType
  {
    // From an unsigned integral input parameter of type UnsignedLargeType,
    // extract the high part of it. The type of the extracted
    // high part is UnsignedShortType, which has half the width of UnsignedLargeType.

    using local_ushort_type = UnsignedShortType;
    using local_ularge_type = UnsignedLargeType;

    // Compile-time checks.
    #if defined(WIDE_INTEGER_HAS_LIMB_TYPE_UINT64)
    static_assert(((sizeof(local_ushort_type) * 2U) == sizeof(local_ularge_type)),
                   "Error: Please check the characteristics of the template parameters UnsignedShortType and UnsignedLargeType");
    #else
    static_assert((    ( std::numeric_limits<local_ushort_type>::is_integer)
                   &&  ( std::numeric_limits<local_ularge_type>::is_integer)
                   &&  (!std::numeric_limits<local_ushort_type>::is_signed)
                   &&  (!std::numeric_limits<local_ularge_type>::is_signed)
                   &&  ((sizeof(local_ushort_type) * 2U) == sizeof(local_ularge_type))),
                   "Error: Please check the characteristics of the template parameters UnsignedShortType and UnsignedLargeType");
    #endif

    return static_cast<local_ushort_type>(u >> static_cast<local_ushort_type>(std::numeric_limits<local_ushort_type>::digits));
  }

  template<typename UnsignedShortType,
           typename UnsignedLargeType = typename detail::uint_type_helper<static_cast<size_t>(std::numeric_limits<UnsignedShortType>::digits * 2)>::exact_unsigned_type>
  constexpr auto make_large(const UnsignedShortType& lo, const UnsignedShortType& hi) -> UnsignedLargeType
  {
    // Create a composite unsigned integral value having type UnsignedLargeType.
    // Two constituents are used having type UnsignedShortType, whereby the
    // width of UnsignedShortType is half the width of UnsignedLargeType.

    using local_ushort_type = UnsignedShortType;
    using local_ularge_type = UnsignedLargeType;

    // Compile-time checks.
    #if defined(WIDE_INTEGER_HAS_LIMB_TYPE_UINT64)
    static_assert(((sizeof(local_ushort_type) * 2U) == sizeof(local_ularge_type)),
                   "Error: Please check the characteristics of the template parameters UnsignedShortType and UnsignedLargeType");
    #else
    static_assert((    ( std::numeric_limits<local_ushort_type>::is_integer)
                   &&  ( std::numeric_limits<local_ularge_type>::is_integer)
                   &&  (!std::numeric_limits<local_ushort_type>::is_signed)
                   &&  (!std::numeric_limits<local_ularge_type>::is_signed)
                   &&  ((sizeof(local_ushort_type) * 2U) == sizeof(local_ularge_type))),
                   "Error: Please check the characteristics of the template parameters UnsignedShortType and UnsignedLargeType");
    #endif

    return static_cast<local_ularge_type>(static_cast<local_ularge_type>(static_cast<local_ularge_type>(hi) << static_cast<unsigned>(std::numeric_limits<UnsignedShortType>::digits)) | lo);
  }

  template<typename UnsignedIntegralType>
  constexpr auto negate(UnsignedIntegralType u) -> typename std::enable_if<   (std::is_integral<UnsignedIntegralType>::value)
                                                                           && (std::is_unsigned<UnsignedIntegralType>::value), UnsignedIntegralType>::type
  {
    return static_cast<UnsignedIntegralType>((static_cast<UnsignedIntegralType>(~u)) + 1U);
  }

  template<typename SignedIntegralType>
  constexpr auto negate(SignedIntegralType n) -> typename std::enable_if<   (std::is_integral<SignedIntegralType>::value)
                                                                         && (std::is_signed  <SignedIntegralType>::value), SignedIntegralType>::type
  {
    using local_unsigned_type =
      typename detail::uint_type_helper<static_cast<size_t>(std::numeric_limits<SignedIntegralType>::digits + 1)>::exact_unsigned_type;

    return static_cast<SignedIntegralType>(negate(static_cast<local_unsigned_type>(n)));
  }

  #if !defined(WIDE_INTEGER_DISABLE_FLOAT_INTEROP)
  template<typename FloatingPointType>
  class native_float_parts final
  {
  public:
    // Emphasize: This template class can be used with native floating-point
    // types like float, double and long double. Note: For long double,
    // you need to verify that the mantissa fits in unsigned long long.
    explicit WIDE_INTEGER_CONSTEXPR native_float_parts(const FloatingPointType f)
      : my_mantissa_part(0ULL),
        my_exponent_part(0)
    {
      using native_float_type = FloatingPointType;

      static_assert(std::numeric_limits<native_float_type>::digits <= std::numeric_limits<unsigned long long>::digits, // NOLINT(google-runtime-int)
                    "Error: The width of the mantissa does not fit in unsigned long long");

      const native_float_type ff = ((f < static_cast<native_float_type>(0)) ? -f : f);

      if(ff < (std::numeric_limits<native_float_type>::min)())
      {
        return;
      }

      using my_own::frexp;

      // Get the fraction and base-2 exponent.
      auto man = static_cast<native_float_type>(frexp(f, &my_exponent_part));

      unsigned n2 = 0U;

      for(auto i = static_cast<std::uint_fast16_t>(0U); i < static_cast<std::uint_fast16_t>(std::numeric_limits<native_float_type>::digits); ++i)
      {
        // Extract the mantissa of the floating-point type in base-2
        // (one bit at a time) and store it in an unsigned long long.
        man *= 2;

        n2   = static_cast<unsigned>(man);
        man -= static_cast<native_float_type>(n2);

        if(n2 != static_cast<unsigned>(0U))
        {
          my_mantissa_part |= 1U;
        }

        if(i < static_cast<unsigned>(std::numeric_limits<native_float_type>::digits - 1))
        {
          my_mantissa_part <<= 1U;
        }
      }

      // Ensure that the value is normalized and adjust the exponent.
      my_mantissa_part |= static_cast<unsigned long long>(1ULL << static_cast<unsigned>(std::numeric_limits<native_float_type>::digits - 1)); // NOLINT(google-runtime-int)
      my_exponent_part -= 1;
    }

    constexpr native_float_parts(const native_float_parts& other) : my_mantissa_part(other.my_mantissa_part),
                                                                    my_exponent_part(other.my_exponent_part) { }

    constexpr native_float_parts(native_float_parts&& other) noexcept : my_mantissa_part(other.my_mantissa_part),
                                                                        my_exponent_part(other.my_exponent_part) { }

    WIDE_INTEGER_CONSTEXPR ~native_float_parts() = default;

    WIDE_INTEGER_CONSTEXPR auto operator=(const native_float_parts& other) noexcept -> native_float_parts&
    {
      if(this != &other)
      {
        my_mantissa_part = other.my_mantissa_part;
        my_exponent_part = other.my_exponent_part;
      }

      return *this;
    }

    WIDE_INTEGER_CONSTEXPR auto operator=(native_float_parts&& other) noexcept -> native_float_parts&
    {
      my_mantissa_part = other.my_mantissa_part;
      my_exponent_part = other.my_exponent_part;

      return *this;
    }

    WIDE_INTEGER_NODISCARD WIDE_INTEGER_CONSTEXPR auto get_mantissa() const -> unsigned long long { return my_mantissa_part; } // NOLINT(google-runtime-int)
    WIDE_INTEGER_NODISCARD WIDE_INTEGER_CONSTEXPR auto get_exponent() const -> int                { return my_exponent_part; }

    WIDE_INTEGER_CONSTEXPR native_float_parts() = delete;

  private:
    unsigned long long my_mantissa_part; // NOLINT(readability-identifier-naming,google-runtime-int)
    int                my_exponent_part; // NOLINT(readability-identifier-naming)
  };
  #endif

  #if(__cplusplus >= 201703L)
  } // namespace math::wide_integer::detail
  #else
  } // namespace detail
  } // namespace wide_integer
  } // namespace math
  #endif

  #if(__cplusplus >= 201703L)
  namespace math::wide_integer {
  #else
  namespace math { namespace wide_integer { // NOLINT(modernize-concat-nested-namespaces)
  #endif

  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  class uintwide_t
  {
  public:
    template<const size_t OtherWidth2,
             typename OtherLimbType,
             typename OtherAllocatorType,
             const bool OtherIsSigned>
    friend class uintwide_t;

    // Class-local type definitions.
    using limb_type = LimbType;

    using double_limb_type =
      typename detail::uint_type_helper<static_cast<size_t>(std::numeric_limits<limb_type>::digits * 2)>::exact_unsigned_type;

    // Legacy ularge and ushort types. These are no longer used
    // in the class, but provided for legacy compatibility.
    using ushort_type = limb_type;
    using ularge_type = double_limb_type;

    // More compile-time checks.
    #if defined(WIDE_INTEGER_HAS_LIMB_TYPE_UINT64)
    static_assert(((sizeof(limb_type) * 2U) == sizeof(double_limb_type)),
                   "Error: Please check the characteristics of the template parameters UnsignedShortType and UnsignedLargeType");
    #else
    static_assert((    ( std::numeric_limits<limb_type>::is_integer)
                   &&  ( std::numeric_limits<double_limb_type>::is_integer)
                   &&  (!std::numeric_limits<limb_type>::is_signed)
                   &&  (!std::numeric_limits<double_limb_type>::is_signed)
                   &&  ((sizeof(limb_type) * 2U) == sizeof(double_limb_type))),
                   "Error: Please check the characteristics of the template parameters UnsignedShortType and UnsignedLargeType");
    #endif

    // Helper constants for the digit characteristics.
    static constexpr size_t my_width2 = Width2;

    // The number of limbs.
    static constexpr size_t number_of_limbs =
      static_cast<size_t>(my_width2 / static_cast<size_t>(std::numeric_limits<limb_type>::digits));

    static constexpr size_t number_of_limbs_karatsuba_threshold = static_cast<size_t>(128U + 1U);

    // Verify that the Width2 template parameter (mirrored with my_width2):
    //   * Is equal to 2^n times 1...63.
    //   * And that there are at least 16, 24 or 32 binary digits, or more.
    //   * And that the number of binary digits is an exact multiple of the number of limbs.
    static_assert(   (detail::verify_power_of_two_times_granularity_one_sixty_fourth<my_width2>::conditional_value)
                  && (my_width2 >= 16U) // NOLINT(cppcoreguidelines-avoid-magic-numbers,readability-magic-numbers)
                  && (my_width2 == (number_of_limbs * static_cast<size_t>(std::numeric_limits<limb_type>::digits))),
                  "Error: Width2 must be 2^n times 1...63 (with n >= 3), while being 16, 24, 32 or larger, and exactly divisible by limb count");

    // The type of the internal data representation.
    using representation_type =
      typename std::conditional
        <std::is_same<AllocatorType, void>::value,
         detail::fixed_static_array <limb_type,
                                     number_of_limbs>,
         detail::fixed_dynamic_array<limb_type,
                                     number_of_limbs,
                                     typename std::allocator_traits<typename std::conditional<std::is_same<AllocatorType, void>::value,
                                                                                              std::allocator<void>,
                                                                                              AllocatorType>::type>::template rebind_alloc<limb_type>>
        >::type;

    // The iterator types of the internal data representation.
    using iterator               = typename representation_type::iterator;
    using const_iterator         = typename representation_type::const_iterator;
    using reverse_iterator       = typename representation_type::reverse_iterator;
    using const_reverse_iterator = typename representation_type::const_reverse_iterator;

    // Define a class-local type that has double the width of *this.
    using double_width_type = uintwide_t<static_cast<size_t>(Width2 * 2U), limb_type, AllocatorType, IsSigned>;

    // Default constructor.
    constexpr uintwide_t() = default;

    // Constructors from built-in unsigned integral types that
    // are less wide than limb_type or exactly as wide as limb_type.
    template<typename UnsignedIntegralType>
    constexpr uintwide_t(const UnsignedIntegralType v, // NOLINT(google-explicit-constructor,hicpp-explicit-conversions)
                         typename std::enable_if<(   (std::is_integral   <UnsignedIntegralType>::value)
                                                  && (std::is_unsigned   <UnsignedIntegralType>::value)
                                                  && (std::numeric_limits<UnsignedIntegralType>::digits <= std::numeric_limits<limb_type>::digits))>::type* = nullptr) // NOLINT(hicpp-named-parameter,readability-named-parameter)
      : values(1U, v) { }

    // Constructors from built-in unsigned integral types that
    // are wider than limb_type, and do not have exactly the
    // same width as limb_type.
    template<typename UnsignedIntegralType>
    WIDE_INTEGER_CONSTEXPR uintwide_t(const UnsignedIntegralType v, // NOLINT(google-explicit-constructor,hicpp-explicit-conversions)
                                      typename std::enable_if<(   (std::is_integral   <UnsignedIntegralType>::value)
                                                               && (std::is_unsigned   <UnsignedIntegralType>::value)
                                                               && (std::numeric_limits<UnsignedIntegralType>::digits > std::numeric_limits<limb_type>::digits))>::type* p_nullparam = nullptr)
    {
      static_cast<void>(p_nullparam == nullptr);

      auto right_shift_amount_v = static_cast<unsigned_fast_type>(0U);
      auto index_u              = static_cast<std::uint_fast8_t> (0U);

      for( ; (   (index_u < values.size()) // NOLINT(altera-id-dependent-backward-branch)
              && (right_shift_amount_v < static_cast<unsigned_fast_type>(std::numeric_limits<UnsignedIntegralType>::digits)));
             ++index_u)
      {
        *(values.begin() + static_cast<size_t>(index_u)) = static_cast<limb_type>(v >> static_cast<unsigned>(right_shift_amount_v));

        right_shift_amount_v += static_cast<unsigned_fast_type>(std::numeric_limits<limb_type>::digits);
      }

      std::fill(values.begin() + index_u, values.end(), static_cast<limb_type>(0U));
    }

    // Constructors from built-in signed integral types.
    template<typename SignedIntegralType>
    WIDE_INTEGER_CONSTEXPR uintwide_t(const SignedIntegralType v, // NOLINT(google-explicit-constructor,hicpp-explicit-conversions)
                                      typename std::enable_if<(   (std::is_integral<SignedIntegralType>::value)
                                                               && (std::is_signed  <SignedIntegralType>::value))>::type* p_nullparam = nullptr)
    {
      static_cast<void>(p_nullparam == nullptr);

      using local_signed_integral_type   = SignedIntegralType;
      using local_unsigned_integral_type =
        typename detail::uint_type_helper<static_cast<size_t>(std::numeric_limits<local_signed_integral_type>::digits + 1)>::exact_unsigned_type;

      const bool v_is_neg = (v < static_cast<local_signed_integral_type>(0));

      const local_unsigned_integral_type u =
        ((!v_is_neg) ? static_cast<local_unsigned_integral_type>(v)
                     : static_cast<local_unsigned_integral_type>(detail::negate(v)));

      operator=(uintwide_t(u));

      if(v_is_neg) { negate(); }
    }

    #if !defined(WIDE_INTEGER_DISABLE_FLOAT_INTEROP)
    template<typename FloatingPointType,
             typename std::enable_if<(std::is_floating_point<FloatingPointType>::value)>::type const* = nullptr>
    WIDE_INTEGER_CONSTEXPR uintwide_t(const FloatingPointType f) // NOLINT(google-explicit-constructor,hicpp-explicit-conversions)
    {
      using local_builtin_float_type = FloatingPointType;

      using detail::my_own::isfinite;

      if(!isfinite(f))
      {
        operator=(0U);
      }
      else
      {
        const bool f_is_neg = (f < static_cast<local_builtin_float_type>(0.0F));

        const local_builtin_float_type a = ((!f_is_neg) ? f : -f);

        const bool a_is_zero = (a < static_cast<local_builtin_float_type>(1.0F));

        if(!a_is_zero)
        {
          const detail::native_float_parts<local_builtin_float_type> ld_parts(a);

          // Create a decwide_t from the fractional part of the
          // mantissa expressed as an unsigned long long.
          *this = uintwide_t(ld_parts.get_mantissa());

          // Scale the unsigned long long representation to the fractional
          // part of the long double and multiply with the base-2 exponent.
          const int p2 = ld_parts.get_exponent() - (std::numeric_limits<FloatingPointType>::digits - 1);

          if     (p2 <   0) { *this >>= static_cast<unsigned>(-p2); }
          else if(p2 ==  0) { ; }
          else              { *this <<= static_cast<unsigned>( p2); }

          if(f_is_neg)
          {
            negate();
          }
        }
        else
        {
          operator=(0U);
        }
      }
    }
    #endif

    // Copy constructor.
    #if !defined(WIDE_INTEGER_DISABLE_TRIVIAL_COPY_AND_STD_LAYOUT_CHECKS)
    constexpr uintwide_t(const uintwide_t& other) = default;
    #else
    constexpr uintwide_t(const uintwide_t& other) : values(other.values) { }
    #endif

    // Copy-like constructor from the other signed-ness type.
    template<const bool OtherIsSigned,
             typename std::enable_if<(OtherIsSigned != IsSigned)>::type const* = nullptr>
    constexpr uintwide_t(const uintwide_t<Width2, LimbType, AllocatorType, OtherIsSigned>& other) // NOLINT(google-explicit-constructor,hicpp-explicit-conversions)
      : values(other.values) { }

    // Copy-like constructor from the another type having width that is wider
    // (but has the same limb type) and possibly a different signed-ness.
    template<const size_t OtherWidth2,
             const bool OtherIsSigned,
             typename std::enable_if<(Width2 < OtherWidth2)>::type const* = nullptr>
    explicit WIDE_INTEGER_CONSTEXPR uintwide_t(const uintwide_t<OtherWidth2, LimbType, AllocatorType, OtherIsSigned>& v)
    {
      using other_wide_integer_type = uintwide_t<OtherWidth2, LimbType, AllocatorType, OtherIsSigned>;

      const bool v_is_neg = (other_wide_integer_type::is_neg(v));

      constexpr auto sz = static_cast<size_t>(number_of_limbs);

      if(!v_is_neg)
      {
        std::copy(v.crepresentation().cbegin(),
                  v.crepresentation().cbegin() + sz,
                  values.begin());
      }
      else
      {
        const other_wide_integer_type uv(-v);

        std::copy(uv.crepresentation().cbegin(),
                  uv.crepresentation().cbegin() + sz,
                  values.begin());

        negate();
      }
    }

    // Copy-like constructor from the another type having width that is less wide
    // (but has the same limb type) and possibly a different signed-ness.
    template<const size_t OtherWidth2,
             const bool OtherIsSigned,
             typename std::enable_if<(Width2 > OtherWidth2)>::type const* = nullptr>
    explicit WIDE_INTEGER_CONSTEXPR uintwide_t(const uintwide_t<OtherWidth2, LimbType, AllocatorType, OtherIsSigned>& v)
    {
      using other_wide_integer_type = uintwide_t<OtherWidth2, LimbType, AllocatorType, OtherIsSigned>;

      const bool v_is_neg = (other_wide_integer_type::is_neg(v));

      constexpr auto sz = static_cast<size_t>(other_wide_integer_type::number_of_limbs);

      if(!v_is_neg)
      {
        std::copy(v.crepresentation().cbegin(),
                  v.crepresentation().cbegin() + sz,
                  values.begin());

        std::fill(values.begin() + sz, values.end(), static_cast<limb_type>(0U));
      }
      else
      {
        const other_wide_integer_type uv(-v);

        std::copy(uv.crepresentation().cbegin(),
                  uv.crepresentation().cbegin() + sz,
                  values.begin());

        std::fill(values.begin() + sz, values.end(), static_cast<limb_type>(0U));

        negate();
      }
    }

    // Constructor from a constant character string.
    WIDE_INTEGER_CONSTEXPR uintwide_t(const char* str_input) // NOLINT(google-explicit-constructor,hicpp-explicit-conversions)
    {
      if(!rd_string(str_input))
      {
        std::fill(values.begin(), values.end(), (std::numeric_limits<limb_type>::max)());
      }
    }

    // Move constructor.
    constexpr uintwide_t(uintwide_t&& other) noexcept = default;

    // Move-like constructor from the other signed-ness type.
    // This constructor is non-explicit because it is a trivial conversion.
    template<const bool OtherIsSigned,
             typename std::enable_if<(IsSigned != OtherIsSigned)>::type const* = nullptr>
    constexpr uintwide_t(uintwide_t<Width2, LimbType, AllocatorType, OtherIsSigned>&& other) // NOLINT(google-explicit-constructor,hicpp-explicit-conversions)
      : values(static_cast<representation_type&&>(other.values)) { }

    // Default destructor.
    WIDE_INTEGER_CONSTEXPR ~uintwide_t() = default;

    // Assignment operator.
    WIDE_INTEGER_CONSTEXPR auto operator=(const uintwide_t& other) -> uintwide_t& = default;

    // Assignment operator from the other signed-ness type.
    template<const bool OtherIsSigned,
             typename std::enable_if<(OtherIsSigned != IsSigned)>::type const* = nullptr>
    WIDE_INTEGER_CONSTEXPR auto operator=(const uintwide_t<Width2, LimbType, AllocatorType, OtherIsSigned>& other) -> uintwide_t&
    {
      values = other.values;

      return *this;
    }

    // Trivial move assignment operator.
    WIDE_INTEGER_CONSTEXPR auto operator=(uintwide_t&& other) noexcept -> uintwide_t& = default;

    // Trivial move assignment operator from the other signed-ness type.
    template<const bool OtherIsSigned,
             typename std::enable_if<(IsSigned != OtherIsSigned)>::type const* = nullptr>
    WIDE_INTEGER_CONSTEXPR auto operator=(uintwide_t<Width2, LimbType, AllocatorType, OtherIsSigned>&& other) -> uintwide_t&
    {
      values = static_cast<representation_type&&>(other.values);

      return *this;
    }

    #if !defined(WIDE_INTEGER_DISABLE_FLOAT_INTEROP)
    explicit constexpr operator long double() const { return extract_builtin_floating_point_type<long double>(); }
    explicit constexpr operator double     () const { return extract_builtin_floating_point_type<double>     (); }
    explicit constexpr operator float      () const { return extract_builtin_floating_point_type<float>      (); }
    #endif

    template<typename IntegralType,
             typename = typename std::enable_if<std::is_integral<IntegralType>::value>::type>
    explicit constexpr operator IntegralType() const
    {
      using local_integral_type = IntegralType;

      return ((!is_neg(*this))
               ? extract_builtin_integral_type<local_integral_type>()
               : detail::negate((-*this).template extract_builtin_integral_type<local_integral_type>()));
    }

    // Cast operator to built-in Boolean type.
    explicit constexpr operator bool() const { return (!is_zero()); }

    // Cast operator that casts to a uintwide_t having a different width
    // (but having the same limb type) and possibly a different signed-ness.
    template<const size_t OtherWidth2,
             const bool OtherIsSigned,
             typename = typename std::enable_if<(Width2 != OtherWidth2), uintwide_t<OtherWidth2, LimbType, AllocatorType, OtherIsSigned>>::type>
    WIDE_INTEGER_CONSTEXPR operator uintwide_t<OtherWidth2, LimbType, AllocatorType, OtherIsSigned>() const // NOLINT(hicpp-explicit-conversions,google-explicit-constructor)
    {
      const bool this_is_neg = (is_neg(*this));

      using other_wide_integer_type = uintwide_t<OtherWidth2, LimbType, AllocatorType, OtherIsSigned>;

      constexpr auto sz =
        static_cast<size_t>
        (
          (Width2 < OtherWidth2) ? static_cast<size_t>(number_of_limbs)
                                 : static_cast<size_t>(other_wide_integer_type::number_of_limbs)
        );

      other_wide_integer_type other;

      if(!this_is_neg)
      {
        std::copy(crepresentation().cbegin(),
                  crepresentation().cbegin() + sz,
                  other.values.begin());

        if(Width2 < OtherWidth2)
        {
          std::fill(other.values.begin() + sz, other.values.end(), static_cast<limb_type>(0U));
        }
      }
      else
      {
        other_wide_integer_type uv(*this);

        uv.negate();

        std::copy(uv.crepresentation().cbegin(),
                  uv.crepresentation().cbegin() + sz,
                  other.values.begin());

        if(Width2 < OtherWidth2)
        {
          std::fill(other.values.begin() + sz, other.values.end(), static_cast<limb_type>(0U));
        }

        other.negate();
      }

      return other;
    }

    // Cast operator that casts to a uintwide_t having a type with the same width
    // (and having the same limb type) but definitely having a different signed-ness.
    template<const bool OtherIsSigned,
             typename = typename std::enable_if<(OtherIsSigned != IsSigned), uintwide_t<Width2, LimbType, AllocatorType, OtherIsSigned>>::type>
    WIDE_INTEGER_CONSTEXPR operator uintwide_t<Width2, LimbType, AllocatorType, OtherIsSigned>() const // NOLINT(hicpp-explicit-conversions,google-explicit-constructor)
    {
      using other_wide_integer_type = uintwide_t<Width2, LimbType, AllocatorType, OtherIsSigned>;

      other_wide_integer_type other;

      std::copy(crepresentation().cbegin(),
                crepresentation().cend(),
                other.representation().begin());

      return other;
    }

    // Provide a user interface to the internal data representation.
                           WIDE_INTEGER_CONSTEXPR auto  representation()       ->       representation_type& { return values; }
    WIDE_INTEGER_NODISCARD WIDE_INTEGER_CONSTEXPR auto  representation() const -> const representation_type& { return values; }
    WIDE_INTEGER_NODISCARD WIDE_INTEGER_CONSTEXPR auto crepresentation() const -> const representation_type& { return values; }

    // Unary operators: not, plus and minus.
    WIDE_INTEGER_CONSTEXPR auto operator+() const -> const uintwide_t& { return *this; }
    WIDE_INTEGER_CONSTEXPR auto operator-() const ->       uintwide_t  { uintwide_t tmp(*this); tmp.negate(); return tmp; }

    WIDE_INTEGER_CONSTEXPR auto operator+=(const uintwide_t& other) -> uintwide_t&
    {
      if(this == &other)
      {
        const uintwide_t self(other);

        // Unary addition function.
        const limb_type carry = eval_add_n(values.data(),
                                           values.data(),
                                           self.values.data(),
                                           static_cast<unsigned_fast_type>(number_of_limbs),
                                           static_cast<limb_type>(0U));

        static_cast<void>(carry);
      }
      else
      {
        // Unary addition function.
        const limb_type carry = eval_add_n(values.data(),
                                           values.data(),
                                           other.values.data(),
                                           static_cast<unsigned_fast_type>(number_of_limbs),
                                           static_cast<limb_type>(0U));

        static_cast<void>(carry);
      }

      return *this;
    }

    WIDE_INTEGER_CONSTEXPR auto operator-=(const uintwide_t& other) -> uintwide_t&
    {
      if(this == &other)
      {
        values.fill(0U);
      }
      else
      {
        // Unary subtraction function.
        const limb_type has_borrow = eval_subtract_n(values.data(),
                                                     values.data(),
                                                     other.values.data(),
                                                     number_of_limbs,
                                                     false);

        static_cast<void>(has_borrow);
      }

      return *this;
    }

    WIDE_INTEGER_CONSTEXPR auto operator*=(const uintwide_t& other) -> uintwide_t&
    {
      if(this == &other)
      {
        const uintwide_t other_as_self_copy(other); // NOLINT(performance-unnecessary-copy-initialization)

        eval_mul_unary(*this, other_as_self_copy);
      }
      else
      {
        eval_mul_unary(*this, other);
      }

      return *this;
    }

    WIDE_INTEGER_CONSTEXPR auto mul_by_limb(const limb_type v) -> uintwide_t&
    {
      if(v == static_cast<limb_type>(0U))
      {
        values.fill(0U);
      }
      else if(v > static_cast<limb_type>(1U))
      {
        static_cast<void>(eval_multiply_1d(values.data(),
                                           values.data(),
                                           v,
                                           number_of_limbs));
      }

      return *this;
    }

    WIDE_INTEGER_CONSTEXPR auto operator/=(const uintwide_t& other) -> uintwide_t&
    {
      if(this == &other)
      {
        values.front() = 1U;

        std::fill(values.begin() + 1U, values.end(), static_cast<limb_type>(0U));
      }
      else if(other.is_zero())
      {
        *this = limits_helper_max(IsSigned);
      }
      else
      {
        // Unary division function.

        const bool numererator_was_neg = is_neg(*this);
        const bool denominator_was_neg = is_neg(other);

        if(numererator_was_neg || denominator_was_neg)
        {
          using local_unsigned_wide_type = uintwide_t<Width2, limb_type, AllocatorType, false>;

          local_unsigned_wide_type a(*this);
          local_unsigned_wide_type b(other);

          if(numererator_was_neg) { a.negate(); }
          if(denominator_was_neg) { b.negate(); }

          a.eval_divide_knuth(b, nullptr);

          if(numererator_was_neg != denominator_was_neg) { a.negate(); }

          values = a.values;
        }
        else
        {
          eval_divide_knuth(other, nullptr);
        }
      }

      return *this;
    }

    WIDE_INTEGER_CONSTEXPR auto operator%=(const uintwide_t& other) -> uintwide_t&
    {
      if(this == &other)
      {
        std::fill(values.begin(), values.end(), static_cast<limb_type>(0U));
      }
      else
      {
        // Unary modulus function.
        const bool numererator_was_neg = is_neg(*this);
        const bool denominator_was_neg = is_neg(other);

        if(numererator_was_neg || denominator_was_neg)
        {
          using local_unsigned_wide_type = uintwide_t<Width2, limb_type, AllocatorType, false>;

          local_unsigned_wide_type a(*this);
          local_unsigned_wide_type b(other);

          if(numererator_was_neg) { a.negate(); }
          if(denominator_was_neg) { b.negate(); }

          local_unsigned_wide_type remainder;

          a.eval_divide_knuth(b, &remainder);

          // The sign of the remainder follows the sign of the denominator.
          if(numererator_was_neg) { remainder.negate(); }

          values = remainder.values;
        }
        else
        {
          uintwide_t remainder;

          eval_divide_knuth(other, &remainder);

          values = remainder.values;
        }
      }

      return *this;
    }

    // Operators pre-increment and pre-decrement.
    WIDE_INTEGER_CONSTEXPR auto operator++()  -> uintwide_t& { preincrement(); return *this; }
    WIDE_INTEGER_CONSTEXPR auto operator--()  -> uintwide_t& { predecrement(); return *this; }

    // Operators post-increment and post-decrement.
    WIDE_INTEGER_CONSTEXPR auto operator++(int) -> uintwide_t { const uintwide_t w(*this); preincrement(); return w; }
    WIDE_INTEGER_CONSTEXPR auto operator--(int) -> uintwide_t { const uintwide_t w(*this); predecrement(); return w; }

    WIDE_INTEGER_CONSTEXPR auto operator~() -> uintwide_t&
    {
      // Perform bitwise NOT.
      bitwise_not();

      return *this;
    }

    WIDE_INTEGER_CONSTEXPR auto operator|=(const uintwide_t& other) -> uintwide_t&
    {
      if(this != &other)
      {
        // Perform bitwise OR.
        for(auto i = static_cast<unsigned_fast_type>(0U); i < number_of_limbs; ++i)
        {
          *(values.begin() + static_cast<size_t>(i)) = static_cast<limb_type>(*(values.cbegin() + static_cast<size_t>(i)) | *(other.values.cbegin() + static_cast<size_t>(i)));
        }
      }

      return *this;
    }

    WIDE_INTEGER_CONSTEXPR auto operator^=(const uintwide_t& other) -> uintwide_t&
    {
      if(this == &other)
      {
        values.fill(0U);
      }
      else
      {
        // Perform bitwise XOR.
        for(auto i = static_cast<unsigned_fast_type>(0U); i < number_of_limbs; ++i)
        {
          *(values.begin() + static_cast<size_t>(i)) = static_cast<limb_type>(*(values.cbegin() + static_cast<size_t>(i)) ^ *(other.values.cbegin() + static_cast<size_t>(i)));
        }
      }

      return *this;
    }

    WIDE_INTEGER_CONSTEXPR auto operator&=(const uintwide_t& other) -> uintwide_t&
    {
      if(this != &other)
      {
        // Perform bitwise AND.
        for(auto i = static_cast<unsigned_fast_type>(0U); i < number_of_limbs; ++i)
        {
          *(values.begin() + static_cast<size_t>(i)) = static_cast<limb_type>(*(values.cbegin() + static_cast<size_t>(i)) & *(other.values.cbegin() + static_cast<size_t>(i)));
        }
      }

      return *this;
    }

    template<typename SignedIntegralType>
    WIDE_INTEGER_CONSTEXPR auto operator<<=(const SignedIntegralType n) -> typename std::enable_if<(   (std::is_integral<SignedIntegralType>::value)
                                                                                                    && (std::is_signed  <SignedIntegralType>::value)), uintwide_t>::type&
    {
      // Implement left-shift operator for signed integral argument.
      if(n < 0)
      {
        using local_unsigned_type =
          typename detail::uint_type_helper<static_cast<size_t>(std::numeric_limits<SignedIntegralType>::digits + 1)>::exact_unsigned_type;

        operator>>=(static_cast<local_unsigned_type>(detail::negate(n)));
      }
      else if(n == 0)
      {
        ;
      }
      else if(static_cast<unsigned_fast_type>(n) >= my_width2)
      {
        std::fill(values.begin(), values.end(), static_cast<limb_type>(0U));
      }
      else
      {
        const auto offset            = static_cast<unsigned_fast_type>(static_cast<unsigned_fast_type>(n) / static_cast<unsigned_fast_type>(std::numeric_limits<limb_type>::digits));
        const auto left_shift_amount = static_cast<std::uint_fast16_t>(static_cast<unsigned_fast_type>(n) % static_cast<unsigned_fast_type>(std::numeric_limits<limb_type>::digits));

        shl(offset, left_shift_amount);
      }

      return *this;
    }

    template<typename UnsignedIntegralType>
    WIDE_INTEGER_CONSTEXPR auto operator<<=(const UnsignedIntegralType n) -> typename std::enable_if<(   ( std::is_integral<UnsignedIntegralType>::value)
                                                                                                      && (!std::is_signed  <UnsignedIntegralType>::value)), uintwide_t>::type&
    {
      // Implement left-shift operator for unsigned integral argument.
      if(n == 0)
      {
        ;
      }
      else if(static_cast<unsigned_fast_type>(n) >= my_width2)
      {
        std::fill(values.begin(), values.end(), static_cast<limb_type>(0U));
      }
      else
      {
        const auto offset            = static_cast<unsigned_fast_type>(static_cast<unsigned_fast_type>(n) / static_cast<unsigned_fast_type>(std::numeric_limits<limb_type>::digits));
        const auto left_shift_amount = static_cast<std::uint_fast16_t>(static_cast<unsigned_fast_type>(n) % static_cast<unsigned_fast_type>(std::numeric_limits<limb_type>::digits));

        shl(offset, left_shift_amount);
      }

      return *this;
    }

    template<typename SignedIntegralType>
    WIDE_INTEGER_CONSTEXPR auto operator>>=(const SignedIntegralType n) -> typename std::enable_if<(   (std::is_integral<SignedIntegralType>::value)
                                                                                                    && (std::is_signed  <SignedIntegralType>::value)), uintwide_t>::type&
    {
      // Implement right-shift operator for signed integral argument.
      if(n < 0)
      {
        using local_unsigned_type =
          typename detail::uint_type_helper<static_cast<size_t>(std::numeric_limits<SignedIntegralType>::digits + 1)>::exact_unsigned_type;

        operator<<=(static_cast<local_unsigned_type>(detail::negate(n)));
      }
      else if(n == 0)
      {
        ;
      }
      else if(static_cast<unsigned_fast_type>(n) >= my_width2)
      {
        // Fill with either 0's or 1's. Note also the implementation-defined
        // behavior of excessive right-shift of negative value.
        if(!is_neg(*this))
        {
          std::fill(values.begin(), values.end(), static_cast<limb_type>(0U));
        }
        else
        {
          std::fill(values.begin(), values.end(), (std::numeric_limits<limb_type>::max)());
        }
      }
      else
      {
        const auto offset             = static_cast<unsigned_fast_type>(static_cast<unsigned_fast_type>(n) / static_cast<unsigned_fast_type>(std::numeric_limits<limb_type>::digits));
        const auto right_shift_amount = static_cast<std::uint_fast16_t>(static_cast<unsigned_fast_type>(n) % static_cast<unsigned_fast_type>(std::numeric_limits<limb_type>::digits));

        shr(offset, right_shift_amount);
      }

      return *this;
    }

    template<typename UnsignedIntegralType>
    WIDE_INTEGER_CONSTEXPR auto operator>>=(const UnsignedIntegralType n) -> typename std::enable_if<(   ( std::is_integral<UnsignedIntegralType>::value)
                                                                                                      && (!std::is_signed  <UnsignedIntegralType>::value)), uintwide_t>::type&
    {
      // Implement right-shift operator for unsigned integral argument.
      if(n == 0)
      {
        ;
      }
      else if(static_cast<unsigned_fast_type>(n) >= my_width2)
      {
        std::fill(values.begin(), values.end(), static_cast<limb_type>(0U));
      }
      else
      {
        const auto offset             = static_cast<unsigned_fast_type>(static_cast<unsigned_fast_type>(n) / static_cast<unsigned_fast_type>(std::numeric_limits<limb_type>::digits));
        const auto right_shift_amount = static_cast<std::uint_fast16_t>(static_cast<unsigned_fast_type>(n) % static_cast<unsigned_fast_type>(std::numeric_limits<limb_type>::digits));

        shr(offset, right_shift_amount);
      }

      return *this;
    }

    // Implement comparison operators.
    constexpr auto operator==(const uintwide_t& other) const -> bool { return (compare(other) == static_cast<std::int_fast8_t>( 0)); }
    constexpr auto operator< (const uintwide_t& other) const -> bool { return (compare(other) == static_cast<std::int_fast8_t>(-1)); }
    constexpr auto operator> (const uintwide_t& other) const -> bool { return (compare(other) == static_cast<std::int_fast8_t>( 1)); }
    constexpr auto operator!=(const uintwide_t& other) const -> bool { return (compare(other) != static_cast<std::int_fast8_t>( 0)); }
    constexpr auto operator<=(const uintwide_t& other) const -> bool { return (compare(other) <= static_cast<std::int_fast8_t>( 0)); }
    constexpr auto operator>=(const uintwide_t& other) const -> bool { return (compare(other) >= static_cast<std::int_fast8_t>( 0)); }

    // Helper functions for supporting std::numeric_limits<>.
    static constexpr auto limits_helper_max(bool is_signed) -> uintwide_t
    {
      return
      (!is_signed)
        ? from_rep
          (
            representation_type
            (
              number_of_limbs, (std::numeric_limits<limb_type>::max)()
            )
          )
        : from_rep
          (
            representation_type
            (
              number_of_limbs, (std::numeric_limits<limb_type>::max)()
            )
          ) ^ (uintwide_t(1U) << (my_width2 - 1))
        ;
    }

    static constexpr auto limits_helper_min(bool is_signed) -> uintwide_t
    {
      return
      (!is_signed)
        ? from_rep
          (
            representation_type
            (
              number_of_limbs, static_cast<limb_type>(0U)
            )
          )
        : from_rep
          (
            representation_type
            (
              number_of_limbs, static_cast<limb_type>(0U)
            )
          ) | (uintwide_t(1U) << (my_width2 - 1))
        ;
    }

    static constexpr auto limits_helper_min() -> uintwide_t
    {
      return uintwide_t(representation_type(number_of_limbs, static_cast<limb_type>(0U)));
    }

    static constexpr auto limits_helper_lowest(bool is_signed) -> uintwide_t
    {
      return
      (!is_signed)
        ? from_rep
          (
            representation_type
            (
              number_of_limbs, static_cast<limb_type>(0U)
            )
          )
        : from_rep
          (
            representation_type
            (
              number_of_limbs, static_cast<limb_type>(0U)
            )
          ) | (uintwide_t(1U) << (my_width2 - 1))
        ;
    }

    // Define the maximum buffer sizes for extracting
    // octal, decimal and hexadecimal string representations.
    static constexpr auto wr_string_max_buffer_size_oct =
      static_cast<size_t>
      (
        (
            8U
          + (((my_width2 % 3U) != 0U) ? 1U : 0U)
          +   (my_width2 / 3U)
        )
      );

    static constexpr auto wr_string_max_buffer_size_hex =
      static_cast<size_t>
      (
        (
            8U
          + (((my_width2 % 4U) != 0U) ? 1U : 0U)
          +   (my_width2 / 4U)
        )
      );

    static constexpr auto wr_string_max_buffer_size_dec =
      static_cast<size_t>
      (
        (
            10U
          + static_cast<size_t>((static_cast<std::uintmax_t>(my_width2) * UINTMAX_C(301)) / UINTMAX_C(1000))
        )
      );

    // Write string function.
    WIDE_INTEGER_CONSTEXPR auto wr_string(      char*              str_result, // NOLINT(readability-function-cognitive-complexity)
                                          const std::uint_fast8_t  base_rep     = 0x10U,
                                          const bool               show_base    = true,
                                          const bool               show_pos     = false,
                                          const bool               is_uppercase = true,
                                                unsigned_fast_type field_width  = 0U,
                                          const char               fill_char    = static_cast<char>('0')) const -> bool
    {
      bool wr_string_is_ok = true;

      if(base_rep == UINT8_C(8))
      {
        uintwide_t t(*this);

        const auto mask = static_cast<limb_type>(static_cast<std::uint8_t>(0x7U));

        using string_storage_oct_type =
          typename std::conditional
            <my_width2 <= static_cast<size_t>(UINT32_C(2048)),
             detail::fixed_static_array <char,
                                         wr_string_max_buffer_size_oct>,
             detail::fixed_dynamic_array<char,
                                         wr_string_max_buffer_size_oct,
                                         typename std::allocator_traits<typename std::conditional<std::is_same<AllocatorType, void>::value,
                                                                                                  std::allocator<void>,
                                                                                                  AllocatorType>::type>::template rebind_alloc<limb_type>>
            >::type;

        string_storage_oct_type str_temp;

        auto pos = static_cast<unsigned_fast_type>(str_temp.size() - 1U);

        if(t.is_zero())
        {
          --pos;

          str_temp[static_cast<typename string_storage_oct_type::size_type>(pos)] = static_cast<char>('0');
        }
        else
        {
          if(!is_neg(t))
          {
            while(!t.is_zero())
            {
              auto c = static_cast<char>(*t.values.cbegin() & mask);

              if(c <= static_cast<char>(INT8_C(8))) { c = static_cast<char>(c + static_cast<char>(INT8_C(0x30))); }

              --pos;

              str_temp[static_cast<typename string_storage_oct_type::size_type>(pos)] = c;

              t >>= 3;
            }
          }
          else
          {
            uintwide_t<my_width2, limb_type, AllocatorType, false> tu(t);

            while(!tu.is_zero()) // NOLINT(altera-id-dependent-backward-branch)
            {
              auto c = static_cast<char>(*tu.values.cbegin() & mask);

              if(c <= static_cast<char>(INT8_C(8))) { c = static_cast<char>(c + static_cast<char>(INT8_C(0x30))); }

              --pos;

              str_temp[static_cast<typename string_storage_oct_type::size_type>(pos)] = c;

              tu >>= 3;
            }
          }
        }

        if(show_base)
        {
          --pos;

          str_temp[static_cast<typename string_storage_oct_type::size_type>(pos)] = static_cast<char>('0');
        }

        if(show_pos)
        {
          --pos;

          str_temp[static_cast<typename string_storage_oct_type::size_type>(pos)] = static_cast<char>('+');
        }

        if(field_width != 0U)
        {
          field_width = (std::min)(field_width, static_cast<unsigned_fast_type>(str_temp.size() - 1U));

          while(static_cast<signed_fast_type>(pos) > static_cast<signed_fast_type>((str_temp.size() - 1U) - field_width)) // NOLINT(altera-id-dependent-backward-branch)
          {
            --pos;

            str_temp[static_cast<typename string_storage_oct_type::size_type>(pos)] = fill_char;
          }
        }

        str_temp[static_cast<typename string_storage_oct_type::size_type>(str_temp.size() - 1U)] = static_cast<char>('\0');

        detail::strcpy_unsafe(str_result, str_temp.data() + pos);
      }
      else if(base_rep == UINT8_C(10))
      {
        uintwide_t t(*this);

        const bool str_has_neg_sign = is_neg(t);

        if(str_has_neg_sign)
        {
          t.negate();
        }

        using string_storage_dec_type =
          typename std::conditional
            <my_width2 <= static_cast<size_t>(UINT32_C(2048)),
             detail::fixed_static_array <char,
                                         wr_string_max_buffer_size_dec>,
             detail::fixed_dynamic_array<char,
                                         wr_string_max_buffer_size_dec,
                                         typename std::allocator_traits<typename std::conditional<std::is_same<AllocatorType, void>::value,
                                                                                                  std::allocator<void>,
                                                                                                  AllocatorType>::type>::template rebind_alloc<limb_type>>
            >::type;

        string_storage_dec_type str_temp;

        auto pos = static_cast<unsigned_fast_type>(str_temp.size() - 1U);

        if(t.is_zero())
        {
          --pos;

          str_temp[static_cast<typename string_storage_dec_type::size_type>(pos)] = static_cast<char>('0');
        }
        else
        {
          while(!t.is_zero())
          {
            const uintwide_t tmp(t);

            t.eval_divide_by_single_limb(static_cast<limb_type>(UINT8_C(10)), 0U, nullptr);

            --pos;

            str_temp[static_cast<typename string_storage_dec_type::size_type>(pos)] =
              static_cast<char>
              (
                  static_cast<limb_type>
                  (
                    tmp - (uintwide_t(t).mul_by_limb(static_cast<limb_type>(UINT8_C(10))))
                  )
                + UINT8_C(0x30)
              );
          }
        }

        if(show_pos && (!str_has_neg_sign))
        {
          --pos;

          str_temp[static_cast<typename string_storage_dec_type::size_type>(pos)] = static_cast<char>('+');
        }
        else if(str_has_neg_sign)
        {
          --pos;

          str_temp[static_cast<typename string_storage_dec_type::size_type>(pos)] = static_cast<char>('-');
        }

        if(field_width != 0U)
        {
          field_width = (std::min)(field_width, static_cast<unsigned_fast_type>(str_temp.size() - 1U));

          while(static_cast<signed_fast_type>(pos) > static_cast<signed_fast_type>((str_temp.size() - 1U) - field_width)) // NOLINT(altera-id-dependent-backward-branch)
          {
            --pos;

            str_temp[static_cast<typename string_storage_dec_type::size_type>(pos)] = fill_char;
          }
        }

        str_temp[static_cast<typename string_storage_dec_type::size_type>(str_temp.size() - 1U)] = static_cast<char>('\0');

        detail::strcpy_unsafe(str_result, str_temp.data() + pos);
      }
      else if(base_rep == UINT8_C(16))
      {
        uintwide_t t(*this);

        const auto mask = static_cast<limb_type>(static_cast<std::uint8_t>(0xFU));

        using string_storage_hex_type =
          typename std::conditional
            <my_width2 <= static_cast<size_t>(UINT32_C(2048)),
             detail::fixed_static_array <char,
                                         wr_string_max_buffer_size_hex>,
             detail::fixed_dynamic_array<char,
                                         wr_string_max_buffer_size_hex,
                                         typename std::allocator_traits<typename std::conditional<std::is_same<AllocatorType, void>::value,
                                                                                                  std::allocator<void>,
                                                                                                  AllocatorType>::type>::template rebind_alloc<limb_type>>
            >::type;

        string_storage_hex_type str_temp;

        auto pos = static_cast<unsigned_fast_type>(str_temp.size() - 1U);

        if(t.is_zero())
        {
          --pos;

          str_temp[static_cast<typename string_storage_hex_type::size_type>(pos)] = static_cast<char>('0');
        }
        else
        {
          if(!is_neg(t))
          {
            while(!t.is_zero())
            {
              char c(*t.values.cbegin() & mask);

              if      (c <= static_cast<char>(INT8_C(  9)))                                           { c = static_cast<char>(c + static_cast<char>(INT8_C(0x30))); }
              else if((c >= static_cast<char>(INT8_C(0xA))) && (c <= static_cast<char>(INT8_C(0xF)))) { c = static_cast<char>(c + (is_uppercase ? static_cast<char>(INT8_C(55)) : static_cast<char>(INT8_C(87)))); }

              --pos;

              str_temp[static_cast<typename string_storage_hex_type::size_type>(pos)] = c;

              t >>= 4;
            }
          }
          else
          {
            uintwide_t<my_width2, limb_type, AllocatorType, false> tu(t);

            while(!tu.is_zero()) // NOLINT(altera-id-dependent-backward-branch)
            {
              char c(*tu.values.cbegin() & mask);

              if      (c <= static_cast<char>(INT8_C(  9)))                                           { c = static_cast<char>(c + static_cast<char>(INT8_C(0x30))); }
              else if((c >= static_cast<char>(INT8_C(0xA))) && (c <= static_cast<char>(INT8_C(0xF)))) { c = static_cast<char>(c + (is_uppercase ? static_cast<char>(INT8_C(55)) : static_cast<char>(INT8_C(87)))); }

              --pos;

              str_temp[static_cast<typename string_storage_hex_type::size_type>(pos)] = c;

              tu >>= 4;
            }
          }
        }

        if(show_base)
        {
          --pos;

          str_temp[static_cast<typename string_storage_hex_type::size_type>(pos)] = (is_uppercase ? static_cast<char>('X') : static_cast<char>('x'));

          --pos;

          str_temp[static_cast<typename string_storage_hex_type::size_type>(pos)] = static_cast<char>('0');
        }

        if(show_pos)
        {
          --pos;

          str_temp[static_cast<typename string_storage_hex_type::size_type>(pos)] = static_cast<char>('+');
        }

        if(field_width != 0U)
        {
          field_width = (std::min)(field_width, static_cast<unsigned_fast_type>(str_temp.size() - 1U));

          while(static_cast<signed_fast_type>(pos) > static_cast<signed_fast_type>((str_temp.size() - 1U) - field_width)) // NOLINT(altera-id-dependent-backward-branch)
          {
            --pos;

            str_temp[static_cast<typename string_storage_hex_type::size_type>(pos)] = fill_char;
          }
        }

        str_temp[static_cast<typename string_storage_hex_type::size_type>(str_temp.size() - 1U)] = static_cast<char>('\0');

        detail::strcpy_unsafe(str_result, str_temp.data() + pos);
      }
      else
      {
        wr_string_is_ok = false;
      }

      return wr_string_is_ok;
    }

    template<const bool RePhraseIsSigned = IsSigned,
             typename std::enable_if<(!RePhraseIsSigned)>::type const* = nullptr>
    WIDE_INTEGER_NODISCARD WIDE_INTEGER_CONSTEXPR auto compare(const uintwide_t<Width2, LimbType, AllocatorType, RePhraseIsSigned>& other) const -> std::int_fast8_t
    {
      return compare_ranges(values.data(),
                            other.values.data(),
                            uintwide_t<Width2, LimbType, AllocatorType, RePhraseIsSigned>::number_of_limbs);
    }

    template<const bool RePhraseIsSigned = IsSigned,
             typename std::enable_if<(RePhraseIsSigned)>::type const* = nullptr>
    WIDE_INTEGER_NODISCARD WIDE_INTEGER_CONSTEXPR auto compare(const uintwide_t<Width2, LimbType, AllocatorType, RePhraseIsSigned>& other) const -> std::int_fast8_t
    {
      const bool other_is_neg = is_neg(other);

      return
      is_neg(*this)
        ? (other_is_neg ? compare_ranges(values.data(), other.values.data(), uintwide_t<Width2, LimbType, AllocatorType, RePhraseIsSigned>::number_of_limbs)
                        : INT8_C(-1))
        : (other_is_neg ? INT8_C(1)
                        : compare_ranges(values.data(), other.values.data(), uintwide_t<Width2, LimbType, AllocatorType, RePhraseIsSigned>::number_of_limbs))
      ;
    }

    WIDE_INTEGER_CONSTEXPR void negate()
    {
      bitwise_not();

      preincrement();
    }

    WIDE_INTEGER_CONSTEXPR void eval_divide_by_single_limb(const limb_type          short_denominator,
                                                           const unsigned_fast_type u_offset,
                                                                 uintwide_t*        remainder)
    {
      // The denominator has one single limb.
      // Use a one-dimensional division algorithm.

      auto long_numerator = static_cast<double_limb_type>(0U);

      auto hi_part = static_cast<limb_type>(0U);

      for(auto i = static_cast<signed_fast_type>(static_cast<unsigned_fast_type>(number_of_limbs - 1U) - u_offset); static_cast<signed_fast_type>(i) >= 0; --i) // NOLINT(altera-id-dependent-backward-branch)
      {
        long_numerator =
          static_cast<double_limb_type>
          (
             static_cast<double_limb_type>(*(values.cbegin() + static_cast<size_t>(i)))
           + static_cast<double_limb_type>(static_cast<double_limb_type>(long_numerator - static_cast<double_limb_type>(static_cast<double_limb_type>(short_denominator) * hi_part)) << static_cast<unsigned>(std::numeric_limits<limb_type>::digits))
          );

        *(values.begin() + static_cast<size_t>(i)) =
          detail::make_lo<limb_type>(static_cast<double_limb_type>(long_numerator / short_denominator));

        hi_part = *(values.cbegin() + static_cast<size_t>(i));
      }

      if(remainder != nullptr)
      {
        long_numerator =
          static_cast<double_limb_type>
          (
             static_cast<double_limb_type>(*values.cbegin())
           + static_cast<double_limb_type>(static_cast<double_limb_type>(long_numerator - static_cast<double_limb_type>(static_cast<double_limb_type>(short_denominator) * hi_part)) << static_cast<unsigned>(std::numeric_limits<limb_type>::digits))
          );

        *remainder = static_cast<limb_type>(long_numerator >> static_cast<unsigned>(std::numeric_limits<limb_type>::digits));
      }
    }

    WIDE_INTEGER_NODISCARD WIDE_INTEGER_CONSTEXPR auto is_zero() const -> bool
    {
      auto it = values.cbegin(); // NOLINT(llvm-qualified-auto,readability-qualified-auto)

      while((it != values.cend()) && (*it == static_cast<limb_type>(0U))) // NOLINT(altera-id-dependent-backward-branch)
      {
        ++it;
      }

      return (it == values.cend());
    }

    template<const bool RePhraseIsSigned = IsSigned,
             typename std::enable_if<(!RePhraseIsSigned)>::type const* = nullptr>
    static constexpr auto is_neg(uintwide_t<Width2, LimbType, AllocatorType, RePhraseIsSigned>) -> bool // NOLINT(hicpp-named-parameter,readability-named-parameter)
    {
      return false;
    }

    template<const bool RePhraseIsSigned = IsSigned,
             typename std::enable_if<(RePhraseIsSigned)>::type const* = nullptr>
    static constexpr auto is_neg(uintwide_t<Width2, LimbType, AllocatorType, RePhraseIsSigned> a) -> bool
    {
      return (static_cast<std::uint_fast8_t>(static_cast<std::uint_fast8_t>(a.values.back() >> static_cast<size_t>(std::numeric_limits<typename uintwide_t<Width2, LimbType, AllocatorType, RePhraseIsSigned>::limb_type>::digits - 1)) & 1U) != 0U);
    }

  private:
    representation_type values { };  // NOLINT(readability-identifier-naming)

    static constexpr auto from_rep(const representation_type& other_rep) -> uintwide_t
    {
      // Factory-like creator from the internal data representation.

      return [&other_rep]() -> uintwide_t
      {
        uintwide_t a;

        a.values = other_rep;

        return a;
      }();
    }

    template<typename InputIteratorLeftType,
             typename InputIteratorRightType>
    static WIDE_INTEGER_CONSTEXPR auto compare_ranges(      InputIteratorLeftType  a,
                                                            InputIteratorRightType b,
                                                      const unsigned_fast_type     count) -> std::int_fast8_t
    {
      std::int_fast8_t n_return = 0;

      std::reverse_iterator<InputIteratorLeftType>  pa(a + count);
      std::reverse_iterator<InputIteratorRightType> pb(b + count);

      for( ; pa != std::reverse_iterator<InputIteratorLeftType>(a); ++pa, ++pb) // NOLINT(altera-id-dependent-backward-branch)
      {
        using value_left_type =
          typename std::iterator_traits<InputIteratorLeftType>::value_type;

        if(*pa > static_cast<value_left_type>(*pb)) { n_return =  1; break; }
        if(*pa < static_cast<value_left_type>(*pb)) { n_return = -1; break; }
      }

      return n_return;
    }

    template<typename UnknownBuiltInIntegralType>
    struct digits_ratio
    {
      using local_unknown_integral_type  = UnknownBuiltInIntegralType;

      using local_unsigned_conversion_type =
        typename detail::uint_type_helper<
          std::numeric_limits<local_unknown_integral_type>::is_signed
            ? static_cast<size_t>(std::numeric_limits<local_unknown_integral_type>::digits + 1)
            : static_cast<size_t>(std::numeric_limits<local_unknown_integral_type>::digits + 0)>::exact_unsigned_type;

      static constexpr unsigned_fast_type value = 
        static_cast<unsigned_fast_type>(  std::numeric_limits<local_unsigned_conversion_type>::digits
                                        / std::numeric_limits<limb_type>::digits);

      template<typename InputIteratorLeft>
      static WIDE_INTEGER_CONSTEXPR auto extract(InputIteratorLeft  p_limb, unsigned_fast_type limb_count) -> local_unknown_integral_type
      {
        using local_limb_type      = typename std::iterator_traits<InputIteratorLeft>::value_type;
        using left_difference_type = typename std::iterator_traits<InputIteratorLeft>::difference_type;

        auto u = static_cast<local_unsigned_conversion_type>(0U);

        for(auto i = static_cast<unsigned_fast_type>(0U); i < limb_count; ++i)
        {
          u =
            static_cast<local_unsigned_conversion_type>
            (
                u
              | static_cast<local_unsigned_conversion_type>(static_cast<local_unsigned_conversion_type>(*(p_limb + static_cast<left_difference_type>(i))) << static_cast<unsigned>(std::numeric_limits<local_limb_type>::digits * static_cast<int>(i)))
            );
        }

        return static_cast<local_unknown_integral_type>(u);
      }
    };

    // Implement a function that extracts any built-in signed or unsigned integral type.
    template<typename UnknownBuiltInIntegralType,
             typename = typename std::enable_if<std::is_integral<UnknownBuiltInIntegralType>::value>::type>
    WIDE_INTEGER_NODISCARD WIDE_INTEGER_CONSTEXPR auto extract_builtin_integral_type() const -> UnknownBuiltInIntegralType
    {
      using local_unknown_integral_type = UnknownBuiltInIntegralType;
      using digits_ratio_type           = digits_ratio<local_unknown_integral_type>;

      const unsigned_fast_type ilim = (std::min)(static_cast<unsigned_fast_type>(digits_ratio_type::value),
                                                 static_cast<unsigned_fast_type>(values.size()));

      // Handle cases for which the input parameter is less wide
      // or equally as wide as the limb width or wider than the limb width.
      return ((digits_ratio_type::value < 2U)
               ? static_cast<local_unknown_integral_type>(*values.cbegin())
               : digits_ratio_type::extract(values.data(), ilim));
    }

    #if !defined(WIDE_INTEGER_DISABLE_FLOAT_INTEROP)
    // Implement a function that extracts any built-in floating-point type.
    template<typename FloatingPointType,
             typename = typename std::enable_if<std::is_floating_point<FloatingPointType>::value>::type>
    WIDE_INTEGER_NODISCARD WIDE_INTEGER_CONSTEXPR auto extract_builtin_floating_point_type() const -> FloatingPointType
    {
      using local_unsigned_wide_integer_type = uintwide_t<Width2, limb_type, AllocatorType, false>;
      using local_builtin_float_type         = FloatingPointType;

      const bool u_is_neg = is_neg(*this);

      const local_unsigned_wide_integer_type u((!u_is_neg) ? *this : -*this);

      const auto my_msb = static_cast<size_t>(msb(u));
      const auto ilim   = static_cast<size_t>
                          (
                             static_cast<size_t>(  static_cast<size_t>(my_msb + 1U) / static_cast<size_t>(std::numeric_limits<limb_type>::digits))
                           + static_cast<size_t>(((static_cast<size_t>(my_msb + 1U) % static_cast<size_t>(std::numeric_limits<limb_type>::digits)) != 0U) ? static_cast<size_t>(1U) : static_cast<size_t>(0U))
                          );

      auto a = static_cast<local_builtin_float_type>(0.0F);

      constexpr long double one_ldbl(1.0L);

      long double ldexp_runner(one_ldbl);

      for(auto i = static_cast<size_t>(0U); i < ilim; ++i) // NOLINT(altera-id-dependent-backward-branch)
      {
        auto ld      = static_cast<long double>(0.0L);
        auto lm_mask = static_cast<limb_type>(1ULL);

        for(auto j = static_cast<size_t>(0U); j < static_cast<size_t>(std::numeric_limits<limb_type>::digits); ++j)
        {
          if(static_cast<limb_type>(*(u.values.cbegin() + static_cast<size_t>(i)) & lm_mask) != static_cast<limb_type>(0U))
          {
            ld = static_cast<long double>(ld + ldexp_runner);
          }

          constexpr long double two_ldbl(2.0L);

          lm_mask      = static_cast<limb_type>  (lm_mask << 1U);
          ldexp_runner = static_cast<long double>(ldexp_runner * two_ldbl);
        }

        a += static_cast<local_builtin_float_type>(ld);
      }

      return static_cast<local_builtin_float_type>((!u_is_neg) ? a : -a);
    }
    #endif

    template<const size_t OtherWidth2>
    static WIDE_INTEGER_CONSTEXPR void eval_mul_unary(      uintwide_t<OtherWidth2, LimbType, AllocatorType, IsSigned>& u,
                                                      const uintwide_t<OtherWidth2, LimbType, AllocatorType, IsSigned>& v,
                                                      typename std::enable_if<((OtherWidth2 / std::numeric_limits<LimbType>::digits) < number_of_limbs_karatsuba_threshold)>::type* p_nullparam = nullptr)
    {
      static_cast<void>(p_nullparam == nullptr);

      // Unary multiplication function using schoolbook multiplication,
      // but we only need to retain the low half of the n*n algorithm.
      // In other words, this is an n*n->n bit multiplication.

      constexpr size_t local_number_of_limbs =
        uintwide_t<OtherWidth2, LimbType, AllocatorType, IsSigned>::number_of_limbs;

      representation_type result { };

      eval_multiply_n_by_n_to_lo_part(result.data(),
                                      u.values.data(),
                                      v.values.data(),
                                      local_number_of_limbs);

      std::copy(result.cbegin(),
                result.cbegin() + local_number_of_limbs,
                u.values.begin());
    }

    template<const size_t OtherWidth2>
    static WIDE_INTEGER_CONSTEXPR void eval_mul_unary(      uintwide_t<OtherWidth2, LimbType, AllocatorType, IsSigned>& u,
                                                      const uintwide_t<OtherWidth2, LimbType, AllocatorType, IsSigned>& v,
                                                      typename std::enable_if<((OtherWidth2 / std::numeric_limits<LimbType>::digits) >= number_of_limbs_karatsuba_threshold)>::type* p_nullparam = nullptr)
    {
      static_cast<void>(p_nullparam == nullptr);

      // Unary multiplication function using Karatsuba multiplication.

      constexpr size_t local_number_of_limbs =
        uintwide_t<OtherWidth2, LimbType, AllocatorType, IsSigned>::number_of_limbs;

      // TBD: Can use specialized allocator or memory pool for these arrays.
      // Good examples for this (both threaded as well as non-threaded)
      // can be found in the wide_decimal project.
      using result_array_type =
        typename std::conditional<std::is_same<AllocatorType, void>::value,
                                  detail::fixed_static_array <limb_type, number_of_limbs * 2U>,
                                  detail::fixed_dynamic_array<limb_type,
                                                              number_of_limbs * 2U,
                                                              typename std::allocator_traits<typename std::conditional<std::is_same<AllocatorType, void>::value,
                                                                                                                       std::allocator<void>,
                                                                                                                       AllocatorType>::type>::template rebind_alloc<limb_type>>>::type;

      using storage_array_type =
        typename std::conditional<std::is_same<AllocatorType, void>::value,
                                  detail::fixed_static_array <limb_type, number_of_limbs * 4U>,
                                  detail::fixed_dynamic_array<limb_type,
                                                              number_of_limbs * 4U,
                                                              typename std::allocator_traits<typename std::conditional<std::is_same<AllocatorType, void>::value,
                                                                                                                       std::allocator<void>,
                                                                                                                       AllocatorType>::type>::template rebind_alloc<limb_type>>>::type;

      result_array_type  result;
      storage_array_type t;

      eval_multiply_kara_n_by_n_to_2n(result.data(),
                                      u.values.data(),
                                      v.values.data(),
                                      local_number_of_limbs,
                                      t.data());

      std::copy(result.cbegin(),
                result.cbegin() + local_number_of_limbs,
                u.values.begin());
    }

    template<typename ResultIterator,
             typename InputIteratorLeft,
             typename InputIteratorRight>
    static WIDE_INTEGER_CONSTEXPR auto eval_add_n(      ResultIterator     r,
                                                        InputIteratorLeft  u,
                                                        InputIteratorRight v,
                                                  const unsigned_fast_type count,
                                                  const limb_type          carry_in = static_cast<limb_type>(0U)) -> limb_type
    {
      auto carry_out = static_cast<std::uint_fast8_t>(carry_in);

      static_assert
      (
           (std::numeric_limits<typename std::iterator_traits<ResultIterator>::value_type>::digits == std::numeric_limits<typename std::iterator_traits<InputIteratorLeft>::value_type>::digits)
        && (std::numeric_limits<typename std::iterator_traits<ResultIterator>::value_type>::digits == std::numeric_limits<typename std::iterator_traits<InputIteratorRight>::value_type>::digits),
        "Error: Internals require same widths for left-right-result limb_types at the moment"
      );

      using local_limb_type = typename std::iterator_traits<ResultIterator>::value_type;

      using local_double_limb_type =
        typename detail::uint_type_helper<static_cast<size_t>(std::numeric_limits<local_limb_type>::digits * 2)>::exact_unsigned_type;

      using result_difference_type = typename std::iterator_traits<ResultIterator>::difference_type;
      using left_difference_type   = typename std::iterator_traits<InputIteratorLeft>::difference_type;
      using right_difference_type  = typename std::iterator_traits<InputIteratorRight>::difference_type;

      for(auto i = static_cast<unsigned_fast_type>(0U); i < count; ++i)
      {
        const auto uv_as_ularge =
          static_cast<local_double_limb_type>(static_cast<local_double_limb_type>(static_cast<local_double_limb_type>(*(u + static_cast<left_difference_type>(i))) + *(v + static_cast<right_difference_type>(i))) + carry_out);

        carry_out = static_cast<std::uint_fast8_t>(detail::make_hi<local_limb_type>(uv_as_ularge));

        *(r + static_cast<result_difference_type>(i)) = static_cast<local_limb_type>(uv_as_ularge);
      }

      return static_cast<limb_type>(carry_out);
    }

    template<typename ResultIterator,
             typename InputIteratorLeft,
             typename InputIteratorRight>
    static WIDE_INTEGER_CONSTEXPR auto eval_subtract_n(      ResultIterator     r,
                                                             InputIteratorLeft  u,
                                                             InputIteratorRight v,
                                                       const unsigned_fast_type count,
                                                       const bool               has_borrow_in = false) -> bool
    {
      std::uint_fast8_t has_borrow_out = (has_borrow_in ? 1U : 0U);

      static_assert
      (
           (std::numeric_limits<typename std::iterator_traits<ResultIterator>::value_type>::digits == std::numeric_limits<typename std::iterator_traits<InputIteratorLeft>::value_type>::digits)
        && (std::numeric_limits<typename std::iterator_traits<ResultIterator>::value_type>::digits == std::numeric_limits<typename std::iterator_traits<InputIteratorRight>::value_type>::digits),
        "Error: Internals require same widths for left-right-result limb_types at the moment"
      );

      using local_limb_type = typename std::iterator_traits<ResultIterator>::value_type;

      using local_double_limb_type =
        typename detail::uint_type_helper<static_cast<size_t>(std::numeric_limits<local_limb_type>::digits * 2)>::exact_unsigned_type;

      using result_difference_type = typename std::iterator_traits<ResultIterator>::difference_type;
      using left_difference_type   = typename std::iterator_traits<InputIteratorLeft>::difference_type;
      using right_difference_type  = typename std::iterator_traits<InputIteratorRight>::difference_type;

      for(auto i = static_cast<unsigned_fast_type>(0U); i < count; ++i)
      {
        const auto uv_as_ularge = static_cast<local_double_limb_type>(static_cast<local_double_limb_type>(static_cast<local_double_limb_type>(*(u + static_cast<left_difference_type>(i))) - *(v + static_cast<right_difference_type>(i))) - has_borrow_out);

        has_borrow_out = (detail::make_hi<local_limb_type>(uv_as_ularge) != static_cast<local_limb_type>(0U)) ? 1U : 0U;

        *(r + static_cast<result_difference_type>(i)) = static_cast<local_limb_type>(uv_as_ularge);
      }

      return (has_borrow_out != 0U);
    }

    template<typename ResultIterator,
             typename InputIteratorLeft,
             typename InputIteratorRight,
             const size_t RePhraseWidth2 = Width2,
             typename std::enable_if<(uintwide_t<RePhraseWidth2, LimbType, AllocatorType, IsSigned>::number_of_limbs == 4U)>::type const* = nullptr>
    static WIDE_INTEGER_CONSTEXPR void eval_multiply_n_by_n_to_lo_part(      ResultIterator     r,
                                                                             InputIteratorLeft  a,
                                                                             InputIteratorRight b,
                                                                       const unsigned_fast_type count)
    {
      static_cast<void>(count);

      static_assert
      (
           (std::numeric_limits<typename std::iterator_traits<ResultIterator>::value_type>::digits == std::numeric_limits<typename std::iterator_traits<InputIteratorLeft>::value_type>::digits)
        && (std::numeric_limits<typename std::iterator_traits<ResultIterator>::value_type>::digits == std::numeric_limits<typename std::iterator_traits<InputIteratorRight>::value_type>::digits),
        "Error: Internals require same widths for left-right-result limb_types at the moment"
      );

      using local_limb_type = typename std::iterator_traits<ResultIterator>::value_type;

      using local_double_limb_type =
        typename detail::uint_type_helper<static_cast<size_t>(std::numeric_limits<local_limb_type>::digits * 2)>::exact_unsigned_type;

      using result_difference_type = typename std::iterator_traits<ResultIterator>::difference_type;
      using left_difference_type   = typename std::iterator_traits<InputIteratorLeft>::difference_type;
      using right_difference_type  = typename std::iterator_traits<InputIteratorRight>::difference_type;
      using result_value_type      = typename std::iterator_traits<ResultIterator>::value_type;

      // The algorithm has been derived from the polynomial multiplication.
      // After the multiplication terms of equal order are grouped
      // together and retained up to order(3). The carries from the
      // multiplications are included when adding up the terms.
      // The results of the intermediate multiplications are stored
      // in local variables in memory.

      //   Column[CoefficientList[Expand[(a0 + a1 x + a2 x^2 + a3 x^3) (b0 + b1 x + b2 x^2 + b3 x^3)], x]]
      //   a0b0
      //   a1b0 + a0b1
      //   a2b0 + a1b1 + a0b2
      //   a3b0 + a2b1 + a1b2 + a0b3

      // See also Wolfram Alpha at:
      // https://www.wolframalpha.com/input/?i=Column%5BCoefficientList%5B+++Expand%5B%28a0+%2B+a1+x+%2B+a2+x%5E2+%2B+a3+x%5E3%29+%28b0+%2B+b1+x+%2B+b2+x%5E2+%2B+b3+x%5E3%29%5D%2C++++x%5D%5D
      // ... and take the upper half of the pyramid.

      // Performance improvement:
      //   (old) kops_per_sec: 33173.50
      //   (new) kops_per_sec: 95069.43

      local_double_limb_type r1;
      local_double_limb_type r2;

      const auto a0b0 = static_cast<local_double_limb_type>(*(a + static_cast<left_difference_type>(0)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(0))));
      const auto a0b1 = static_cast<local_double_limb_type>(*(a + static_cast<left_difference_type>(0)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(1))));
      const auto a1b0 = static_cast<local_double_limb_type>(*(a + static_cast<left_difference_type>(1)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(0))));
      const auto a1b1 = static_cast<local_double_limb_type>(*(a + static_cast<left_difference_type>(1)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(1))));

      // One special case is considered, the case of multiplication
      // of the form BITS/2 * BITS/2 = BITS. In this case, the algorithm
      // can be significantly simplified by using only the 'lower-halves'
      // of the data.
      if(    (*(a + static_cast<left_difference_type>(2)) == 0U) && (*(b + static_cast<right_difference_type>(2)) == 0U)
          && (*(a + static_cast<left_difference_type>(3)) == 0U) && (*(b + static_cast<right_difference_type>(3)) == 0U))
      {
        r1    = static_cast<local_double_limb_type>
                (
                  static_cast<local_double_limb_type>
                  (
                    detail::make_hi<local_limb_type>(a0b0)
                  )
                  + detail::make_lo<local_limb_type>(a1b0)
                  + detail::make_lo<local_limb_type>(a0b1)
                )
                ;
        r2    = static_cast<local_double_limb_type>
                (
                  static_cast<local_double_limb_type>
                  (
                    detail::make_hi<local_limb_type>(r1)
                  )
                  + detail::make_lo<local_limb_type>(a1b1)
                  + detail::make_hi<local_limb_type>(a0b1)
                  + detail::make_hi<local_limb_type>(a1b0)
                )
                ;
        *(r + static_cast<result_difference_type>(3))
              = static_cast<result_value_type>
                (
                    detail::make_hi<local_limb_type>(r2)
                  + detail::make_hi<local_limb_type>(a1b1)
                )
                ;
      }
      else
      {
        const auto a0b2 = static_cast<local_double_limb_type>(*(a + static_cast<left_difference_type>(0)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(2))));
        const auto a2b0 = static_cast<local_double_limb_type>(*(a + static_cast<left_difference_type>(2)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(0))));

        r1    = static_cast<local_double_limb_type>
                (
                  static_cast<local_double_limb_type>
                  (
                    detail::make_hi<local_limb_type>(a0b0)
                  )
                  + detail::make_lo<local_limb_type>(a1b0)
                  + detail::make_lo<local_limb_type>(a0b1)
                )
                ;
        r2    = static_cast<local_double_limb_type>
                (
                  static_cast<local_double_limb_type>
                  (
                    detail::make_hi<local_limb_type>(r1)
                  )
                  + detail::make_lo<local_limb_type>(a2b0)
                  + detail::make_lo<local_limb_type>(a1b1)
                  + detail::make_lo<local_limb_type>(a0b2)
                  + detail::make_hi<local_limb_type>(a1b0)
                  + detail::make_hi<local_limb_type>(a0b1)
                )
                ;
        *(r + static_cast<result_difference_type>(3))
              = static_cast<result_value_type>
                (
                    detail::make_hi<local_limb_type>(r2)
                  + static_cast<local_limb_type>    (*(a + static_cast<left_difference_type>(3)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(0))))
                  + static_cast<local_limb_type>    (*(a + static_cast<left_difference_type>(2)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(1))))
                  + static_cast<local_limb_type>    (*(a + static_cast<left_difference_type>(1)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(2))))
                  + static_cast<local_limb_type>    (*(a + static_cast<left_difference_type>(0)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(3))))
                  + detail::make_hi<local_limb_type>(a2b0)
                  + detail::make_hi<local_limb_type>(a1b1)
                  + detail::make_hi<local_limb_type>(a0b2)
                )
                ;
      }

      *(r + static_cast<result_difference_type>(0)) = static_cast<local_limb_type>(a0b0);
      *(r + static_cast<result_difference_type>(1)) = static_cast<local_limb_type>(r1);
      *(r + static_cast<result_difference_type>(2)) = static_cast<local_limb_type>(r2);
    }

    #if defined(WIDE_INTEGER_HAS_MUL_8_BY_8_UNROLL)
    template<typename ResultIterator,
             typename InputIteratorLeft,
             typename InputIteratorRight,
             const size_t RePhraseWidth2 = Width2,
             typename std::enable_if<(uintwide_t<RePhraseWidth2, LimbType, AllocatorType, IsSigned>::number_of_limbs == static_cast<size_t>(UINT32_C(8)))>::type const* = nullptr>
    static WIDE_INTEGER_CONSTEXPR void eval_multiply_n_by_n_to_lo_part(      ResultIterator     r,
                                                                             InputIteratorLeft  a,
                                                                             InputIteratorRight b,
                                                                       const unsigned_fast_type count)
    {
      static_cast<void>(count);

      static_assert
      (
           (std::numeric_limits<typename std::iterator_traits<ResultIterator>::value_type>::digits == std::numeric_limits<typename std::iterator_traits<InputIteratorLeft>::value_type>::digits)
        && (std::numeric_limits<typename std::iterator_traits<ResultIterator>::value_type>::digits == std::numeric_limits<typename std::iterator_traits<InputIteratorRight>::value_type>::digits),
        "Error: Internals require same widths for left-right-result limb_types at the moment"
      );

      using local_limb_type = typename std::iterator_traits<ResultIterator>::value_type;

      using local_double_limb_type =
        typename detail::uint_type_helper<static_cast<size_t>(std::numeric_limits<local_limb_type>::digits * 2)>::exact_unsigned_type;

      using result_difference_type = typename std::iterator_traits<ResultIterator>::difference_type;
      using left_difference_type   = typename std::iterator_traits<InputIteratorLeft>::difference_type;
      using right_difference_type  = typename std::iterator_traits<InputIteratorRight>::difference_type;

      // The algorithm has been derived from the polynomial multiplication.
      // After the multiplication terms of equal order are grouped
      // together and retained up to order(3). The carries from the
      // multiplications are included when adding up the terms.
      // The results of the intermediate multiplications are stored
      // in local variables in memory.

      //   Column[CoefficientList[Expand[(a0 + a1 x + a2 x^2 + a3 x^3 + a4 x^4 + a5 x^5 + a6 x^6 + a7 x^7) (b0 + b1 x + b2 x^2 + b3 x^3 + b4 x^4 + b5 x^5 + b6 x^6 + b7 x^7)], x]]
      //   a0b0
      //   a1b0 + a0b1
      //   a2b0 + a1b1 + a0b2
      //   a3b0 + a2b1 + a1b2 + a0b3
      //   a4b0 + a3b1 + a2b2 + a1b3 + a0b4
      //   a5b0 + a4b1 + a3b2 + a2b3 + a1b4 + a0b5
      //   a6b0 + a5b1 + a4b2 + a3b3 + a2b4 + a1b5 + a0b6
      //   a7b0 + a6b1 + a5b2 + a4b3 + a3b4 + a2b5 + a1b6 + a0b7

      // See also Wolfram Alpha at:
      // https://www.wolframalpha.com/input/?i=Column%5BCoefficientList%5B+++Expand%5B%28a0+%2B+a1+x+%2B+a2+x%5E2+%2B+a3+x%5E3%29+%28b0+%2B+b1+x+%2B+b2+x%5E2+%2B+b3+x%5E3%29%5D%2C++++x%5D%5D
      // ... and take the upper half of the pyramid.

      const local_double_limb_type a0b0 = *(a + static_cast<left_difference_type>(0)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(0)));

      const local_double_limb_type a1b0 = *(a + static_cast<left_difference_type>(1)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(0)));
      const local_double_limb_type a0b1 = *(a + static_cast<left_difference_type>(0)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(1)));

      const local_double_limb_type a2b0 = *(a + static_cast<left_difference_type>(2)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(0)));
      const local_double_limb_type a1b1 = *(a + static_cast<left_difference_type>(1)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(1)));
      const local_double_limb_type a0b2 = *(a + static_cast<left_difference_type>(0)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(2)));

      const local_double_limb_type a3b0 = *(a + static_cast<left_difference_type>(3)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(0)));
      const local_double_limb_type a2b1 = *(a + static_cast<left_difference_type>(2)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(1)));
      const local_double_limb_type a1b2 = *(a + static_cast<left_difference_type>(1)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(2)));
      const local_double_limb_type a0b3 = *(a + static_cast<left_difference_type>(0)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(3)));

      const local_double_limb_type a3b1 = *(a + static_cast<left_difference_type>(3)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(1)));
      const local_double_limb_type a2b2 = *(a + static_cast<left_difference_type>(2)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(2)));
      const local_double_limb_type a1b3 = *(a + static_cast<left_difference_type>(1)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(3)));

      const local_double_limb_type a3b2 = *(a + static_cast<left_difference_type>(3)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(2)));
      const local_double_limb_type a2b3 = *(a + static_cast<left_difference_type>(2)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(3)));

      const local_double_limb_type a3b3 = *(a + static_cast<left_difference_type>(3)) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(3)));

            local_double_limb_type rd1;
            local_double_limb_type rd2;
            local_double_limb_type rd3;
            local_double_limb_type rd4;
            local_double_limb_type rd5;
            local_double_limb_type rd6;

      // One special case is considered, the case of multiplication
      // of the form BITS/2 * BITS/2 = BITS. In this case, the algorithm
      // can be significantly simplified by using only the 'lower-halves'
      // of the data.
      if(    (*(a + static_cast<left_difference_type>(INT32_C(7))) == 0U) && (*(b + static_cast<right_difference_type>(INT32_C(7))) == 0U)
          && (*(a + static_cast<left_difference_type>(INT32_C(6))) == 0U) && (*(b + static_cast<right_difference_type>(INT32_C(6))) == 0U)
          && (*(a + static_cast<left_difference_type>(INT32_C(5))) == 0U) && (*(b + static_cast<right_difference_type>(INT32_C(5))) == 0U)
          && (*(a + static_cast<left_difference_type>(INT32_C(4))) == 0U) && (*(b + static_cast<right_difference_type>(INT32_C(4))) == 0U))
      {
        rd1   = static_cast<local_double_limb_type>
                (
                  detail::make_hi<local_limb_type>(a0b0)
                )
                + detail::make_lo<local_limb_type>(a1b0)
                + detail::make_lo<local_limb_type>(a0b1)
                ;

        rd2   = static_cast<local_double_limb_type>
                (
                  detail::make_hi<local_limb_type>(rd1)
                )
                + detail::make_lo<local_limb_type>(a2b0)
                + detail::make_lo<local_limb_type>(a1b1)
                + detail::make_lo<local_limb_type>(a0b2)
                + detail::make_hi<local_limb_type>(a1b0)
                + detail::make_hi<local_limb_type>(a0b1)
                ;

        rd3   = static_cast<local_double_limb_type>
                (
                  detail::make_hi<local_limb_type>(rd2)
                )
                + detail::make_lo<local_limb_type>(a3b0)
                + detail::make_lo<local_limb_type>(a2b1)
                + detail::make_lo<local_limb_type>(a1b2)
                + detail::make_lo<local_limb_type>(a0b3)
                + detail::make_hi<local_limb_type>(a2b0)
                + detail::make_hi<local_limb_type>(a1b1)
                + detail::make_hi<local_limb_type>(a0b2)
                ;

        rd4   = static_cast<local_double_limb_type>
                (
                  detail::make_hi<local_limb_type>(rd3)
                )
                + detail::make_lo<local_limb_type>(a3b1)
                + detail::make_lo<local_limb_type>(a2b2)
                + detail::make_lo<local_limb_type>(a1b3)
                + detail::make_hi<local_limb_type>(a3b0)
                + detail::make_hi<local_limb_type>(a2b1)
                + detail::make_hi<local_limb_type>(a1b2)
                + detail::make_hi<local_limb_type>(a0b3)
                ;

        rd5   = static_cast<local_double_limb_type>
                (
                  detail::make_hi<local_limb_type>(rd4)
                )
                + detail::make_lo<local_limb_type>(a3b2)
                + detail::make_lo<local_limb_type>(a2b3)
                + detail::make_hi<local_limb_type>(a3b1)
                + detail::make_hi<local_limb_type>(a2b2)
                + detail::make_hi<local_limb_type>(a1b3)
                ;

        rd6   = static_cast<local_double_limb_type>
                (
                  detail::make_hi<local_limb_type>(rd5)
                )
                + detail::make_lo<local_limb_type>(a3b3)
                + detail::make_hi<local_limb_type>(a3b2)
                + detail::make_hi<local_limb_type>(a2b3)
                ;

        *(r + static_cast<result_difference_type>(INT32_C(7)))
              = static_cast<local_limb_type>
                (
                    detail::make_hi<local_limb_type>(rd6)
                  + detail::make_hi<local_limb_type>(a3b3)
                )
                ;
      }
      else
      {
        const local_double_limb_type a4b0 = *(a + static_cast<left_difference_type>(INT32_C(4))) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(INT32_C(0))));
        const local_double_limb_type a0b4 = *(a + static_cast<left_difference_type>(INT32_C(0))) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(INT32_C(4))));

        const local_double_limb_type a5b0 = *(a + static_cast<left_difference_type>(INT32_C(5))) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(INT32_C(0))));
        const local_double_limb_type a4b1 = *(a + static_cast<left_difference_type>(INT32_C(4))) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(INT32_C(1))));

        const local_double_limb_type a1b4 = *(a + static_cast<left_difference_type>(INT32_C(1))) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(INT32_C(4))));
        const local_double_limb_type a0b5 = *(a + static_cast<left_difference_type>(INT32_C(0))) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(INT32_C(5))));

        const local_double_limb_type a6b0 = *(a + static_cast<left_difference_type>(INT32_C(6))) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(INT32_C(0))));
        const local_double_limb_type a5b1 = *(a + static_cast<left_difference_type>(INT32_C(5))) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(INT32_C(1))));

        const local_double_limb_type a4b2 = *(a + static_cast<left_difference_type>(INT32_C(4))) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(INT32_C(2))));
        const local_double_limb_type a2b4 = *(a + static_cast<left_difference_type>(INT32_C(2))) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(INT32_C(4))));

        const local_double_limb_type a1b5 = *(a + static_cast<left_difference_type>(INT32_C(1))) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(INT32_C(5))));
        const local_double_limb_type a0b6 = *(a + static_cast<left_difference_type>(INT32_C(0))) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(INT32_C(6))));

        rd1   = static_cast<local_double_limb_type>
                (
                  detail::make_hi<local_limb_type>(a0b0)
                )
                + detail::make_lo<local_limb_type>(a1b0)
                + detail::make_lo<local_limb_type>(a0b1)
                ;

        rd2   = static_cast<local_double_limb_type>
                (
                  detail::make_hi<local_limb_type>(rd1)
                )
                + detail::make_lo<local_limb_type>(a2b0)
                + detail::make_lo<local_limb_type>(a1b1)
                + detail::make_lo<local_limb_type>(a0b2)
                + detail::make_hi<local_limb_type>(a1b0)
                + detail::make_hi<local_limb_type>(a0b1)
                ;

        rd3   = static_cast<local_double_limb_type>
                (
                  detail::make_hi<local_limb_type>(rd2)
                )
                + detail::make_lo<local_limb_type>(a3b0)
                + detail::make_lo<local_limb_type>(a2b1)
                + detail::make_lo<local_limb_type>(a1b2)
                + detail::make_lo<local_limb_type>(a0b3)
                + detail::make_hi<local_limb_type>(a2b0)
                + detail::make_hi<local_limb_type>(a1b1)
                + detail::make_hi<local_limb_type>(a0b2)
                ;

        rd4   = static_cast<local_double_limb_type>
                (
                  detail::make_hi<local_limb_type>(rd3)
                )
                + detail::make_lo<local_limb_type>(a4b0)
                + detail::make_lo<local_limb_type>(a3b1)
                + detail::make_lo<local_limb_type>(a2b2)
                + detail::make_lo<local_limb_type>(a1b3)
                + detail::make_lo<local_limb_type>(a0b4)
                + detail::make_hi<local_limb_type>(a3b0)
                + detail::make_hi<local_limb_type>(a2b1)
                + detail::make_hi<local_limb_type>(a1b2)
                + detail::make_hi<local_limb_type>(a0b3)
                ;

        rd5   = static_cast<local_double_limb_type>
                (
                  detail::make_hi<local_limb_type>(rd4)
                )
                + detail::make_lo<local_limb_type>(a5b0)
                + detail::make_lo<local_limb_type>(a4b1)
                + detail::make_lo<local_limb_type>(a3b2)
                + detail::make_lo<local_limb_type>(a2b3)
                + detail::make_lo<local_limb_type>(a1b4)
                + detail::make_lo<local_limb_type>(a0b5)
                + detail::make_hi<local_limb_type>(a4b0)
                + detail::make_hi<local_limb_type>(a3b1)
                + detail::make_hi<local_limb_type>(a2b2)
                + detail::make_hi<local_limb_type>(a1b3)
                + detail::make_hi<local_limb_type>(a0b4)
                ;

        rd6   = static_cast<local_double_limb_type>
                (
                  detail::make_hi<local_limb_type>(rd5)
                )
                + detail::make_lo<local_limb_type>(a6b0)
                + detail::make_lo<local_limb_type>(a5b1)
                + detail::make_lo<local_limb_type>(a4b2)
                + detail::make_lo<local_limb_type>(a3b3)
                + detail::make_lo<local_limb_type>(a2b4)
                + detail::make_lo<local_limb_type>(a1b5)
                + detail::make_lo<local_limb_type>(a0b6)
                + detail::make_hi<local_limb_type>(a5b0)
                + detail::make_hi<local_limb_type>(a4b1)
                + detail::make_hi<local_limb_type>(a3b2)
                + detail::make_hi<local_limb_type>(a2b3)
                + detail::make_hi<local_limb_type>(a1b4)
                + detail::make_hi<local_limb_type>(a0b5)
                ;

        *(r + static_cast<result_difference_type>(INT32_C(7)))
              = static_cast<local_limb_type>
                (
                    detail::make_hi<local_limb_type>(rd6)
                  + static_cast<local_limb_type>    (*(a + static_cast<left_difference_type>(INT32_C(7))) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(INT32_C(0)))))
                  + static_cast<local_limb_type>    (*(a + static_cast<left_difference_type>(INT32_C(6))) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(INT32_C(1)))))
                  + static_cast<local_limb_type>    (*(a + static_cast<left_difference_type>(INT32_C(5))) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(INT32_C(2)))))
                  + static_cast<local_limb_type>    (*(a + static_cast<left_difference_type>(INT32_C(4))) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(INT32_C(3)))))
                  + static_cast<local_limb_type>    (*(a + static_cast<left_difference_type>(INT32_C(3))) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(INT32_C(4)))))
                  + static_cast<local_limb_type>    (*(a + static_cast<left_difference_type>(INT32_C(2))) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(INT32_C(5)))))
                  + static_cast<local_limb_type>    (*(a + static_cast<left_difference_type>(INT32_C(1))) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(INT32_C(6)))))
                  + static_cast<local_limb_type>    (*(a + static_cast<left_difference_type>(INT32_C(0))) * static_cast<local_double_limb_type>(*(b + static_cast<right_difference_type>(INT32_C(7)))))
                  + detail::make_hi<local_limb_type>(a6b0)
                  + detail::make_hi<local_limb_type>(a5b1)
                  + detail::make_hi<local_limb_type>(a4b2)
                  + detail::make_hi<local_limb_type>(a3b3)
                  + detail::make_hi<local_limb_type>(a2b4)
                  + detail::make_hi<local_limb_type>(a1b5)
                  + detail::make_hi<local_limb_type>(a0b6)
                )
                ;
      }

      *(r + static_cast<result_difference_type>(INT32_C(0))) = static_cast<local_limb_type>(a0b0);
      *(r + static_cast<result_difference_type>(INT32_C(1))) = static_cast<local_limb_type>(rd1);
      *(r + static_cast<result_difference_type>(INT32_C(2))) = static_cast<local_limb_type>(rd2);
      *(r + static_cast<result_difference_type>(INT32_C(3))) = static_cast<local_limb_type>(rd3);
      *(r + static_cast<result_difference_type>(INT32_C(4))) = static_cast<local_limb_type>(rd4);
      *(r + static_cast<result_difference_type>(INT32_C(5))) = static_cast<local_limb_type>(rd5);
      *(r + static_cast<result_difference_type>(INT32_C(6))) = static_cast<local_limb_type>(rd6);
    }
    #endif

    template<typename ResultIterator,
             typename InputIteratorLeft,
             typename InputIteratorRight,
             const size_t RePhraseWidth2 = Width2,
             typename std::enable_if<(   (uintwide_t<RePhraseWidth2, LimbType, AllocatorType>::number_of_limbs != static_cast<size_t>(UINT32_C(4)))
    #if defined(WIDE_INTEGER_HAS_MUL_8_BY_8_UNROLL)
                                      && (uintwide_t<RePhraseWidth2, LimbType, AllocatorType>::number_of_limbs != static_cast<size_t>(UINT32_C(8)))
    #endif
                                     )>::type const* = nullptr>
    static WIDE_INTEGER_CONSTEXPR void eval_multiply_n_by_n_to_lo_part(      ResultIterator     r,
                                                                             InputIteratorLeft  a,
                                                                             InputIteratorRight b,
                                                                       const unsigned_fast_type count)
    {
      static_assert
      (
           (std::numeric_limits<typename std::iterator_traits<ResultIterator>::value_type>::digits == std::numeric_limits<typename std::iterator_traits<InputIteratorLeft>::value_type>::digits)
        && (std::numeric_limits<typename std::iterator_traits<ResultIterator>::value_type>::digits == std::numeric_limits<typename std::iterator_traits<InputIteratorRight>::value_type>::digits),
        "Error: Internals require same widths for left-right-result limb_types at the moment"
      );

      using local_limb_type = typename std::iterator_traits<ResultIterator>::value_type;

      using local_double_limb_type =
        typename detail::uint_type_helper<static_cast<size_t>(std::numeric_limits<local_limb_type>::digits * 2)>::exact_unsigned_type;

      using result_difference_type = typename std::iterator_traits<ResultIterator>::difference_type;
      using left_difference_type   = typename std::iterator_traits<InputIteratorLeft>::difference_type;
      using right_difference_type  = typename std::iterator_traits<InputIteratorRight>::difference_type;

      std::fill_n(r, count, static_cast<local_limb_type>(0U));

      for(auto i = static_cast<unsigned_fast_type>(0U); i < count; ++i)
      {
        if(*(a + static_cast<left_difference_type>(i)) != static_cast<local_limb_type>(0U))
        {
          local_double_limb_type carry = 0U;

          for(auto j = static_cast<unsigned_fast_type>(0U); j < static_cast<unsigned_fast_type>(count - i); ++j)
          {
            carry = static_cast<local_double_limb_type>(carry + static_cast<local_double_limb_type>(static_cast<local_double_limb_type>(*(a + static_cast<left_difference_type>(i))) * *(b + static_cast<right_difference_type>(j))));
            carry = static_cast<local_double_limb_type>(carry + *(r + static_cast<result_difference_type>(i + j)));

            *(r + static_cast<result_difference_type>(i + j)) = static_cast<local_limb_type>(carry);
            carry                                             = detail::make_hi<local_limb_type>(carry);
          }
        }
      }
    }

    template<typename ResultIterator,
             typename InputIteratorLeft,
             typename InputIteratorRight>
    static WIDE_INTEGER_CONSTEXPR void eval_multiply_n_by_n_to_2n(      ResultIterator     r,
                                                                        InputIteratorLeft  a,
                                                                        InputIteratorRight b,
                                                                  const unsigned_fast_type count)
    {
      static_assert
      (
           (std::numeric_limits<typename std::iterator_traits<ResultIterator>::value_type>::digits == std::numeric_limits<typename std::iterator_traits<InputIteratorLeft>::value_type>::digits)
        && (std::numeric_limits<typename std::iterator_traits<ResultIterator>::value_type>::digits == std::numeric_limits<typename std::iterator_traits<InputIteratorRight>::value_type>::digits),
        "Error: Internals require same widths for left-right-result limb_types at the moment"
      );

      using local_limb_type = typename std::iterator_traits<ResultIterator>::value_type;

      using local_double_limb_type =
        typename detail::uint_type_helper<static_cast<size_t>(std::numeric_limits<local_limb_type>::digits * 2)>::exact_unsigned_type;

      using result_difference_type = typename std::iterator_traits<ResultIterator>::difference_type;
      using left_difference_type   = typename std::iterator_traits<InputIteratorLeft>::difference_type;
      using right_difference_type  = typename std::iterator_traits<InputIteratorRight>::difference_type;

      std::fill_n(r, (count * 2U), static_cast<local_limb_type>(0U));

      for(auto i = static_cast<unsigned_fast_type>(0U); i < count; ++i)
      {
        if(*(a + static_cast<left_difference_type>(i)) != static_cast<local_limb_type>(0U))
        {
          unsigned_fast_type j = 0U;

          local_double_limb_type carry = 0U;

          for( ; j < count; ++j)
          {
            carry = static_cast<local_double_limb_type>(carry + static_cast<local_double_limb_type>(static_cast<local_double_limb_type>(*(a + static_cast<left_difference_type>(i))) * *(b + static_cast<right_difference_type>(j))));
            carry = static_cast<local_double_limb_type>(carry + *(r + static_cast<result_difference_type>(i + j)));

            *(r + static_cast<result_difference_type>(i + j)) = static_cast<local_limb_type>(carry);
            carry                                             = detail::make_hi<local_limb_type>(carry);
          }

          *(r + static_cast<result_difference_type>(i + j)) = static_cast<local_limb_type>(carry);
        }
      }
    }

    template<typename ResultIterator,
             typename InputIteratorLeft>
    static WIDE_INTEGER_CONSTEXPR auto eval_multiply_1d(      ResultIterator                                               r,
                                                              InputIteratorLeft                                            a,
                                                        const typename std::iterator_traits<InputIteratorLeft>::value_type b,
                                                        const unsigned_fast_type                                           count) -> limb_type
    {
      static_assert
      (
        (std::numeric_limits<typename std::iterator_traits<ResultIterator>::value_type>::digits == std::numeric_limits<typename std::iterator_traits<InputIteratorLeft>::value_type>::digits),
        "Error: Internals require same widths for left-right-result limb_types at the moment"
      );

      using local_limb_type = typename std::iterator_traits<ResultIterator>::value_type;

      using local_double_limb_type =
        typename detail::uint_type_helper<static_cast<size_t>(std::numeric_limits<local_limb_type>::digits * 2)>::exact_unsigned_type;

      using result_difference_type = typename std::iterator_traits<ResultIterator>::difference_type;
      using left_difference_type   = typename std::iterator_traits<InputIteratorLeft>::difference_type;

      local_double_limb_type carry = 0U;

      if(b == 0U)
      {
        std::fill(r, r + count, static_cast<limb_type>(0U));
      }
      else
      {
        for(auto i = static_cast<unsigned_fast_type>(0U) ; i < count; ++i)
        {
          carry = static_cast<local_double_limb_type>(carry + static_cast<local_double_limb_type>(static_cast<local_double_limb_type>(*(a + static_cast<left_difference_type>(i))) * b));

          *(r + static_cast<result_difference_type>(i)) = static_cast<local_limb_type>(carry);
          carry                                         = detail::make_hi<local_limb_type>(carry);
        }
      }

      return static_cast<local_limb_type>(carry);
    }

    template<typename InputIteratorLeft>
    static WIDE_INTEGER_CONSTEXPR
    void eval_multiply_kara_propagate_carry(      InputIteratorLeft                                            t,
                                            const unsigned_fast_type                                           n,
                                            const typename std::iterator_traits<InputIteratorLeft>::value_type carry)
    {
      using local_limb_type = typename std::iterator_traits<InputIteratorLeft>::value_type;

      using local_double_limb_type =
        typename detail::uint_type_helper<static_cast<size_t>(std::numeric_limits<local_limb_type>::digits * 2)>::exact_unsigned_type;

      using left_difference_type   = typename std::iterator_traits<InputIteratorLeft>::difference_type;

      unsigned_fast_type i = 0U;

      local_limb_type carry_out = carry;

      while((i < n) && (carry_out != static_cast<local_limb_type>(0U))) // NOLINT(altera-id-dependent-backward-branch)
      {
        const local_double_limb_type uv_as_ularge = static_cast<local_double_limb_type>(*(t + static_cast<left_difference_type>(i))) + carry_out;

        carry_out = detail::make_hi<local_limb_type>(uv_as_ularge);

        *(t + static_cast<left_difference_type>(i)) = static_cast<local_limb_type>(uv_as_ularge);

        ++i;
      }
    }

    template<typename InputIteratorLeft>
    static WIDE_INTEGER_CONSTEXPR
    void eval_multiply_kara_propagate_borrow(      InputIteratorLeft  t,
                                             const unsigned_fast_type n,
                                             const bool               has_borrow)
    {
      using local_limb_type = typename std::iterator_traits<InputIteratorLeft>::value_type;

      using local_double_limb_type =
        typename detail::uint_type_helper<static_cast<size_t>(std::numeric_limits<local_limb_type>::digits * 2)>::exact_unsigned_type;

      using left_difference_type   = typename std::iterator_traits<InputIteratorLeft>::difference_type;

      unsigned_fast_type i = 0U;

      bool has_borrow_out = has_borrow;

      while((i < n) && (has_borrow_out)) // NOLINT(altera-id-dependent-backward-branch)
      {
        auto uv_as_ularge = static_cast<local_double_limb_type>(*(t + static_cast<left_difference_type>(i)));

        if(has_borrow_out)
        {
          --uv_as_ularge;
        }

        has_borrow_out = (detail::make_hi<local_limb_type>(uv_as_ularge) != static_cast<local_limb_type>(0U));

        *(t + static_cast<left_difference_type>(i)) = static_cast<local_limb_type>(uv_as_ularge);

        ++i;
      }
    }

    template<typename ResultIterator,
             typename InputIteratorLeft,
             typename InputIteratorRight,
             typename InputIteratorTemp>
    static WIDE_INTEGER_CONSTEXPR
    void eval_multiply_kara_n_by_n_to_2n(      ResultIterator     r, // NOLINT(misc-no-recursion)
                                         const InputIteratorLeft  a,
                                         const InputIteratorRight b,
                                         const unsigned_fast_type n,
                                               InputIteratorTemp  t)
    {
      if(n <= static_cast<unsigned_fast_type>(UINT32_C(48)))
      {
        static_cast<void>(t);

        eval_multiply_n_by_n_to_2n(r, a, b, n);
      }
      else
      {
        static_assert
        (
             (std::numeric_limits<typename std::iterator_traits<ResultIterator>::value_type>::digits == std::numeric_limits<typename std::iterator_traits<InputIteratorLeft>::value_type>::digits)
          && (std::numeric_limits<typename std::iterator_traits<ResultIterator>::value_type>::digits == std::numeric_limits<typename std::iterator_traits<InputIteratorRight>::value_type>::digits)
          && (std::numeric_limits<typename std::iterator_traits<ResultIterator>::value_type>::digits == std::numeric_limits<typename std::iterator_traits<InputIteratorTemp>::value_type>::digits),
          "Error: Internals require same widths for left-right-result limb_types at the moment"
        );

        using local_limb_type = typename std::iterator_traits<ResultIterator>::value_type;

        using result_difference_type = typename std::iterator_traits<ResultIterator>::difference_type;
        using left_difference_type   = typename std::iterator_traits<InputIteratorLeft>::difference_type;
        using right_difference_type  = typename std::iterator_traits<InputIteratorRight>::difference_type;
        using temp_difference_type   = typename std::iterator_traits<InputIteratorTemp>::difference_type;

        // Based on "Algorithm 1.3 KaratsubaMultiply", Sect. 1.3.2, page 5
        // of R.P. Brent and P. Zimmermann, "Modern Computer Arithmetic",
        // Cambridge University Press (2011).

        // The Karatsuba multipliation computes the product of u*v as:
        // [b^N + b^(N/2)] a1*b1 + [b^(N/2)](a1 - a0)(b0 - b1) + [b^(N/2) + 1] a0*b0

        // Here we visualize u and v in two components 0,1 corresponding
        // to the high and low order parts, respectively.

        // Step 1
        // Calculate a1*b1 and store it in the upper part of r.
        // Calculate a0*b0 and store it in the lower part of r.
        // copy r to t0.

        // Step 2
        // Add a1*b1 (which is t2) to the middle two-quarters of r (which is r1)
        // Add a0*b0 (which is t0) to the middle two-quarters of r (which is r1)

        // Step 3
        // Calculate |a1-a0| in t0 and note the sign (i.e., the borrow flag)

        // Step 4
        // Calculate |b0-b1| in t1 and note the sign (i.e., the borrow flag)

        // Step 5
        // Call kara mul to calculate |a1-a0|*|b0-b1| in (t2),
        // while using temporary storage in t4 along the way.

        // Step 6
        // Check the borrow signs. If a1-a0 and b0-b1 have the same signs,
        // then add |a1-a0|*|b0-b1| to r1, otherwise subtract it from r1.

        const unsigned_fast_type  nh = n / 2U;

        const InputIteratorLeft   a0 = a + static_cast<left_difference_type>(0);
        const InputIteratorLeft   a1 = a + static_cast<left_difference_type>(nh);

        const InputIteratorRight  b0 = b + static_cast<right_difference_type>(0);
        const InputIteratorRight  b1 = b + static_cast<right_difference_type>(nh);

              ResultIterator      r0 = r + static_cast<result_difference_type>(0);
              ResultIterator      r1 = r + static_cast<result_difference_type>(nh);
              ResultIterator      r2 = r + static_cast<result_difference_type>(n);
              ResultIterator      r3 = r + static_cast<result_difference_type>(n + nh);

              InputIteratorTemp   t0 = t + static_cast<temp_difference_type>(0);
              InputIteratorTemp   t1 = t + static_cast<temp_difference_type>(nh);
              InputIteratorTemp   t2 = t + static_cast<temp_difference_type>(n);
              InputIteratorTemp   t4 = t + static_cast<temp_difference_type>(n + n);

        // Step 1
        //   a1*b1 -> r2
        //   a0*b0 -> r0
        //   r -> t0
        eval_multiply_kara_n_by_n_to_2n(r2, a1, b1, nh, t0);
        eval_multiply_kara_n_by_n_to_2n(r0, a0, b0, nh, t0);
        std::copy(r0, r0 + (2U * n), t0);

        local_limb_type carry;

        // Step 2
        //   r1 += a1*b1
        //   r1 += a0*b0
        carry = eval_add_n(r1, r1, t2, n);
        eval_multiply_kara_propagate_carry(r3, nh, carry);
        carry = eval_add_n(r1, r1, t0, n);
        eval_multiply_kara_propagate_carry(r3, nh, carry);

        // Step 3
        //   |a1-a0| -> t0
        const std::int_fast8_t cmp_result_a1a0 = compare_ranges(a1, a0, nh);

        if(cmp_result_a1a0 == 1)
        {
          static_cast<void>(eval_subtract_n(t0, a1, a0, nh));
        }
        else if(cmp_result_a1a0 == -1)
        {
          static_cast<void>(eval_subtract_n(t0, a0, a1, nh));
        }

        // Step 4
        //   |b0-b1| -> t1
        const std::int_fast8_t cmp_result_b0b1 = compare_ranges(b0, b1, nh);

        if(cmp_result_b0b1 == 1)
        {
          static_cast<void>(eval_subtract_n(t1, b0, b1, nh));
        }
        else if(cmp_result_b0b1 == -1)
        {
          static_cast<void>(eval_subtract_n(t1, b1, b0, nh));
        }

        // Step 5
        //   |a1-a0|*|b0-b1| -> t2
        eval_multiply_kara_n_by_n_to_2n(t2, t0, t1, nh, t4);

        // Step 6
        //   either r1 += |a1-a0|*|b0-b1|
        //   or     r1 -= |a1-a0|*|b0-b1|
        if((cmp_result_a1a0 * cmp_result_b0b1) == 1)
        {
          carry = eval_add_n(r1, r1, t2, n);

          eval_multiply_kara_propagate_carry(r3, nh, carry);
        }
        else if((cmp_result_a1a0 * cmp_result_b0b1) == -1)
        {
          const bool has_borrow = eval_subtract_n(r1, r1, t2, n);

          eval_multiply_kara_propagate_borrow(r3, nh, has_borrow);
        }
      }
    }

    WIDE_INTEGER_CONSTEXPR void eval_divide_knuth(const uintwide_t& other, // NOLINT(readability-function-cognitive-complexity)
                                                        uintwide_t* remainder)
    {
      // Use Knuth's long division algorithm.
      // The loop-ordering of indices in Knuth's original
      // algorithm has been reversed due to the data format
      // used here. Several optimizations and combinations
      // of logic have been carried out in the source code.

      // See also:
      // D.E. Knuth, "The Art of Computer Programming, Volume 2:
      // Seminumerical Algorithms", Addison-Wesley (1998),
      // Section 4.3.1 Algorithm D and Exercise 16.

      using local_uint_index_type = unsigned_fast_type;

      auto u_offset = static_cast<local_uint_index_type>(0U);
      auto v_offset = static_cast<local_uint_index_type>(0U);

      // Compute the offsets for u and v.
      for(auto i = static_cast<local_uint_index_type>(0U); (i < number_of_limbs) && (*(      values.cbegin() + static_cast<size_t>(static_cast<local_uint_index_type>(number_of_limbs - 1U) - i)) == static_cast<limb_type>(0U)); ++i) { ++u_offset; } // NOLINT(altera-id-dependent-backward-branch)
      for(auto i = static_cast<local_uint_index_type>(0U); (i < number_of_limbs) && (*(other.values.cbegin() + static_cast<size_t>(static_cast<local_uint_index_type>(number_of_limbs - 1U) - i)) == static_cast<limb_type>(0U)); ++i) { ++v_offset; } // NOLINT(altera-id-dependent-backward-branch)

      if(v_offset == static_cast<local_uint_index_type>(number_of_limbs))
      {
        // The denominator is zero. Set the maximum value and return.
        // This also catches (0 / 0) and sets the maximum value for it.
        operator=(limits_helper_max(IsSigned));

        if(remainder != nullptr)
        {
          *remainder = uintwide_t(static_cast<std::uint8_t>(0U));
        }
      }
      else if(u_offset == static_cast<local_uint_index_type>(number_of_limbs))
      {
        // The numerator is zero. Do nothing and return.

        if(remainder != nullptr)
        {
          *remainder = uintwide_t(static_cast<std::uint8_t>(0U));
        }
      }
      else
      {
        const auto result_of_compare_left_with_right = compare(other);

        const bool left_is_less_than_right = (result_of_compare_left_with_right == INT8_C(-1));
        const bool left_is_equal_to_right  = (result_of_compare_left_with_right == INT8_C( 0));

        if(left_is_less_than_right)
        {
          // If the denominator is larger than the numerator,
          // then the result of the division is zero.
          if(remainder != nullptr)
          {
            *remainder = *this;
          }

          operator=(static_cast<std::uint8_t>(0U));
        }
        else if(left_is_equal_to_right)
        {
          // If the denominator is equal to the numerator,
          // then the result of the division is one.
          operator=(static_cast<std::uint8_t>(1U));

          if(remainder != nullptr)
          {
            *remainder = uintwide_t(static_cast<std::uint8_t>(0U));
          }
        }
        else if(v_offset == static_cast<local_uint_index_type>(number_of_limbs - 1U))
        {
          // The denominator has one single limb.
          // Use a one-dimensional division algorithm.
          const limb_type short_denominator = *other.values.cbegin();

          eval_divide_by_single_limb(short_denominator, u_offset, remainder);
        }
        else
        {
          // We will now use the Knuth long division algorithm.

          // Compute the normalization factor d.
          const auto d =
            static_cast<limb_type>(static_cast<double_limb_type>(  static_cast<double_limb_type>(static_cast<double_limb_type>(1U) << static_cast<unsigned>(std::numeric_limits<limb_type>::digits))
                                                                 / static_cast<double_limb_type>(static_cast<double_limb_type>(*(other.values.cbegin() + static_cast<size_t>(static_cast<local_uint_index_type>(number_of_limbs - 1U) - v_offset))) + static_cast<limb_type>(1U))));

          // Step D1(b), normalize u -> u * d = uu.
          // Step D1(c): normalize v -> v * d = vv.

          using uu_array_type =
            typename std::conditional<std::is_same<AllocatorType, void>::value,
                                      detail::fixed_static_array <limb_type, number_of_limbs + 1U>,
                                      detail::fixed_dynamic_array<limb_type,
                                                                  number_of_limbs + 1U,
                                                                  typename std::allocator_traits<typename std::conditional<std::is_same<AllocatorType, void>::value,
                                                                                                                           std::allocator<void>,
                                                                                                                           AllocatorType>::type>::template rebind_alloc<limb_type>>>::type;

          uu_array_type       uu;
          representation_type vv;

          if(d > static_cast<limb_type>(1U))
          {
            *(uu.begin() + static_cast<size_t>(static_cast<local_uint_index_type>(number_of_limbs) - u_offset)) =
              eval_multiply_1d(uu.data(), values.data(), d, number_of_limbs - u_offset);

            static_cast<void>(eval_multiply_1d(vv.data(), other.values.data(), d, number_of_limbs - v_offset));
          }
          else
          {
            std::copy(values.cbegin(), values.cend(), uu.begin());

            *(uu.begin() + static_cast<size_t>(static_cast<local_uint_index_type>(number_of_limbs) - u_offset)) = static_cast<limb_type>(0U);

            vv = other.values;
          }

          // Step D2: Initialize j.
          // Step D7: Loop on j from m to 0.

          const auto n   = static_cast<local_uint_index_type> (number_of_limbs - v_offset);
          const auto m   = static_cast<local_uint_index_type> (number_of_limbs - u_offset) - n;
          const auto vj0 = static_cast<local_uint_index_type>((number_of_limbs - 1U) - v_offset);

          for(auto j = static_cast<local_uint_index_type>(0U); j <= m; ++j) // NOLINT(altera-id-dependent-backward-branch)
          {
            // Step D3 [Calculate q_hat].
            //   if u[j] == v[j0]
            //     set q_hat = b - 1
            //   else
            //     set q_hat = (u[j] * b + u[j + 1]) / v[1]

            const auto uj     = static_cast<local_uint_index_type>(static_cast<local_uint_index_type>(static_cast<local_uint_index_type>(static_cast<local_uint_index_type>(number_of_limbs + 1U) - 1U) - u_offset) - j);
            const auto u_j_j1 = static_cast<double_limb_type>(static_cast<double_limb_type>(static_cast<double_limb_type>(*(uu.cbegin() + static_cast<size_t>(uj))) << static_cast<unsigned>(std::numeric_limits<limb_type>::digits)) + *(uu.cbegin() + static_cast<size_t>(uj - 1U)));

            limb_type q_hat = ((*(uu.cbegin() + static_cast<size_t>(uj)) == *(vv.cbegin() + static_cast<size_t>(vj0)))
              ? (std::numeric_limits<limb_type>::max)()
              : static_cast<limb_type>(u_j_j1 / *(vv.cbegin() + static_cast<size_t>(vj0))));

            // Decrease q_hat if necessary.
            // This means that q_hat must be decreased if the
            // expression [(u[uj] * b + u[uj - 1] - q_hat * v[vj0 - 1]) * b]
            // exceeds the range of uintwide_t.

            for(auto t = static_cast<double_limb_type>(u_j_j1 - static_cast<double_limb_type>(q_hat * static_cast<double_limb_type>(*(vv.cbegin() + static_cast<size_t>(vj0))))); ; --q_hat, t = static_cast<double_limb_type>(t + *(vv.cbegin() + static_cast<size_t>(vj0))))
            {
              if(   (detail::make_hi<limb_type>(t) != static_cast<limb_type>(0U))
                 || (   static_cast<double_limb_type>(static_cast<double_limb_type>(*(vv.cbegin() + static_cast<size_t>(vj0 - 1U))) * q_hat)
                     <= static_cast<double_limb_type>(static_cast<double_limb_type>(t << static_cast<unsigned>(std::numeric_limits<limb_type>::digits)) + *(uu.cbegin() + static_cast<size_t>(uj - 2U)))))
              {
                break;
              }
            }

            // Step D4: Multiply and subtract.
            // Replace u[j, ... j + n] by u[j, ... j + n] - q_hat * v[1, ... n].

            // Set nv = q_hat * (v[1, ... n]).
            uu_array_type nv;

            *(nv.begin() + static_cast<size_t>(n)) = eval_multiply_1d(nv.data(), vv.data(), q_hat, n);

            const bool has_borrow =
              eval_subtract_n(uu.data() + static_cast<size_t>(static_cast<local_uint_index_type>(uj - n)),
                              uu.data() + static_cast<size_t>(static_cast<local_uint_index_type>(uj - n)),
                              nv.data(),
                              n + 1U);


            // Get the result data.
            *(values.begin() + static_cast<size_t>(m - j)) = static_cast<limb_type>(q_hat - (has_borrow ? 1U : 0U));

            // Step D5: Test the remainder.
            // Set the result value: Set result.m_data[m - j] = q_hat.
            // Use the condition (u[j] < 0), in other words if the borrow
            // is non-zero, then step D6 needs to be carried out.

            if(has_borrow)
            {
              // Step D6: Add back.
              // Add v[1, ... n] back to u[j, ... j + n],
              // and decrease the result by 1.

              static_cast<void>(eval_add_n(uu.data() + static_cast<size_t>(static_cast<local_uint_index_type>(uj - n)),
                                           uu.data() + static_cast<size_t>(static_cast<local_uint_index_type>(uj - n)),
                                           vv.data(),
                                           n));
            }
          }

          // Clear the data elements that have not
          // been computed in the division algorithm.
          std::fill(values.begin() + static_cast<local_uint_index_type>(m + 1U), values.end(), static_cast<limb_type>(0U));

          if(remainder != nullptr)
          {
            if(d == 1U)
            {
              std::copy(uu.cbegin(),
                        uu.cbegin() + static_cast<size_t>(static_cast<local_uint_index_type>(number_of_limbs - v_offset)),
                        remainder->values.begin());
            }
            else
            {
              auto previous_u = static_cast<limb_type>(0U);

              for(auto rl = static_cast<signed_fast_type>(n - 1U), ul = static_cast<signed_fast_type>(number_of_limbs - (v_offset + 1U)); rl >= 0; --rl, --ul) // NOLINT(altera-id-dependent-backward-branch)
              {
                const auto t =
                  static_cast<double_limb_type>(  *(uu.cbegin() + static_cast<size_t>(ul))
                                                + static_cast<double_limb_type>(static_cast<double_limb_type>(previous_u) << static_cast<unsigned>(std::numeric_limits<limb_type>::digits)));

                *(remainder->values.begin() + static_cast<size_t>(rl)) = static_cast<limb_type>(static_cast<double_limb_type>(t / d));
                previous_u                                             = static_cast<limb_type>(static_cast<double_limb_type>(t - static_cast<double_limb_type>(static_cast<double_limb_type>(d) * *(remainder->values.cbegin() + static_cast<size_t>(rl)))));
              }
            }

            std::fill(remainder->values.begin() + static_cast<size_t>(n),
                      remainder->values.end(),
                      static_cast<limb_type>(0U));
          }
        }
      }
    }

    WIDE_INTEGER_CONSTEXPR void shl(const unsigned_fast_type offset, // NOLINT(bugprone-easily-swappable-parameters)
                                    const std::uint_fast16_t left_shift_amount)
    {
      if(offset > 0U)
      {
        std::copy_backward(values.data(),
                           values.data() + static_cast<size_t>(number_of_limbs - offset),
                           values.data() + static_cast<size_t>(number_of_limbs));

        std::fill(values.begin(), values.begin() + static_cast<size_t>(offset), static_cast<limb_type>(0U));
      }

      using local_integral_type = unsigned_fast_type;

      if(left_shift_amount != static_cast<local_integral_type>(0U))
      {
        auto part_from_previous_value = static_cast<limb_type>(0U);

        for(unsigned_fast_type i = offset; i < static_cast<unsigned_fast_type>(number_of_limbs); ++i) // NOLINT(altera-id-dependent-backward-branch)
        {
          const limb_type t = *(values.cbegin() + static_cast<size_t>(i));

          *(values.begin() + static_cast<size_t>(i)) =
            static_cast<limb_type>(static_cast<limb_type>(t << static_cast<local_integral_type>(left_shift_amount)) | part_from_previous_value);

          part_from_previous_value =
            static_cast<limb_type>(t >> static_cast<local_integral_type>(static_cast<unsigned_fast_type>(std::numeric_limits<limb_type>::digits - left_shift_amount)));
        }
      }
    }

    WIDE_INTEGER_CONSTEXPR void shr(const unsigned_fast_type offset, // NOLINT(bugprone-easily-swappable-parameters)
                                    const std::uint_fast16_t right_shift_amount)
    {
      if(offset > 0U)
      {
        std::copy(values.begin() + static_cast<size_t>(offset),
                  values.begin() + static_cast<size_t>(number_of_limbs),
                  values.begin());

        std::fill(values.end() - static_cast<size_t>(offset),
                  values.end(),
                  (!is_neg(*this)) ? static_cast<limb_type>(0U) : static_cast<limb_type>((std::numeric_limits<limb_type>::max)()));
      }

      using local_integral_type = unsigned_fast_type;

      if(right_shift_amount != static_cast<local_integral_type>(0U))
      {
        limb_type part_from_previous_value =
          (!is_neg(*this))
            ? static_cast<limb_type>(0U)
            : static_cast<limb_type>((std::numeric_limits<limb_type>::max)() << static_cast<std::uint_fast16_t>(static_cast<std::uint_fast16_t>(std::numeric_limits<limb_type>::digits) - right_shift_amount));

        for(auto i = static_cast<signed_fast_type>((number_of_limbs - 1U) - offset); i >= static_cast<signed_fast_type>(0); --i) // NOLINT(altera-id-dependent-backward-branch)
        {
          const limb_type t = *(values.cbegin() + static_cast<size_t>(i));

          *(values.begin() + static_cast<size_t>(i)) = static_cast<limb_type>(static_cast<limb_type>(t >> static_cast<local_integral_type>(right_shift_amount)) | part_from_previous_value);

          part_from_previous_value = static_cast<limb_type>(t << static_cast<local_integral_type>(static_cast<unsigned_fast_type>(std::numeric_limits<limb_type>::digits - right_shift_amount)));
        }
      }
    }

    // Read string function.
    WIDE_INTEGER_CONSTEXPR auto rd_string(const char* str_input) -> bool // NOLINT(readability-function-cognitive-complexity)
    {
      std::fill(values.begin(), values.end(), static_cast<limb_type>(0U));

      const unsigned_fast_type str_length = detail::strlen_unsafe(str_input);

      std::uint_fast8_t base = UINT8_C(10);

      unsigned_fast_type pos = 0U;

      // Detect: Is there a plus sign?
      // And if there is a plus sign, skip over the plus sign.
      if((str_length > 0U) && (str_input[0U] == static_cast<char>('+'))) // NOLINT(cppcoreguidelines-pro-bounds-pointer-arithmetic)
      {
        ++pos;
      }

      bool str_has_neg_sign = false;

      // Detect: Is there a minus sign?
      // And if there is a minus sign, skip over the minus sign.
      if((str_length > 0U) && (str_input[0U] == static_cast<char>('-'))) // NOLINT(cppcoreguidelines-pro-bounds-pointer-arithmetic)
      {
        str_has_neg_sign = true;

        ++pos;
      }

      // Perform a dynamic detection of the base.
      if(str_length > (pos + 0U))
      {
        const bool might_be_oct_or_hex = ((str_input[pos + 0U] == static_cast<char>('0')) && (str_length > (pos + 1U))); // NOLINT(cppcoreguidelines-pro-bounds-pointer-arithmetic)

        if(might_be_oct_or_hex)
        {
          if((str_input[pos + 1U] >= static_cast<char>('0')) && (str_input[pos + 1U] <= static_cast<char>('8'))) // NOLINT(cppcoreguidelines-pro-bounds-pointer-arithmetic)
          {
            // The input format is octal.
            base = UINT8_C(8);

            pos += 1U;
          }
          else if((str_input[pos + 1U] == static_cast<char>('x')) || (str_input[pos + 1U] == static_cast<char>('X'))) // NOLINT(cppcoreguidelines-pro-bounds-pointer-arithmetic)
          {
            // The input format is hexadecimal.
            base = UINT8_C(16);

            pos += 2U;
          }
        }
        else if((str_input[pos + 0U] >= static_cast<char>('0')) && (str_input[pos + 0U] <= static_cast<char>('9'))) // NOLINT(cppcoreguidelines-pro-bounds-pointer-arithmetic)
        {
          // The input format is decimal.
          ;
        }
      }

      bool char_is_valid = true;

      for( ; ((pos < str_length) && char_is_valid); ++pos) // NOLINT(altera-id-dependent-backward-branch)
      {
        const auto c = static_cast<std::uint8_t>(str_input[pos]); // NOLINT(cppcoreguidelines-pro-bounds-pointer-arithmetic)

        // TBD: Handle other digit delimiters in addition to apostrophe.
        const bool char_is_apostrophe = (c == static_cast<char>(39));

        if(!char_is_apostrophe)
        {
          if(base == UINT8_C(8))
          {
            std::uint8_t uc_oct { };

            if  ((c >= static_cast<char>('0')) && (c <= static_cast<char>('8'))) { uc_oct = static_cast<std::uint8_t>(c - static_cast<std::uint8_t>(UINT8_C(0x30))); }
            else                                                                 { uc_oct = static_cast<std::uint8_t>('\0'); char_is_valid = false; }

            if(char_is_valid)
            {
              operator<<=(3);

              *values.begin() |= uc_oct;
            }
          }
          else if(base == UINT8_C(10))
          {
            std::uint8_t uc_dec { };

            if   ((c >= static_cast<std::uint8_t>('0')) && (c <= static_cast<std::uint8_t>('9'))) { uc_dec = static_cast<std::uint8_t>(c - static_cast<std::uint8_t>(UINT8_C(0x30))); }
            else                                                                                  { uc_dec = static_cast<std::uint8_t>('\0'); char_is_valid = false; }

            if(char_is_valid)
            {
              mul_by_limb(static_cast<limb_type>(UINT8_C(10)));

              operator+=(uc_dec);
            }
          }
          else if(base == UINT8_C(16))
          {
            std::uint8_t uc_hex { };

            if     ((c >= static_cast<std::uint8_t>('a')) && (c <= static_cast<std::uint8_t>('f'))) { uc_hex = static_cast<std::uint8_t>(c - static_cast<std::uint8_t>(UINT8_C(  87))); }
            else if((c >= static_cast<std::uint8_t>('A')) && (c <= static_cast<std::uint8_t>('F'))) { uc_hex = static_cast<std::uint8_t>(c - static_cast<std::uint8_t>(UINT8_C(  55))); }
            else if((c >= static_cast<std::uint8_t>('0')) && (c <= static_cast<std::uint8_t>('9'))) { uc_hex = static_cast<std::uint8_t>(c - static_cast<std::uint8_t>(UINT8_C(0x30))); }
            else                                                                                    { uc_hex = static_cast<std::uint8_t>('\0'); char_is_valid = false; }

            if(char_is_valid)
            {
              operator<<=(4);

              *values.begin() |= uc_hex;
            }
          }
        }
      }

      if(str_has_neg_sign)
      {
        negate();
      }

      return char_is_valid;
    }

    WIDE_INTEGER_CONSTEXPR void bitwise_not()
    {
      for(auto i = static_cast<unsigned_fast_type>(0U); i < number_of_limbs; ++i)
      {
        *(values.begin() + static_cast<size_t>(i)) = static_cast<limb_type>(~(*(values.cbegin() + static_cast<size_t>(i))));
      }
    }

    WIDE_INTEGER_CONSTEXPR void preincrement()
    {
      // Implement pre-increment.
      unsigned_fast_type i = 0U;

      for( ; (i < static_cast<unsigned_fast_type>(values.size() - 1U)) && (++(*(values.begin() + static_cast<size_t>(i))) == static_cast<limb_type>(0U)); ++i) // NOLINT(altera-id-dependent-backward-branch)
      {
        ;
      }

      if(i == static_cast<unsigned_fast_type>(values.size() - 1U))
      {
        ++(*(values.begin() + static_cast<size_t>(i)));
      }
    }

    WIDE_INTEGER_CONSTEXPR void predecrement()
    {
      // Implement pre-decrement.
      unsigned_fast_type i = 0U;

      for( ; (i < static_cast<unsigned_fast_type>(values.size() - 1U)) && ((*(values.begin() + static_cast<size_t>(i)))-- == static_cast<limb_type>(0U)); ++i) // NOLINT(altera-id-dependent-backward-branch)
      {
        ;
      }

      if(i == static_cast<unsigned_fast_type>(values.size() - 1U))
      {
        --(*(values.begin() + static_cast<size_t>(i)));
      }
    }
  };

  // Define some convenient unsigned wide integer types.
  using uint64_t    = uintwide_t<static_cast<size_t>(UINT32_C(   64)), std::uint16_t>;
  using uint128_t   = uintwide_t<static_cast<size_t>(UINT32_C(  128)), std::uint32_t>;
  using uint256_t   = uintwide_t<static_cast<size_t>(UINT32_C(  256)), std::uint32_t>;
  using uint512_t   = uintwide_t<static_cast<size_t>(UINT32_C(  512)), std::uint32_t>;
  using uint1024_t  = uintwide_t<static_cast<size_t>(UINT32_C( 1024)), std::uint32_t>;
  using uint2048_t  = uintwide_t<static_cast<size_t>(UINT32_C( 2048)), std::uint32_t>;
  using uint4096_t  = uintwide_t<static_cast<size_t>(UINT32_C( 4096)), std::uint32_t>;
  using uint8192_t  = uintwide_t<static_cast<size_t>(UINT32_C( 8192)), std::uint32_t>;
  using uint16384_t = uintwide_t<static_cast<size_t>(UINT32_C(16384)), std::uint32_t>;
  using uint32768_t = uintwide_t<static_cast<size_t>(UINT32_C(32768)), std::uint32_t>;
  using uint65536_t = uintwide_t<static_cast<size_t>(UINT32_C(65536)), std::uint32_t>;

  #if !defined(WIDE_INTEGER_DISABLE_TRIVIAL_COPY_AND_STD_LAYOUT_CHECKS)
  static_assert(std::is_trivially_copyable<uint64_t   >::value, "uintwide_t must be trivially copyable.");
  static_assert(std::is_trivially_copyable<uint128_t  >::value, "uintwide_t must be trivially copyable.");
  static_assert(std::is_trivially_copyable<uint256_t  >::value, "uintwide_t must be trivially copyable.");
  static_assert(std::is_trivially_copyable<uint512_t  >::value, "uintwide_t must be trivially copyable.");
  static_assert(std::is_trivially_copyable<uint1024_t >::value, "uintwide_t must be trivially copyable.");
  static_assert(std::is_trivially_copyable<uint2048_t >::value, "uintwide_t must be trivially copyable.");
  static_assert(std::is_trivially_copyable<uint4096_t >::value, "uintwide_t must be trivially copyable.");
  static_assert(std::is_trivially_copyable<uint8192_t >::value, "uintwide_t must be trivially copyable.");
  static_assert(std::is_trivially_copyable<uint16384_t>::value, "uintwide_t must be trivially copyable.");
  static_assert(std::is_trivially_copyable<uint32768_t>::value, "uintwide_t must be trivially copyable.");
  static_assert(std::is_trivially_copyable<uint65536_t>::value, "uintwide_t must be trivially copyable.");

  static_assert(std::is_standard_layout<uint64_t   >::value, "uintwide_t must have standard layout.");
  static_assert(std::is_standard_layout<uint128_t  >::value, "uintwide_t must have standard layout.");
  static_assert(std::is_standard_layout<uint256_t  >::value, "uintwide_t must have standard layout.");
  static_assert(std::is_standard_layout<uint512_t  >::value, "uintwide_t must have standard layout.");
  static_assert(std::is_standard_layout<uint1024_t >::value, "uintwide_t must have standard layout.");
  static_assert(std::is_standard_layout<uint2048_t >::value, "uintwide_t must have standard layout.");
  static_assert(std::is_standard_layout<uint4096_t >::value, "uintwide_t must have standard layout.");
  static_assert(std::is_standard_layout<uint8192_t >::value, "uintwide_t must have standard layout.");
  static_assert(std::is_standard_layout<uint16384_t>::value, "uintwide_t must have standard layout.");
  static_assert(std::is_standard_layout<uint32768_t>::value, "uintwide_t must have standard layout.");
  static_assert(std::is_standard_layout<uint65536_t>::value, "uintwide_t must have standard layout.");
  #endif

  using  int64_t    = uintwide_t<static_cast<size_t>(UINT32_C(   64)), std::uint16_t, void, true>;
  using  int128_t   = uintwide_t<static_cast<size_t>(UINT32_C(  128)), std::uint32_t, void, true>;
  using  int256_t   = uintwide_t<static_cast<size_t>(UINT32_C(  256)), std::uint32_t, void, true>;
  using  int512_t   = uintwide_t<static_cast<size_t>(UINT32_C(  512)), std::uint32_t, void, true>;
  using  int1024_t  = uintwide_t<static_cast<size_t>(UINT32_C( 1024)), std::uint32_t, void, true>;
  using  int2048_t  = uintwide_t<static_cast<size_t>(UINT32_C( 2048)), std::uint32_t, void, true>;
  using  int4096_t  = uintwide_t<static_cast<size_t>(UINT32_C( 4096)), std::uint32_t, void, true>;
  using  int8192_t  = uintwide_t<static_cast<size_t>(UINT32_C( 8192)), std::uint32_t, void, true>;
  using  int16384_t = uintwide_t<static_cast<size_t>(UINT32_C(16384)), std::uint32_t, void, true>;
  using  int32768_t = uintwide_t<static_cast<size_t>(UINT32_C(32768)), std::uint32_t, void, true>;
  using  int65536_t = uintwide_t<static_cast<size_t>(UINT32_C(65536)), std::uint32_t, void, true>;

  #if !defined(WIDE_INTEGER_DISABLE_TRIVIAL_COPY_AND_STD_LAYOUT_CHECKS)
  static_assert(std::is_trivially_copyable<int64_t   >::value, "uintwide_t must be trivially copyable.");
  static_assert(std::is_trivially_copyable<int128_t  >::value, "uintwide_t must be trivially copyable.");
  static_assert(std::is_trivially_copyable<int256_t  >::value, "uintwide_t must be trivially copyable.");
  static_assert(std::is_trivially_copyable<int512_t  >::value, "uintwide_t must be trivially copyable.");
  static_assert(std::is_trivially_copyable<int1024_t >::value, "uintwide_t must be trivially copyable.");
  static_assert(std::is_trivially_copyable<int2048_t >::value, "uintwide_t must be trivially copyable.");
  static_assert(std::is_trivially_copyable<int4096_t >::value, "uintwide_t must be trivially copyable.");
  static_assert(std::is_trivially_copyable<int8192_t >::value, "uintwide_t must be trivially copyable.");
  static_assert(std::is_trivially_copyable<int16384_t>::value, "uintwide_t must be trivially copyable.");
  static_assert(std::is_trivially_copyable<int32768_t>::value, "uintwide_t must be trivially copyable.");
  static_assert(std::is_trivially_copyable<int65536_t>::value, "uintwide_t must be trivially copyable.");

  static_assert(std::is_standard_layout<int64_t   >::value, "uintwide_t must have standard layout.");
  static_assert(std::is_standard_layout<int128_t  >::value, "uintwide_t must have standard layout.");
  static_assert(std::is_standard_layout<int256_t  >::value, "uintwide_t must have standard layout.");
  static_assert(std::is_standard_layout<int512_t  >::value, "uintwide_t must have standard layout.");
  static_assert(std::is_standard_layout<int1024_t >::value, "uintwide_t must have standard layout.");
  static_assert(std::is_standard_layout<int2048_t >::value, "uintwide_t must have standard layout.");
  static_assert(std::is_standard_layout<int4096_t >::value, "uintwide_t must have standard layout.");
  static_assert(std::is_standard_layout<int8192_t >::value, "uintwide_t must have standard layout.");
  static_assert(std::is_standard_layout<int16384_t>::value, "uintwide_t must have standard layout.");
  static_assert(std::is_standard_layout<int32768_t>::value, "uintwide_t must have standard layout.");
  static_assert(std::is_standard_layout<int65536_t>::value, "uintwide_t must have standard layout.");
  #endif

  // Insert a base class for numeric_limits<> support.
  // This class inherits from std::numeric_limits<unsigned int>
  // in order to provide limits for a non-specific unsigned type.

  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  WIDE_INTEGER_NUM_LIMITS_CLASS_TYPE numeric_limits_uintwide_t_base
    : public std::numeric_limits<typename std::conditional<(!IsSigned), unsigned int, signed int>::type>
  {
  private:
    using local_wide_integer_type = uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;

  public:
    static constexpr int digits          = (!IsSigned)
                                             ? static_cast<int>(local_wide_integer_type::my_width2)
                                             : static_cast<int>(local_wide_integer_type::my_width2 - 1U);

    static constexpr int digits10        = static_cast<int>((static_cast<std::uintmax_t>(digits)       * UINTMAX_C(75257499)) / UINTMAX_C(250000000));
    static constexpr int max_digits10    = digits10;
    static constexpr int max_exponent    = digits;
    static constexpr int max_exponent10  = static_cast<int>((static_cast<std::uintmax_t>(max_exponent) * UINTMAX_C(75257499)) / UINTMAX_C(250000000));

    static constexpr auto (max) () -> local_wide_integer_type { return local_wide_integer_type::limits_helper_max   (IsSigned); }
    static constexpr auto (min) () -> local_wide_integer_type { return local_wide_integer_type::limits_helper_min   (IsSigned); }
    static constexpr auto lowest() -> local_wide_integer_type { return local_wide_integer_type::limits_helper_lowest(IsSigned); }
  };

  template<class T>
  struct is_integral : public std::is_integral<T> { };

  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  struct is_integral<math::wide_integer::uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>
    : public std::integral_constant<bool, true> { };

  #if(__cplusplus >= 201703L)
  } // namespace math::wide_integer
  #else
  } // namespace wide_integer
  } // namespace math
  #endif

  WIDE_INTEGER_NAMESPACE_END

  namespace std
  {
    // Specialization of std::numeric_limits<uintwide_t>.
    #if defined(WIDE_INTEGER_NAMESPACE)
    template<const WIDE_INTEGER_NAMESPACE::math::wide_integer::size_t Width2,
             typename LimbType,
             typename AllocatorType,
             const bool IsSigned>
    WIDE_INTEGER_NUM_LIMITS_CLASS_TYPE numeric_limits<WIDE_INTEGER_NAMESPACE::math::wide_integer::uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>
      : public WIDE_INTEGER_NAMESPACE::math::wide_integer::numeric_limits_uintwide_t_base<Width2, LimbType, AllocatorType, IsSigned> { };
    #else
    template<const ::math::wide_integer::size_t Width2,
             typename LimbType,
             typename AllocatorType,
             const bool IsSigned>
    WIDE_INTEGER_NUM_LIMITS_CLASS_TYPE numeric_limits<::math::wide_integer::uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>
      : public ::math::wide_integer::numeric_limits_uintwide_t_base<Width2, LimbType, AllocatorType, IsSigned> { };
    #endif
  } // namespace std

  WIDE_INTEGER_NAMESPACE_BEGIN

  #if(__cplusplus >= 201703L)
  namespace math::wide_integer {
  #else
  namespace math { namespace wide_integer { // NOLINT(modernize-concat-nested-namespaces)
  #endif

  // Non-member binary add, sub, mul, div, mod of (uintwide_t op uintwide_t).
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator+ (const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned> { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator+=(v); }
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator- (const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned> { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator-=(v); }
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator* (const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned> { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator*=(v); }
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator/ (const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned> { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator/=(v); }
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator% (const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned> { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator%=(v); }

  // Non-member binary logic operations of (uintwide_t op uintwide_t).
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator| (const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned> { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator|=(v); }
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator^ (const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned> { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator^=(v); }
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator& (const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned> { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator&=(v); }

  // Non-member binary add, sub, mul, div, mod of (uintwide_t op IntegralType).
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator+(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator+=(uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(v)); }
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator-(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator-=(uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(v)); }
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator*(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator*=(uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(v)); }
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator/(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator/=(uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(v)); }

  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned>
  constexpr auto operator%(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<(   ( std::is_integral<IntegralType>::value)
                                                                                                                                              && (!std::is_unsigned<IntegralType>::value)),
                                                                                                                                              uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type
  { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator%=(uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(v)); }

  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned>
  WIDE_INTEGER_CONSTEXPR auto operator%(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<(   (std::is_integral<IntegralType>::value)
                                                                                                                                                           && (std::is_unsigned<IntegralType>::value)
                                                                                                                                                           && (std::numeric_limits<IntegralType>::digits <= std::numeric_limits<LimbType>::digits)),
                                                                                                                                                           typename uintwide_t<Width2, LimbType, AllocatorType, IsSigned>::limb_type>::type
  {
    using local_wide_integer_type = uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;

    const bool u_is_neg = local_wide_integer_type::is_neg(u);

    local_wide_integer_type remainder;

    local_wide_integer_type((!u_is_neg) ? u : -u).eval_divide_by_single_limb(v, 0U, &remainder);

    using local_limb_type = typename local_wide_integer_type::limb_type;

    auto u_rem = static_cast<local_limb_type>(remainder);

    return ((!u_is_neg) ? u_rem : static_cast<local_limb_type>(static_cast<local_limb_type>(~u_rem) + 1U));
  }

  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned>
  constexpr auto operator%(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<(   (std::is_integral<IntegralType>::value)
                                                                                                                                              && (std::is_unsigned<IntegralType>::value)
                                                                                                                                              && (std::numeric_limits<IntegralType>::digits > std::numeric_limits<LimbType>::digits)),
                                                                                                                                              uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type
  { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator%=(uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(v)); }

  // Non-member binary add, sub, mul, div, mod of (IntegralType op uintwide_t).
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator+(const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator+=(v); }
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator-(const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator-=(v); }
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator*(const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator*=(v); }
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator/(const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator/=(v); }
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator%(const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator%=(v); }

  #if !defined(WIDE_INTEGER_DISABLE_FLOAT_INTEROP)
  // Non-member binary add, sub, mul, div, mod of (uintwide_t op FloatingPointType).
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator+(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const FloatingPointType& f) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator+=(uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(f)); }
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator-(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const FloatingPointType& f) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator-=(uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(f)); }
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator*(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const FloatingPointType& f) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator*=(uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(f)); }
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator/(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const FloatingPointType& f) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator/=(uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(f)); }
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator%(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const FloatingPointType& f) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator%=(uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(f)); }

  // Non-member binary add, sub, mul, div, mod of (FloatingPointType op uintwide_t).
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator+(const FloatingPointType& f, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(f).operator+=(v); }
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator-(const FloatingPointType& f, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(f).operator-=(v); }
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator*(const FloatingPointType& f, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(f).operator*=(v); }
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator/(const FloatingPointType& f, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(f).operator/=(v); }
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator%(const FloatingPointType& f, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(f).operator%=(v); }
  #endif

  // Non-member binary logic operations of (uintwide_t op IntegralType).
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator|(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator|=(uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(v)); }
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator^(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator^=(uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(v)); }
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator&(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator&=(uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(v)); }

  // Non-member binary binary logic operations of (IntegralType op uintwide_t).
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator|(const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator|=(v); }
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator^(const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator^=(v); }
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator&(const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator&=(v); }

  // Non-member shift functions of (uintwide_t shift IntegralType).
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator<<(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType n) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator<<=(n); }
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator>>(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType n) -> typename std::enable_if<std::is_integral<IntegralType>::value, uintwide_t<Width2, LimbType, AllocatorType, IsSigned>>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator>>=(n); }

  // Non-member comparison functions of (uintwide_t cmp uintwide_t).
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator==(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> bool { return u.operator==(v); }
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator!=(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> bool { return u.operator!=(v); }
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator> (const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> bool { return u.operator> (v); }
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator< (const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> bool { return u.operator< (v); }
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator>=(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> bool { return u.operator>=(v); }
  template<const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator<=(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> bool { return u.operator<=(v); }

  // Non-member comparison functions of (uintwide_t cmp IntegralType).
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator==(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, bool>::type { return u.operator==(uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(v)); }
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator!=(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, bool>::type { return u.operator!=(uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(v)); }
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator> (const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, bool>::type { return u.operator> (uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(v)); }
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator< (const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, bool>::type { return u.operator< (uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(v)); }
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator>=(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, bool>::type { return u.operator>=(uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(v)); }
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator<=(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const IntegralType& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, bool>::type { return u.operator<=(uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(v)); }

  // Non-member comparison functions of (IntegralType cmp uintwide_t).
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator==(const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, bool>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator==(v); }
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator!=(const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, bool>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator!=(v); }
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator> (const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, bool>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator> (v); }
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator< (const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, bool>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator< (v); }
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator>=(const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, bool>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator>=(v); }
  template<typename IntegralType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator<=(const IntegralType& u, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_integral<IntegralType>::value, bool>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(u).operator<=(v); }

  #if !defined(WIDE_INTEGER_DISABLE_FLOAT_INTEROP)
  // Non-member comparison functions of (uintwide_t cmp FloatingPointType).
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator==(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const FloatingPointType& f) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, bool>::type { return u.operator==(uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(f)); }
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator!=(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const FloatingPointType& f) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, bool>::type { return u.operator!=(uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(f)); }
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator> (const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const FloatingPointType& f) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, bool>::type { return u.operator> (uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(f)); }
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator< (const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const FloatingPointType& f) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, bool>::type { return u.operator< (uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(f)); }
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator>=(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const FloatingPointType& f) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, bool>::type { return u.operator>=(uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(f)); }
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator<=(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& u, const FloatingPointType& f) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, bool>::type { return u.operator<=(uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(f)); }

  // Non-member comparison functions of (FloatingPointType cmp uintwide_t).
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator==(const FloatingPointType& f, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, bool>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(f).operator==(v); }
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator!=(const FloatingPointType& f, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, bool>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(f).operator!=(v); }
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator> (const FloatingPointType& f, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, bool>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(f).operator> (v); }
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator< (const FloatingPointType& f, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, bool>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(f).operator< (v); }
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator>=(const FloatingPointType& f, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, bool>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(f).operator>=(v); }
  template<typename FloatingPointType, const size_t Width2, typename LimbType, typename AllocatorType, const bool IsSigned> constexpr auto operator<=(const FloatingPointType& f, const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& v) -> typename std::enable_if<std::is_floating_point<FloatingPointType>::value, bool>::type { return uintwide_t<Width2, LimbType, AllocatorType, IsSigned>(f).operator<=(v); }
  #endif // !defined(WIDE_INTEGER_DISABLE_FLOAT_INTEROP)

  #if !defined(WIDE_INTEGER_DISABLE_IOSTREAM)

  // I/O streaming functions.
  template<typename char_type,
           typename traits_type,
           const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  auto operator<<(std::basic_ostream<char_type, traits_type>& out,
                  const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& x) -> std::basic_ostream<char_type, traits_type>&
  {
    std::basic_ostringstream<char_type, traits_type> ostr;

    const std::ios::fmtflags my_flags = out.flags();

    const bool show_pos     = ((my_flags & std::ios::showpos)   == std::ios::showpos);
    const bool show_base    = ((my_flags & std::ios::showbase)  == std::ios::showbase);
    const bool is_uppercase = ((my_flags & std::ios::uppercase) == std::ios::uppercase);

    std::uint_fast8_t base_rep { };

    if     ((my_flags & std::ios::oct) == std::ios::oct) { base_rep = UINT8_C( 8); }
    else if((my_flags & std::ios::hex) == std::ios::hex) { base_rep = UINT8_C(16); }
    else                                                 { base_rep = UINT8_C(10); }

    const auto field_width = static_cast<unsigned_fast_type>(out.width());
    const auto fill_char   = static_cast<char>(out.fill());

    using local_wide_integer_type = uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;

    if(base_rep == UINT8_C(8))
    {
      using string_storage_oct_type =
        typename std::conditional
          <local_wide_integer_type::my_width2 <= static_cast<size_t>(UINT32_C(2048)),
            detail::fixed_static_array <char,
                                        local_wide_integer_type::wr_string_max_buffer_size_oct>,
            detail::fixed_dynamic_array<char,
                                        local_wide_integer_type::wr_string_max_buffer_size_oct,
                                        typename std::allocator_traits<typename std::conditional<std::is_same<AllocatorType, void>::value,
                                                                                                std::allocator<void>,
                                                                                                AllocatorType>::type>::template rebind_alloc<typename local_wide_integer_type::limb_type>>
          >::type;

      // TBD: There is redundant storage of this kind both here
      // in this subroutine as well as in the wr_string method.
      string_storage_oct_type str_result;

      str_result.fill(static_cast<char>('\0'));

      x.wr_string(str_result.data(), base_rep, show_base, show_pos, is_uppercase, field_width, fill_char);

      static_cast<void>(ostr << str_result.data());
    }
    else if(base_rep == UINT8_C(10))
    {
      using string_storage_dec_type =
        typename std::conditional
          <local_wide_integer_type::my_width2 <= static_cast<size_t>(UINT32_C(2048)),
            detail::fixed_static_array <char,
                                        local_wide_integer_type::wr_string_max_buffer_size_dec>,
            detail::fixed_dynamic_array<char,
                                        local_wide_integer_type::wr_string_max_buffer_size_dec,
                                        typename std::allocator_traits<typename std::conditional<std::is_same<AllocatorType, void>::value,
                                                                                                std::allocator<void>,
                                                                                                AllocatorType>::type>::template rebind_alloc<typename local_wide_integer_type::limb_type>>
          >::type;

      // TBD: There is redundant storage of this kind both here
      // in this subroutine as well as in the wr_string method.
      string_storage_dec_type str_result;

      str_result.fill(static_cast<char>('\0'));

      x.wr_string(str_result.data(), base_rep, show_base, show_pos, is_uppercase, field_width, fill_char);

      static_cast<void>(ostr << str_result.data());
    }
    else if(base_rep == UINT8_C(16))
    {
      using string_storage_hex_type =
        typename std::conditional
          <local_wide_integer_type::my_width2 <= static_cast<size_t>(UINT32_C(2048)),
            detail::fixed_static_array <char,
                                        local_wide_integer_type::wr_string_max_buffer_size_hex>,
            detail::fixed_dynamic_array<char,
                                        local_wide_integer_type::wr_string_max_buffer_size_hex,
                                        typename std::allocator_traits<typename std::conditional<std::is_same<AllocatorType, void>::value,
                                                                                                std::allocator<void>,
                                                                                                AllocatorType>::type>::template rebind_alloc<typename local_wide_integer_type::limb_type>>
          >::type;

      // TBD: There is redundant storage of this kind both here
      // in this subroutine as well as in the wr_string method.
      string_storage_hex_type str_result;

      str_result.fill(static_cast<char>('\0'));

      x.wr_string(str_result.data(), base_rep, show_base, show_pos, is_uppercase, field_width, fill_char);

      static_cast<void>(ostr << str_result.data());
    }

    return (out << ostr.str());
  }

  template<typename char_type,
           typename traits_type,
           const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  auto operator>>(std::basic_istream<char_type, traits_type>& in,
                  uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& x) -> std::basic_istream<char_type, traits_type>&
  {
    std::string str_in;

    in >> str_in;

    using local_wide_integer_type = uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;

    x = local_wide_integer_type(str_in.c_str());

    return in;
  }

  #endif // !defined(WIDE_INTEGER_DISABLE_IOSTREAM)

  #if(__cplusplus >= 201703L)
  } // namespace math::wide_integer
  #else
  } // namespace wide_integer
  } // namespace math
  #endif

  // Implement various number-theoretical tools.

  #if(__cplusplus >= 201703L)
  namespace math::wide_integer {
  #else
  namespace math { namespace wide_integer { // NOLINT(modernize-concat-nested-namespaces)
  #endif

  namespace detail {

  #if !defined(WIDE_INTEGER_DISABLE_FLOAT_INTEROP)
  namespace my_own {

  template<typename FloatingPointType> WIDE_INTEGER_CONSTEXPR auto frexp(FloatingPointType x, int* expptr) -> typename std::enable_if<((std::is_floating_point<FloatingPointType>::value) && (std::numeric_limits<FloatingPointType>::is_iec559)), FloatingPointType>::type
  {
    using local_floating_point_type = FloatingPointType;

    const bool x_is_neg = (x < static_cast<local_floating_point_type>(0.0L));

    local_floating_point_type f = (x_is_neg ? -x : x);

    int e2 = 0;

    constexpr long double two_pow32 =
      static_cast<long double>(0x10000) * static_cast<long double>(0x10000);

    while(f >= static_cast<local_floating_point_type>(two_pow32)) // NOLINT(altera-id-dependent-backward-branch)
    {
      // TBD: Maybe optimize this exponent reduction
      // with a more clever kind of binary searching.

      f   = static_cast<local_floating_point_type>(f / static_cast<local_floating_point_type>(two_pow32));
      e2 += static_cast<int>(INT32_C(32));
    }

    constexpr long double one_ldbl(1.0L);

    while(f >= static_cast<local_floating_point_type>(one_ldbl)) // NOLINT(altera-id-dependent-backward-branch)
    {
      constexpr long double two_ldbl(2.0L);

      f = static_cast<local_floating_point_type>(f / static_cast<local_floating_point_type>(two_ldbl));

      ++e2;
    }

    if(expptr != nullptr)
    {
      *expptr = e2;
    }

    return ((!x_is_neg) ? f : -f);
  }

  template<typename FloatingPointType> WIDE_INTEGER_CONSTEXPR auto frexp(FloatingPointType x, int* expptr) -> typename std::enable_if<((std::is_floating_point<FloatingPointType>::value) && (!std::numeric_limits<FloatingPointType>::is_iec559)), FloatingPointType>::type
  {
    using std::frexp;

    return frexp(x, expptr);
  }

  template<typename FloatingPointType> WIDE_INTEGER_CONSTEXPR auto isfinite(FloatingPointType x) -> typename std::enable_if<((std::is_floating_point<FloatingPointType>::value) && (std::numeric_limits<FloatingPointType>::is_iec559)), bool>::type
  {
    using local_floating_point_type = FloatingPointType;

    bool x_is_finite = true;

    const bool x_is_nan = (x != x);

    if(x_is_nan)
    {
      x_is_finite = false;
    }
    else
    {
      const bool x_is_inf_pos = (x > (std::numeric_limits<local_floating_point_type>::max)());
      const bool x_is_inf_neg = (x < (std::numeric_limits<local_floating_point_type>::lowest)());

      if(x_is_inf_pos || x_is_inf_neg)
      {
        x_is_finite = false;
      }
    }

    return x_is_finite;
  }

  template<typename FloatingPointType> WIDE_INTEGER_CONSTEXPR auto isfinite(FloatingPointType x) -> typename std::enable_if<((std::is_floating_point<FloatingPointType>::value) && (!std::numeric_limits<FloatingPointType>::is_iec559)), bool>::type
  {
    using std::isfinite;

    return isfinite(x);
  }
  } // namespace my_own
  #endif // !defined(WIDE_INTEGER_DISABLE_FLOAT_INTEROP)

  template<typename UnsignedIntegralType>
  inline WIDE_INTEGER_CONSTEXPR auto lsb_helper(const UnsignedIntegralType& u) -> unsigned_fast_type
  {
    // Compile-time checks.
    static_assert((   (std::is_integral<UnsignedIntegralType>::value)
                   && (std::is_unsigned<UnsignedIntegralType>::value)),
                   "Error: Please check the characteristics of UnsignedIntegralType");

    unsigned_fast_type result = 0U;

    UnsignedIntegralType mask(u);

    // This assumes that at least one bit is set.
    // Otherwise saturation of the index will occur.

    // Naive and basic LSB search.
    // TBD: This could be improved with a binary search
    // on the lowest bit position of the fundamental type.
    while(static_cast<std::uint_fast8_t>(static_cast<std::uint_fast8_t>(mask) & UINT8_C(1)) == UINT8_C(0)) // NOLINT(hicpp-signed-bitwise,altera-id-dependent-backward-branch)
    {
      mask >>= 1U;

      ++result;
    }

    return result;
  }

  template<typename UnsignedIntegralType>
  inline WIDE_INTEGER_CONSTEXPR auto msb_helper(const UnsignedIntegralType& u) -> unsigned_fast_type
  {
    // Compile-time checks.
    static_assert((   (std::is_integral<UnsignedIntegralType>::value)
                   && (std::is_unsigned<UnsignedIntegralType>::value)),
                   "Error: Please check the characteristics of UnsignedIntegralType");

    using local_unsigned_integral_type = UnsignedIntegralType;

    signed_fast_type i { };

    // TBD: This could potentially be improved with a binary
    // search for the highest bit position in the type.

    for(i = static_cast<signed_fast_type>(std::numeric_limits<local_unsigned_integral_type>::digits - 1); i >= 0; --i)
    {
      if((u & static_cast<local_unsigned_integral_type>(static_cast<local_unsigned_integral_type>(1U) << i)) != 0U)
      {
        break;
      }
    }

    return static_cast<unsigned_fast_type>((std::max)(static_cast<signed_fast_type>(0), i));
  }

  template<>
  inline WIDE_INTEGER_CONSTEXPR auto msb_helper<std::uint32_t>(const std::uint32_t& u) -> unsigned_fast_type
  {
    auto r = static_cast<unsigned_fast_type>(0U);
    auto x = static_cast<std::uint_fast32_t>(u);

    // Use O(log2[N]) binary-halving in an unrolled loop to find the msb.
    if((x & UINT32_C(0xFFFF0000)) != UINT32_C(0)) { x = static_cast<std::uint_fast32_t>(x >> static_cast<unsigned>(UINT8_C(16))); r = static_cast<unsigned_fast_type>(r | UINT32_C(16)); }
    if((x & UINT32_C(0x0000FF00)) != UINT32_C(0)) { x = static_cast<std::uint_fast32_t>(x >> static_cast<unsigned>(UINT8_C( 8))); r = static_cast<unsigned_fast_type>(r | UINT32_C( 8)); }
    if((x & UINT32_C(0x000000F0)) != UINT32_C(0)) { x = static_cast<std::uint_fast32_t>(x >> static_cast<unsigned>(UINT8_C( 4))); r = static_cast<unsigned_fast_type>(r | UINT32_C( 4)); }
    if((x & UINT32_C(0x0000000C)) != UINT32_C(0)) { x = static_cast<std::uint_fast32_t>(x >> static_cast<unsigned>(UINT8_C( 2))); r = static_cast<unsigned_fast_type>(r | UINT32_C( 2)); }
    if((x & UINT32_C(0x00000002)) != UINT32_C(0)) {                                                                               r = static_cast<unsigned_fast_type>(r | UINT32_C( 1)); }

    return r;
  }

  template<>
  inline WIDE_INTEGER_CONSTEXPR auto msb_helper<std::uint16_t>(const std::uint16_t& u) -> unsigned_fast_type
  {
    auto r = static_cast<unsigned_fast_type>(0U);
    auto x = static_cast<std::uint_fast16_t>(u);

    // Use O(log2[N]) binary-halving in an unrolled loop to find the msb.
    if(static_cast<std::uint_fast16_t>(static_cast<std::uint_fast32_t>(x) & UINT32_C(0xFF00)) != UINT16_C(0)) { x = static_cast<std::uint_fast16_t>(x >> static_cast<unsigned>(UINT8_C(8))); r = static_cast<unsigned_fast_type>(r | UINT32_C(8)); }
    if(static_cast<std::uint_fast16_t>(static_cast<std::uint_fast32_t>(x) & UINT32_C(0x00F0)) != UINT16_C(0)) { x = static_cast<std::uint_fast16_t>(x >> static_cast<unsigned>(UINT8_C(4))); r = static_cast<unsigned_fast_type>(r | UINT32_C(4)); }
    if(static_cast<std::uint_fast16_t>(static_cast<std::uint_fast32_t>(x) & UINT32_C(0x000C)) != UINT16_C(0)) { x = static_cast<std::uint_fast16_t>(x >> static_cast<unsigned>(UINT8_C(2))); r = static_cast<unsigned_fast_type>(r | UINT32_C(2)); }
    if(static_cast<std::uint_fast16_t>(static_cast<std::uint_fast32_t>(x) & UINT32_C(0x0002)) != UINT16_C(0)) {                                                                              r = static_cast<unsigned_fast_type>(r | UINT32_C(1)); }

    return r;
  }

  template<>
  inline WIDE_INTEGER_CONSTEXPR auto msb_helper<std::uint8_t>(const std::uint8_t& u) -> unsigned_fast_type
  {
    auto r = static_cast<unsigned_fast_type>(0U);
    auto x = static_cast<std::uint_fast8_t>(u);

    // Use O(log2[N]) binary-halving in an unrolled loop to find the msb.
    if(static_cast<std::uint_fast8_t>(static_cast<std::uint_fast32_t>(x) & UINT32_C(0xF0)) != UINT8_C(0)) { x = static_cast<std::uint_fast8_t>(x >> static_cast<unsigned>(UINT8_C(4))); r = static_cast<unsigned_fast_type>(r | UINT32_C(4)); }
    if(static_cast<std::uint_fast8_t>(static_cast<std::uint_fast32_t>(x) & UINT32_C(0x0C)) != UINT8_C(0)) { x = static_cast<std::uint_fast8_t>(x >> static_cast<unsigned>(UINT8_C(2))); r = static_cast<unsigned_fast_type>(r | UINT32_C(2)); }
    if(static_cast<std::uint_fast8_t>(static_cast<std::uint_fast32_t>(x) & UINT32_C(0x02)) != UINT8_C(0)) {                                                                             r = static_cast<unsigned_fast_type>(r | UINT32_C(1)); }

    return r;
  }

  } // namespace detail

  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  WIDE_INTEGER_CONSTEXPR void swap(uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& x,
                                   uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& y)
  {
    if(&x != &y)
    {
      using local_wide_integer_type = uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;

      const local_wide_integer_type tmp_x(x);

      x = y;
      y = tmp_x;
    }
  }

  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  inline WIDE_INTEGER_CONSTEXPR auto lsb(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& x) -> unsigned_fast_type
  {
    // Calculate the position of the least-significant bit.
    // Use a linear search starting from the least significant limbs.

    using local_wide_integer_type = uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;
    using local_value_type        = typename local_wide_integer_type::representation_type::value_type;

    auto bpos   = static_cast<unsigned_fast_type>(0U);
    auto offset = static_cast<unsigned_fast_type>(0U);

    for(auto it = x.crepresentation().cbegin(); it != x.crepresentation().cend(); ++it, ++offset) // NOLINT(llvm-qualified-auto,readability-qualified-auto,altera-id-dependent-backward-branch)
    {
      const auto vi = static_cast<local_value_type>(*it & (std::numeric_limits<local_value_type>::max)());

      if(vi != static_cast<local_value_type>(0U))
      {
        bpos = static_cast<unsigned_fast_type>
               (
                   detail::lsb_helper(*it)
                 + static_cast<unsigned_fast_type>(static_cast<unsigned_fast_type>(std::numeric_limits<local_value_type>::digits) * offset)
               );

        break;
      }
    }

    return bpos;
  }

  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  WIDE_INTEGER_CONSTEXPR auto msb(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& x) -> unsigned_fast_type
  {
    // Calculate the position of the most-significant bit.
    // Use a linear search starting from the most significant limbs.

    using local_wide_integer_type = uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;
    using local_value_type        = typename local_wide_integer_type::representation_type::value_type;

    auto bpos   = static_cast<unsigned_fast_type>(0U);
    auto offset = static_cast<unsigned_fast_type>(x.crepresentation().size() - 1U);

    for(auto ri = x.crepresentation().crbegin(); ri != x.crepresentation().crend(); ++ri, --offset) // NOLINT(altera-id-dependent-backward-branch)
    {
      const auto vr = static_cast<local_value_type>(*ri & (std::numeric_limits<local_value_type>::max)());

      if(vr != static_cast<local_value_type>(0U))
      {
        bpos = static_cast<unsigned_fast_type>
               (
                    detail::msb_helper(*ri)
                  + static_cast<unsigned_fast_type>(static_cast<unsigned_fast_type>(std::numeric_limits<local_value_type>::digits) * offset)
               );

        break;
      }
    }

    return bpos;
  }

  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  constexpr auto abs(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& x) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned>
  {
    using local_wide_integer_type = uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;

    return ((!local_wide_integer_type::is_neg(x)) ? x : -x);
  }

  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  WIDE_INTEGER_CONSTEXPR auto sqrt(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& m) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned>
  {
    // Calculate the square root.

    using local_wide_integer_type = uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;

    local_wide_integer_type s;

    if(m.is_zero() || local_wide_integer_type::is_neg(m))
    {
      s = local_wide_integer_type(static_cast<std::uint_fast8_t>(0U));
    }
    else
    {
      // Obtain the initial guess via algorithms
      // involving the position of the msb.
      const unsigned_fast_type msb_pos = msb(m);

      // Obtain the initial value.
      const unsigned_fast_type left_shift_amount =
        ((static_cast<unsigned_fast_type>(msb_pos % 2U) == 0U)
          ? static_cast<unsigned_fast_type>(1U + static_cast<unsigned_fast_type>((msb_pos + 0U) / 2U))
          : static_cast<unsigned_fast_type>(1U + static_cast<unsigned_fast_type>((msb_pos + 1U) / 2U)));

      local_wide_integer_type
      u
      (
        local_wide_integer_type(static_cast<std::uint_fast8_t>(1U)) << left_shift_amount
      );

      // Perform the iteration for the square root.
      // See Algorithm 1.13 SqrtInt, Sect. 1.5.1
      // in R.P. Brent and Paul Zimmermann, "Modern Computer Arithmetic",
      // Cambridge University Press, 2011.

      for(auto i = static_cast<unsigned_fast_type>(0U); i < static_cast<unsigned_fast_type>(UINT8_C(64)); ++i)
      {
        s = u;

        u = (s + (m / s)) >> 1;

        if(u >= s)
        {
          break;
        }
      }
    }

    return s;
  }

  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  WIDE_INTEGER_CONSTEXPR auto cbrt(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& m) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned> // NOLINT(misc-no-recursion)
  {
    // Calculate the cube root.

    using local_wide_integer_type = uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;

    local_wide_integer_type s;

    if(local_wide_integer_type::is_neg(m))
    {
      s = -cbrt(-m);
    }
    else if(m.is_zero())
    {
      s = local_wide_integer_type(static_cast<std::uint_fast8_t>(0U));
    }
    else
    {
      // Obtain the initial guess via algorithms
      // involving the position of the msb.
      const unsigned_fast_type msb_pos = msb(m);

      // Obtain the initial value.
      const auto msb_pos_mod_3 = static_cast<unsigned_fast_type>(msb_pos % UINT8_C(3));

      const unsigned_fast_type left_shift_amount =
        ((msb_pos_mod_3 == 0U)
          ? static_cast<unsigned_fast_type>(1U + static_cast<unsigned_fast_type>((msb_pos +                  0U ) / 3U))
          : static_cast<unsigned_fast_type>(1U + static_cast<unsigned_fast_type>((msb_pos + (3U - msb_pos_mod_3)) / 3U)));

      local_wide_integer_type u(local_wide_integer_type(static_cast<std::uint_fast8_t>(1U)) << left_shift_amount);

      // Perform the iteration for the k'th root.
      // See Algorithm 1.14 RootInt, Sect. 1.5.2
      // in R.P. Brent and Paul Zimmermann, "Modern Computer Arithmetic",
      // Cambridge University Press, 2011.

      const auto three_minus_one = static_cast<unsigned_fast_type>(3U - 1U);

      for(auto i = static_cast<unsigned_fast_type>(0U); i < static_cast<unsigned_fast_type>(UINT8_C(64)); ++i)
      {
        s = u;

        local_wide_integer_type m_over_s_pow_3_minus_one = m;

        for(unsigned_fast_type j = 0U; j < 3U - 1U; ++j)
        {
          // Use a loop here to divide by s^(3 - 1) because
          // without a loop, s^(3 - 1) is likely to overflow.

          m_over_s_pow_3_minus_one /= s;
        }

        u = ((s * three_minus_one) + m_over_s_pow_3_minus_one) / 3U;

        if(u >= s)
        {
          break;
        }
      }
    }

    return s;
  }

  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  WIDE_INTEGER_CONSTEXPR auto rootk(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& m, const std::uint_fast8_t k) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned>
  {
    // Calculate the k'th root.

    using local_wide_integer_type = uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;

    local_wide_integer_type s;

    if(k < 2U)
    {
      s = m;
    }
    else if(k == 2U)
    {
      s = sqrt(m);
    }
    else if(k == 3U)
    {
      s = cbrt(m);
    }
    else
    {
      if(m.is_zero() || local_wide_integer_type::is_neg(m))
      {
        s = local_wide_integer_type(static_cast<std::uint_fast8_t>(0U));
      }
      else
      {
        // Obtain the initial guess via algorithms
        // involving the position of the msb.
        const unsigned_fast_type msb_pos = msb(m);

        // Obtain the initial value.
        const unsigned_fast_type msb_pos_mod_k = msb_pos % k;

        const unsigned_fast_type left_shift_amount =
          ((msb_pos_mod_k == 0U)
            ? 1U + static_cast<unsigned_fast_type>((msb_pos +                 0U ) / k)
            : 1U + static_cast<unsigned_fast_type>((msb_pos + (k - msb_pos_mod_k)) / k));

        local_wide_integer_type u(local_wide_integer_type(static_cast<std::uint_fast8_t>(1U)) << left_shift_amount);

        // Perform the iteration for the k'th root.
        // See Algorithm 1.14 RootInt, Sect. 1.5.2
        // in R.P. Brent and Paul Zimmermann, "Modern Computer Arithmetic",
        // Cambridge University Press, 2011.

        const unsigned_fast_type k_minus_one(k - 1U);

        for(auto i = static_cast<unsigned_fast_type>(0U); i < static_cast<unsigned_fast_type>(UINT8_C(64)); ++i)
        {
          s = u;

          local_wide_integer_type m_over_s_pow_k_minus_one = m;

          for(unsigned_fast_type j = 0U; j < k - 1U; ++j)
          {
            // Use a loop here to divide by s^(k - 1) because
            // without a loop, s^(k - 1) is likely to overflow.

            m_over_s_pow_k_minus_one /= s;
          }

          u = ((s * k_minus_one) + m_over_s_pow_k_minus_one) / k;

          if(u >= s)
          {
            break;
          }
        }
      }
    }

    return s;
  }

  template<typename OtherIntegralTypeP,
           const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  WIDE_INTEGER_CONSTEXPR auto pow(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& b, const OtherIntegralTypeP& p) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned>
  {
    // Calculate (b ^ p).
    using local_wide_integer_type = uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;
    using local_limb_type         = typename local_wide_integer_type::limb_type;

    local_wide_integer_type result;
    auto p0(static_cast<local_limb_type>(p));

    if((p0 == 0U) && (p == OtherIntegralTypeP(0)))
    {
      result = local_wide_integer_type(static_cast<std::uint8_t>(1U));
    }
    else if((p0 == 1U) && (p == OtherIntegralTypeP(1)))
    {
      result = b;
    }
    else if((p0 == 2U) && (p == OtherIntegralTypeP(2)))
    {
      result  = b;
      result *= b;
    }
    else
    {
      result = local_wide_integer_type(static_cast<std::uint8_t>(1U));

      local_wide_integer_type y      (b);
      local_wide_integer_type p_local(p);

      while(((p0 = static_cast<local_limb_type>(p_local)) != 0U) || (p_local != 0U)) // NOLINT(altera-id-dependent-backward-branch)
      {
        if((p0 & 1U) != 0U)
        {
          result *= y;
        }

        y *= y;

        p_local >>= 1;
      }
    }

    return result;
  }

  template<typename OtherIntegralTypeP,
           typename OtherIntegralTypeM,
           const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  WIDE_INTEGER_CONSTEXPR auto powm(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& b,
                                   const OtherIntegralTypeP& p,
                                   const OtherIntegralTypeM& m) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned>
  {
    // Calculate (b ^ p) % m.

    using local_normal_width_type = uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;
    using local_double_width_type = typename local_normal_width_type::double_width_type;
    using local_limb_type         = typename local_normal_width_type::limb_type;

          local_normal_width_type result;
          local_double_width_type y      (b);
    const local_double_width_type m_local(m);
          auto                    p0     (static_cast<local_limb_type>(p));

    if((p0 == 0U) && (p == OtherIntegralTypeP(0)))
    {
      result = local_normal_width_type((m != 1U) ? static_cast<std::uint8_t>(1U) : static_cast<std::uint8_t>(0U));
    }
    else if((p0 == 1U) && (p == OtherIntegralTypeP(1)))
    {
      result = b % m;
    }
    else if((p0 == 2U) && (p == OtherIntegralTypeP(2)))
    {
      y *= y;
      y %= m_local;

      result = local_normal_width_type(y);
    }
    else
    {
      local_double_width_type x      (static_cast<std::uint8_t>(1U));
      OtherIntegralTypeP      p_local(p);

      while(((p0 = static_cast<local_limb_type>(p_local)) != 0U) || (p_local != 0U)) // NOLINT(altera-id-dependent-backward-branch)
      {
        if((p0 & 1U) != 0U)
        {
          x *= y;
          x %= m_local;
        }

        y *= y;
        y %= m_local;

        p_local >>= 1U; // NOLINT(hicpp-signed-bitwise)
      }

      result = local_normal_width_type(x);
    }

    return result;
  }

  namespace detail {

  template<typename UnsignedShortType>
  WIDE_INTEGER_CONSTEXPR auto integer_gcd_reduce_short(UnsignedShortType u, UnsignedShortType v) -> UnsignedShortType
  {
    // This implementation of GCD reduction is based on an
    // adaptation of existing code from Boost.Multiprecision.

    for(;;)
    {
      if(u > v)
      {
        std::swap(u, v);
      }

      if(u == v)
      {
        break;
      }

      v  -= u;
      v >>= detail::lsb_helper(v);
    }

    return u;
  }

  template<typename UnsignedLargeType>
  WIDE_INTEGER_CONSTEXPR auto integer_gcd_reduce_large(UnsignedLargeType u, UnsignedLargeType v) -> UnsignedLargeType
  {
    // This implementation of GCD reduction is based on an
    // adaptation of existing code from Boost.Multiprecision.

    using local_ularge_type = UnsignedLargeType;
    using local_ushort_type = typename detail::uint_type_helper<static_cast<size_t>(std::numeric_limits<local_ularge_type>::digits / 2)>::exact_unsigned_type;

    for(;;)
    {
      if(u > v)
      {
        std::swap(u, v);
      }

      if(u == v)
      {
        break;
      }

      if(v <= static_cast<local_ularge_type>((std::numeric_limits<local_ushort_type>::max)()))
      {
        u = integer_gcd_reduce_short(static_cast<local_ushort_type>(v),
                                     static_cast<local_ushort_type>(u));

        break;
      }

      v -= u;

      while(static_cast<std::uint_fast8_t>(static_cast<std::uint_fast8_t>(v) & UINT8_C(1)) == UINT8_C(0)) // NOLINT(hicpp-signed-bitwise,altera-id-dependent-backward-branch)
      {
        v >>= 1U;
      }
    }

    return u;
  }

  } // namespace detail

  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  WIDE_INTEGER_CONSTEXPR auto gcd(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& a, // NOLINT(readability-function-cognitive-complexity,bugprone-easily-swappable-parameters)
                                  const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& b) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned>
  {
    // This implementation of GCD is an adaptation
    // of existing code from Boost.Multiprecision.

    using local_wide_integer_type = uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;
    using local_ushort_type       = typename local_wide_integer_type::limb_type;
    using local_ularge_type       = typename local_wide_integer_type::double_limb_type;

    const bool u_is_neg = local_wide_integer_type::is_neg(a);
    const bool v_is_neg = local_wide_integer_type::is_neg(b);

    local_wide_integer_type u((!u_is_neg) ? a : -a);
    local_wide_integer_type v((!v_is_neg) ? b : -b);

    local_wide_integer_type result;

    if(u == v)
    {
      // This handles cases having (u = v) and also (u = v = 0).
      result = u;
    }

    if((static_cast<local_ushort_type>(v) == 0U) && (v == 0U))
    {
      // This handles cases having (v = 0) with (u != 0).
      result = u;
    }

    if((static_cast<local_ushort_type>(u) == 0U) && (u == 0U))
    {
      // This handles cases having (u = 0) with (v != 0).
      result = v;
    }
    else
    {
      // Now we handle cases having (u != 0) and (v != 0).

      // Let shift := lg K, where K is the greatest
      // power of 2 dividing both u and v.

      const unsigned_fast_type u_shift = lsb(u);
      const unsigned_fast_type v_shift = lsb(v);

      const unsigned_fast_type left_shift_amount = (std::min)(u_shift, v_shift);

      u >>= u_shift;
      v >>= v_shift;

      for(;;)
      {
        // Now u and v are both odd, so diff(u, v) is even.
        // Let u = min(u, v), v = diff(u, v) / 2.

        if(u > v)
        {
          swap(u, v);
        }

        if(u == v)
        {
          break;
        }

        if(v <= (std::numeric_limits<local_ularge_type>::max)())
        {
          if(v <= (std::numeric_limits<local_ushort_type>::max)())
          {
            u = detail::integer_gcd_reduce_short(*(v.crepresentation().cbegin() + 0U),
                                                 *(u.crepresentation().cbegin() + 0U));
          }
          else
          {
            const auto my_v_hi =
              static_cast<local_ushort_type>
              (
                (v.crepresentation().size() >= static_cast<typename local_wide_integer_type::representation_type::size_type>(2U))
                  ? static_cast<local_ushort_type>(*(v.crepresentation().cbegin() + 1U))
                  : static_cast<local_ushort_type>(0U)
              );

            const auto my_u_hi =
              static_cast<local_ushort_type>
              (
                (u.crepresentation().size() >= static_cast<typename local_wide_integer_type::representation_type::size_type>(2U))
                  ? static_cast<local_ushort_type>(*(u.crepresentation().cbegin() + 1U))
                  : static_cast<local_ushort_type>(0U)
              );

            const local_ularge_type v_large = detail::make_large(*(v.crepresentation().cbegin() + 0U), my_v_hi);
            const local_ularge_type u_large = detail::make_large(*(u.crepresentation().cbegin() + 0U), my_u_hi);

            u = detail::integer_gcd_reduce_large(v_large, u_large);
          }

          break;
        }

        v  -= u;
        v >>= lsb(v);
      }

      result = (u << left_shift_amount);
    }

    return ((u_is_neg == v_is_neg) ? result : -result);
  }

  template<typename UnsignedShortType>
  WIDE_INTEGER_CONSTEXPR auto gcd(const UnsignedShortType& u, const UnsignedShortType& v) -> typename std::enable_if<(   (std::is_integral<UnsignedShortType>::value)
                                                                                                                      && (std::is_unsigned<UnsignedShortType>::value)), UnsignedShortType>::type
  {
    UnsignedShortType result;

    if(u > v)
    {
      result = gcd(v, u);
    }

    if(u == v)
    {
      // This handles cases having (u = v) and also (u = v = 0).
      result = u;
    }

    if(v == 0U)
    {
      // This handles cases having (v = 0) with (u != 0).
      result = u;
    }

    if(u == 0U)
    {
      // This handles cases having (u = 0) with (v != 0).
      result = v;
    }
    else
    {
      result = detail::integer_gcd_reduce_short(u, v);
    }

    return result;
  }

  namespace detail {

  template<typename IntegerType>
  WIDE_INTEGER_CONSTEXPR auto lcm_impl(const IntegerType& a, const IntegerType& b) -> IntegerType
  {
    using local_integer_type = IntegerType;

    using std::abs;

    const local_integer_type ap = abs(a);
    const local_integer_type bp = abs(b);

    const bool a_is_greater_than_b = (ap > bp);

    const local_integer_type gcd_of_ab = gcd(a, b);

    return (a_is_greater_than_b ? ap * (bp / gcd_of_ab)
                                : bp * (ap / gcd_of_ab));
  }

  } // namespace detail

  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  WIDE_INTEGER_CONSTEXPR auto lcm(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& a,
                                  const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& b) -> uintwide_t<Width2, LimbType, AllocatorType, IsSigned>
  {
    return detail::lcm_impl(a, b);
  }

  template<typename UnsignedShortType>
  WIDE_INTEGER_CONSTEXPR auto lcm(const UnsignedShortType& a, const UnsignedShortType& b) -> typename std::enable_if<(   (std::is_integral<UnsignedShortType>::value)
                                                                                                                      && (std::is_unsigned<UnsignedShortType>::value)), UnsignedShortType>::type
  {
    return detail::lcm_impl(a, b);
  }

  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  class uniform_int_distribution
  {
  public:
    using result_type = uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;

    struct param_type
    {
    public:
      explicit param_type(result_type p_a = (std::numeric_limits<result_type>::min)(),
                          result_type p_b = (std::numeric_limits<result_type>::max)())
        : param_a(std::move(p_a)),
          param_b(std::move(p_b)) { }

      ~param_type() = default;

      param_type(const param_type& other_params) : param_a(other_params.param_a),
                                                   param_b(other_params.param_b) { }

      param_type(param_type&& other_params) noexcept : param_a(other_params.param_a),
                                                       param_b(other_params.param_b) { }

      auto operator=(const param_type& other_params) -> param_type&
      {
        if(this != &other_params)
        {
          param_a = other_params.param_a;
          param_b = other_params.param_b;
        }

        return *this;
      }

      auto operator=(param_type&& other_params) noexcept -> param_type&
      {
        param_a = other_params.param_a;
        param_b = other_params.param_b;

        return *this;
      }

      WIDE_INTEGER_NODISCARD constexpr auto get_a() const -> result_type { return param_a; }
      WIDE_INTEGER_NODISCARD constexpr auto get_b() const -> result_type { return param_b; }

      void set_a(const result_type& p_a) { param_a = p_a; }
      void set_b(const result_type& p_b) { param_b = p_b; }

    private:
      result_type param_a; // NOLINT(readability-identifier-naming)
      result_type param_b; // NOLINT(readability-identifier-naming)

      friend inline constexpr auto operator==(const param_type& lhs,
                                              const param_type& rhs) -> bool
      {
        return (   (lhs.param_a == rhs.param_a)
                && (lhs.param_b == rhs.param_b));
      }

      friend inline constexpr auto operator!=(const param_type& lhs,
                                              const param_type& rhs) -> bool
      {
        return (   (lhs.param_a != rhs.param_a)
                || (lhs.param_b != rhs.param_b));
      }
    };

    uniform_int_distribution() : my_params() { }

    explicit uniform_int_distribution(const result_type& p_a,
                                      const result_type& p_b = (std::numeric_limits<result_type>::max)())
        : my_params(param_type(p_a, p_b)) { }

    explicit uniform_int_distribution(const param_type& other_params)
      : my_params(other_params) { }

    uniform_int_distribution(const uniform_int_distribution& other_distribution) = delete;

    uniform_int_distribution(uniform_int_distribution&& other) noexcept : my_params(other.my_params) { }

    ~uniform_int_distribution() = default;

    auto operator=(const uniform_int_distribution& other) -> uniform_int_distribution&
    {
      if(this != &other)
      {
        my_params = other.my_params;
      }

      return *this;
    }

    auto operator=(uniform_int_distribution&& other) noexcept -> uniform_int_distribution&
    {
      my_params = other.my_params;

      return *this;
    }

    void param(const param_type& new_params)
    {
      my_params = new_params;
    }

    WIDE_INTEGER_NODISCARD auto param() const -> const param_type& { return my_params; }

    WIDE_INTEGER_NODISCARD auto a() const -> result_type { return my_params.get_a(); }
    WIDE_INTEGER_NODISCARD auto b() const -> result_type { return my_params.get_b(); }

    template<typename GeneratorType,
             const int GeneratorResultBits = std::numeric_limits<typename GeneratorType::result_type>::digits>
    WIDE_INTEGER_CONSTEXPR auto operator()(GeneratorType& generator) -> result_type
    {
      return generate<GeneratorType, GeneratorResultBits>
             (
               generator,
               my_params
             );
    }

    template<typename GeneratorType,
             const int GeneratorResultBits = std::numeric_limits<typename GeneratorType::result_type>::digits>
    WIDE_INTEGER_CONSTEXPR auto operator()(      GeneratorType& input_generator,
                                           const param_type&    input_params) -> result_type
    {
      return generate<GeneratorType, GeneratorResultBits>
             (
               input_generator,
               input_params
             );
    }

  private:
    param_type my_params; // NOLINT(readability-identifier-naming)

    template<typename GeneratorType,
             const int GeneratorResultBits = std::numeric_limits<typename GeneratorType::result_type>::digits>
    WIDE_INTEGER_CONSTEXPR auto generate(      GeneratorType& input_generator,
                                         const param_type&    input_params) const -> result_type
    {
      // Generate random numbers r, where a <= r <= b.

      auto result = static_cast<result_type>(static_cast<std::uint8_t>(0U));

      using local_limb_type = typename result_type::limb_type;

      using generator_result_type = typename GeneratorType::result_type;

      constexpr auto digits_generator_result_type = static_cast<std::uint32_t>(GeneratorResultBits);

      static_assert((digits_generator_result_type % UINT32_C(8)) == UINT32_C(0),
                    "Error: Generator result type must have a multiple of 8 bits.");

      constexpr auto digits_limb_ratio = 
        static_cast<std::uint32_t>(std::numeric_limits<local_limb_type>::digits / 8U);

      constexpr auto digits_gtor_ratio = static_cast<std::uint32_t>(digits_generator_result_type / 8U);

      generator_result_type value = generator_result_type();

      auto it = result.representation().begin(); // NOLINT(llvm-qualified-auto,readability-qualified-auto)

      unsigned_fast_type j = 0U;

      while(it != result.representation().end()) // NOLINT(altera-id-dependent-backward-branch)
      {
        if((j % digits_gtor_ratio) == 0U)
        {
          value = input_generator();
        }

        const auto next_byte =
          static_cast<std::uint8_t>(value >> static_cast<unsigned>(static_cast<unsigned_fast_type>(j % digits_gtor_ratio) * static_cast<unsigned_fast_type>(UINT8_C(8))));

        *it =
          static_cast<typename result_type::limb_type>
          (
            *it | static_cast<local_limb_type>(static_cast<local_limb_type>(next_byte) << static_cast<unsigned>(static_cast<unsigned_fast_type>(j % digits_limb_ratio) * static_cast<unsigned_fast_type>(UINT8_C(8))))
          );

        ++j;

        if(static_cast<unsigned_fast_type>(j % digits_limb_ratio) == static_cast<unsigned_fast_type>(0U))
        {
          ++it;
        }
      }

      if(   (input_params.get_a() != (std::numeric_limits<result_type>::min)())
         || (input_params.get_b() != (std::numeric_limits<result_type>::max)()))
      {
        // Note that this restricts the range r to:
        //   r = {[input_generator() % ((b - a) + 1)] + a}

        result_type range(input_params.get_b() - input_params.get_a());

        ++range;

        result %= range;
        result += input_params.get_a();
      }

      return result;
    }
  };

  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  constexpr auto operator==(const uniform_int_distribution<Width2, LimbType, AllocatorType, IsSigned>& lhs,
                            const uniform_int_distribution<Width2, LimbType, AllocatorType, IsSigned>& rhs) -> bool
  {
    return (lhs.param() == rhs.param());
  }

  template<const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  constexpr auto operator!=(const uniform_int_distribution<Width2, LimbType, AllocatorType, IsSigned>& lhs,
                            const uniform_int_distribution<Width2, LimbType, AllocatorType, IsSigned>& rhs) -> bool
  {
    return (lhs.param() != rhs.param());
  }

  template<typename DistributionType,
           typename GeneratorType,
           const size_t Width2,
           typename LimbType,
           typename AllocatorType,
           const bool IsSigned>
  auto miller_rabin(const uintwide_t<Width2, LimbType, AllocatorType, IsSigned>& n, // NOLINT(readability-function-cognitive-complexity)
                    const unsigned_fast_type                                     number_of_trials,
                          DistributionType&                                      distribution,
                          GeneratorType&                                         generator) -> bool
  {
    // This Miller-Rabin primality test is loosely based on
    // an adaptation of some code from Boost.Multiprecision.
    // The Boost.Multiprecision code can be found here:
    // https://www.boost.org/doc/libs/1_76_0/libs/multiprecision/doc/html/boost_multiprecision/tut/primetest.html

    // Note: Some comments in this subroutine use the Wolfram Language(TM).
    // These can be exercised at the web links to WolframAlpha(R) provided

    using local_wide_integer_type = uintwide_t<Width2, LimbType, AllocatorType, IsSigned>;
    using local_limb_type         = typename local_wide_integer_type::limb_type;

    const local_wide_integer_type np((!local_wide_integer_type::is_neg(n)) ? n : -n);

    {
      const auto n0 = static_cast<local_limb_type>(np);

      if((n0 & 1U) == 0U)
      {
        // Not prime because n is even.
        return false;
      }

      if((n0 <= static_cast<local_limb_type>(UINT8_C(227))) && (np <= static_cast<local_limb_type>(UINT8_C(227))))
      {
        if((n0 == static_cast<local_limb_type>(UINT8_C(2))) && (np == static_cast<local_limb_type>(UINT8_C(2))))
        {
          // Trivial special case of (n = 2).
          return true;
        }

        // Exclude pure small primes from 3...227.
        // Table[Prime[i], {i, 2, 49}] =
        // {
        //     3,   5,   7,  11,  13,  17,  19,  23,
        //    29,  31,  37,  41,  43,  47,  53,  59,
        //    61,  67,  71,  73,  79,  83,  89,  97,
        //   101, 103, 107, 109, 113, 127, 131, 137,
        //   139, 149, 151, 157, 163, 167, 173, 179,
        //   181, 191, 193, 197, 199, 211, 223, 227
        // }
        // See also:
        // https://www.wolframalpha.com/input/?i=Table%5BPrime%5Bi%5D%2C+%7Bi%2C+2%2C+49%7D%5D

        constexpr std::array<local_limb_type, 48U> small_primes = 
        {{
          UINT8_C(  3), UINT8_C(  5), UINT8_C(  7), UINT8_C( 11), UINT8_C( 13), UINT8_C( 17), UINT8_C( 19), UINT8_C( 23),
          UINT8_C( 29), UINT8_C( 31), UINT8_C( 37), UINT8_C( 41), UINT8_C( 43), UINT8_C( 47), UINT8_C( 53), UINT8_C( 59),
          UINT8_C( 61), UINT8_C( 67), UINT8_C( 71), UINT8_C( 73), UINT8_C( 79), UINT8_C( 83), UINT8_C( 89), UINT8_C( 97),
          UINT8_C(101), UINT8_C(103), UINT8_C(107), UINT8_C(109), UINT8_C(113), UINT8_C(127), UINT8_C(131), UINT8_C(137),
          UINT8_C(139), UINT8_C(149), UINT8_C(151), UINT8_C(157), UINT8_C(163), UINT8_C(167), UINT8_C(173), UINT8_C(179),
          UINT8_C(181), UINT8_C(191), UINT8_C(193), UINT8_C(197), UINT8_C(199), UINT8_C(211), UINT8_C(223), UINT8_C(227)
        }};

        return std::binary_search(small_primes.cbegin(),
                                  small_primes.cend(),
                                  n0);
      }
    }

    // Check small factors.

    // Exclude small prime factors from { 3 ...  53 }.
    // Product[Prime[i], {i, 2, 16}] = 16294579238595022365
    // See also: https://www.wolframalpha.com/input/?i=Product%5BPrime%5Bi%5D%2C+%7Bi%2C+2%2C+16%7D%5D
    {
      constexpr std::uint64_t pp0 = UINT64_C(16294579238595022365);

      const auto m0 = static_cast<std::uint64_t>(np % pp0);

      if(detail::integer_gcd_reduce_large(m0, pp0) != 1U)
      {
        return false;
      }
    }

    // Exclude small prime factors from { 59 ... 101 }.
    // Product[Prime[i], {i, 17, 26}] = 7145393598349078859
    // See also: https://www.wolframalpha.com/input/?i=Product%5BPrime%5Bi%5D%2C+%7Bi%2C+17%2C+26%7D%5D
    {
      constexpr std::uint64_t pp1 = UINT64_C(7145393598349078859);

      const auto m1 = static_cast<std::uint64_t>(np % pp1);

      if(detail::integer_gcd_reduce_large(m1, pp1) != 1U)
      {
        return false;
      }
    }

    // Exclude small prime factors from { 103 ... 149 }.
    // Product[Prime[i], {i, 27, 35}] = 6408001374760705163
    // See also: https://www.wolframalpha.com/input/?i=Product%5BPrime%5Bi%5D%2C+%7Bi%2C+27%2C+35%7D%5D
    {
      constexpr std::uint64_t pp2 = UINT64_C(6408001374760705163);

      const auto m2 = static_cast<std::uint64_t>(np % pp2);

      if(detail::integer_gcd_reduce_large(m2, pp2) != 1U)
      {
        return false;
      }
    }

    // Exclude small prime factors from { 151 ... 191 }.
    // Product[Prime[i], {i, 36, 43}] = 690862709424854779
    // See also: https://www.wolframalpha.com/input/?i=Product%5BPrime%5Bi%5D%2C+%7Bi%2C+36%2C+43%7D%5D
    {
      constexpr std::uint64_t pp3 = UINT64_C(690862709424854779);

      const auto m3 = static_cast<std::uint64_t>(np % pp3);

      if(detail::integer_gcd_reduce_large(m3, pp3) != 1U)
      {
        return false;
      }
    }

    // Exclude small prime factors from { 193 ... 227 }.
    // Product[Prime[i], {i, 44, 49}] = 80814592450549
    // See also: https://www.wolframalpha.com/input/?i=Product%5BPrime%5Bi%5D%2C+%7Bi%2C+44%2C+49%7D%5D
    {
      constexpr std::uint64_t pp4 = UINT64_C(80814592450549);

      const auto m4 = static_cast<std::uint64_t>(np % pp4);

      if(detail::integer_gcd_reduce_large(m4, pp4) != 1U)
      {
        return false;
      }
    }

    const local_wide_integer_type nm1(np - 1U);

    // Since we have already excluded all small factors
    // up to and including 227, n is greater than 227.

    {
      // Perform a single Fermat test which will
      // exclude many non-prime candidates.

      const local_wide_integer_type fn = powm(local_wide_integer_type(static_cast<local_limb_type>(228U)), nm1, np);

      const auto fn0 = static_cast<local_limb_type>(fn);

      if((fn0 != 1U) && (fn != 1U))
      {
        return false;
      }
    }

    const unsigned_fast_type k = lsb(nm1);

    const local_wide_integer_type q = nm1 >> k;

    using local_param_type = typename DistributionType::param_type;

    const local_param_type params(local_wide_integer_type(2U), np - 2U);

    bool is_probably_prime = true;

    auto i = static_cast<unsigned_fast_type>(0U);

    local_wide_integer_type x;
    local_wide_integer_type y;

    // Execute the random trials.
    do
    {
      x = distribution(generator, params);
      y = powm(x, q, np);

      auto j = static_cast<unsigned_fast_type>(0U);

      while(y != nm1) // NOLINT(altera-id-dependent-backward-branch)
      {
        const local_limb_type y0(y);

        if((y0 == 1U) && (y == 1U))
        {
          if(j != 0U)
          {
            is_probably_prime = false;
          }
          else
          {
            break;
          }
        }
        else
        {
          ++j;

          if(j == k)
          {
            is_probably_prime = false;
          }
          else
          {
            y = powm(y, 2U, np);
          }
        }
      }

      ++i;
    }
    while((i < number_of_trials) && is_probably_prime);

    // The prime candidate is probably prime in the sense
    // of the very high probability resulting from Miller-Rabin.
    return is_probably_prime;
  }

  #if(__cplusplus >= 201703L)
  } // namespace math::wide_integer
  #else
  } // namespace wide_integer
  } // namespace math
  #endif

  WIDE_INTEGER_NAMESPACE_END

#endif // UINTWIDE_T_2018_10_02_H
