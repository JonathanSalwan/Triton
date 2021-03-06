#ifndef TRITON_HASH_HPP
#define TRITON_HASH_HPP

#include <triton/tritonTypes.hpp>

namespace triton
{

template<typename T>
class IdentityHash
{
public:
  // KEy is unique and are be returned as is
  T operator()(const T& key) const { return key; }
};

} // end of triton namespace

#endif // End of TRITON_HASH_HPP