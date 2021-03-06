#ifndef TRITON_HASH_HPP
#define TRITON_HASH_HPP

#include <triton/tritonTypes.hpp>

//! The Triton namespace
namespace triton
{
/*!
 *  \addtogroup triton
 *  @{
 */

  /*! \class IdentityHash
   *  \brief This class can be used as a hash function in hash tables containers.
   */
  template<typename T>
  class IdentityHash
  {
  public:
    //! Returns the key as is.
    T operator()(const T& key) const { return key; }
  };

} // end of triton namespace

#endif // End of TRITON_HASH_HPP