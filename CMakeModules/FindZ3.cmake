# - Try to find Z3
# Once done, this will define
#
#  Z3_FOUND - system has Z3
#  Z3_INCLUDE_DIRS - the Z3 include directories
#  Z3_LIBRARIES - link these to use Z3

include(LibFindMacros)

# Dependencies
# libfind_package(Z3 z3)

# Use pkg-config to get hints about paths
# libfind_pkg_check_modules(Z3_PKGCONF z3)

# Include dir
find_path(Z3_INCLUDE_DIR
  NAMES z3.h
  PATHS ${Z3_PKGCONF_INCLUDE_DIRS}
)

# Finally the library itself
find_library(Z3_LIBRARY
  NAMES z3
  PATHS ${Z3_PKGCONF_LIBRARY_DIRS}
)

# Set the include dir variables and the libraries and let libfind_process do the rest.
# NOTE: Singular variables for this library, plural for libraries this this lib depends on.
set(Z3_PROCESS_INCLUDES Z3_INCLUDE_DIR Z3_INCLUDE_DIRS)
set(Z3_PROCESS_LIBS Z3_LIBRARY Z3_LIBRARIES)
libfind_process(Z3)

