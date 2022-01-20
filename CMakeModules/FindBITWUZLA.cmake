# - Try to find BITWUZLA
# Once done, this will define
#
#  BITWUZLA_FOUND - system has BITWUZLA
#  BITWUZLA_INCLUDE_DIRS - the BITWUZLA include directories
#  BITWUZLA_LIBRARIES - link these to use BITWUZLA

include(LibFindMacros)

# Dependencies
# libfind_package(BITWUZLA bitwuzla)

# Use pkg-config to get hints about paths
# libfind_pkg_check_modules(BITWUZLA_PKGCONF bitwuzla)

if(NOT BITWUZLA_INCLUDE_DIRS)
    set(BITWUZLA_INCLUDE_DIRS "$ENV{BITWUZLA_INCLUDE_DIRS}")
endif()

if(NOT BITWUZLA_LIBRARIES)
    set(BITWUZLA_LIBRARIES "$ENV{BITWUZLA_LIBRARIES}")
endif()

if(NOT BITWUZLA_INCLUDE_DIRS AND NOT BITWUZLA_LIBRARIES)
    find_path(BITWUZLA_INCLUDE_DIR
      NAMES bitwuzla/bitwuzla.h
      PATHS ${BITWUZLA_PKGCONF_INCLUDE_DIRS}
    )

    if(NOT BUILD_SHARED_LIBS)
        SET(CMAKE_FIND_LIBRARY_SUFFIXES ".a")
    endif()

    find_library(BITWUZLA_LIBRARY
      NAMES bitwuzla
      PATHS ${BITWUZLA_PKGCONF_LIBRARY_DIRS}
    )

    # Set the include dir variables and the libraries and let libfind_process do the rest.
    # NOTE: Singular variables for this library, plural for libraries this this lib depends on.
    set(BITWUZLA_PROCESS_INCLUDES BITWUZLA_INCLUDE_DIR BITWUZLA_INCLUDE_DIRS)
    set(BITWUZLA_PROCESS_LIBS BITWUZLA_LIBRARY BITWUZLA_LIBRARIES)

    libfind_process(BITWUZLA)

    if(NOT BITWUZLA_FOUND)
        message(FATAL_ERROR "Bitwuzla not found")
    endif()
else()
    message(STATUS "Bitwuzla includes directory defined: ${BITWUZLA_INCLUDE_DIRS}")
    message(STATUS "Bitwuzla libraries defined: ${BITWUZLA_LIBRARIES}")
endif()
