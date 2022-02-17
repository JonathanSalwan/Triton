# - Try to find CAPSTONE
# Once done, this will define
#
#  CAPSTONE_FOUND - system has CAPSTONE
#  CAPSTONE_INCLUDE_DIRS - the CAPSTONE include directories
#  CAPSTONE_LIBRARIES - link these to use CAPSTONE

include(LibFindMacros)

# Dependencies
# libfind_package(CAPSTONE capstone)

# Use pkg-config to get hints about paths
# libfind_pkg_check_modules(CAPSTONE_PKGCONF capstone)

if(NOT CAPSTONE_INCLUDE_DIRS)
    set(CAPSTONE_INCLUDE_DIRS "$ENV{CAPSTONE_INCLUDE_DIRS}")
endif()

if(NOT CAPSTONE_LIBRARIES)
    set(CAPSTONE_LIBRARIES "$ENV{CAPSTONE_LIBRARIES}")
endif()

if(NOT CAPSTONE_INCLUDE_DIRS AND NOT CAPSTONE_LIBRARIES)
    find_path(CAPSTONE_INCLUDE_DIR
      NAMES capstone/capstone.h
      PATHS ${CAPSTONE_PKGCONF_INCLUDE_DIRS}
    )

    find_library(CAPSTONE_LIBRARY
      NAMES capstone
      PATHS ${CAPSTONE_PKGCONF_LIBRARY_DIRS}
    )

    # Set the include dir variables and the libraries and let libfind_process do the rest.
    # NOTE: Singular variables for this library, plural for libraries this this lib depends on.
    set(CAPSTONE_PROCESS_INCLUDES CAPSTONE_INCLUDE_DIR CAPSTONE_INCLUDE_DIRS)
    set(CAPSTONE_PROCESS_LIBS CAPSTONE_LIBRARY CAPSTONE_LIBRARIES)

    libfind_process(CAPSTONE)

    if(NOT CAPSTONE_FOUND)
        message(FATAL_ERROR "Capstone not found")
    else()
        cmake_path(GET CAPSTONE_LIBRARY PARENT_PATH CAPSTONE_LIB_DIR)
        cmake_path(GET CAPSTONE_LIBRARY STEM LAST_ONLY CAPSTONE_LIB_NAME)
        string(REGEX REPLACE "^lib" "" CAPSTONE_LIB_NAME ${CAPSTONE_LIB_NAME})
    endif()
else()
    message(STATUS "Capstone includes directory defined: ${CAPSTONE_INCLUDE_DIRS}")
    message(STATUS "Capstone libraries defined: ${CAPSTONE_LIBRARIES}")
endif()
