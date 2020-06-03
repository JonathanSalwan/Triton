##
##  Copyright (C) - Triton
##
##  This program is under the terms of the BSD License.
##

##################################################################################### CMake libtriton

cmake_minimum_required(VERSION 2.8)
project(triton)

# Define cmake options
option(ASAN "Enable the ASAN linking" OFF)
option(GCOV "Enable code coverage" OFF)
option(KERNEL4 "Pin will run on a Linux's kernel v4" ON)
option(PINTOOL "Build Triton with the Pin tool as tracer" OFF)
option(PYTHON36 "Python 36" ON)
option(PYTHON37 "Python 37" OFF)
option(PYTHON38 "Python 38" OFF)
option(PYTHON_BINDINGS "Enable Python bindings into the libtriton" ON)
option(PYTHON_BINDINGS_AUTOCOMPLETE "Enable the generation of a triton_autocomplete module for IDE autocompletion" OFF)
option(STATICLIB "Build a static library" OFF)
option(Z3_INTERFACE "Use Z3 as SMT solver" ON)

if(STATICLIB)
    # We can't use Python bindings with a static library
    set(PYTHON_BINDINGS OFF)
endif()

if(PINTOOL AND NOT PYTHON_BINDINGS)
    MESSAGE(FATAL_ERROR "You can't have pintools without python binding.")
endif()

if(PINTOOL AND (PYTHON36 OR PYTHON37 OR PYTHON38))
    MESSAGE(FATAL_ERROR "The Pin tracer needs Python 2.7.")
endif()

set(TRITON_ROOT "${CMAKE_CURRENT_LIST_DIR}")

#Enable ctest
include(CTest)

set(PYTHONPATH_CMD ${CMAKE_COMMAND} -E env PYTHONPATH=${CMAKE_CURRENT_BINARY_DIR}/src/libtriton/${CMAKE_CFG_INTDIR}/)

if(PYTHON_BINDINGS)
    if(PYTHON38)
        set(PYTHON_VERSION 3.8)
    elseif(PYTHON37)
        set(PYTHON_VERSION 3.7)
    elseif(PYTHON36)
        set(PYTHON_VERSION 3.6)
    else()
        set(PYTHON_VERSION 2.7)
    endif()
    find_package(PythonInterp ${PYTHON_VERSION} REQUIRED)
    add_custom_target(test-python
        COMMAND ${PYTHONPATH_CMD} ${PYTHON_EXECUTABLE} -m unittest discover ${TRITON_ROOT}/src/testers/unittests
        DEPENDS python-triton
    )
else()
    add_custom_target(test-python
        COMMAND echo "No python test as python support is disabled"
    )
endif()

if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  if(GCOV)
    add_custom_target(check
        COMMAND lcov --zerocounters --directory ${CMAKE_BINARY_DIR}/src/libtriton
        COMMAND lcov --capture --initial --directory ${CMAKE_BINARY_DIR}/src/libtriton --output-file app
        COMMAND ${CMAKE_COMMAND} --build ${CMAKE_BINARY_DIR} --target test-python
        COMMAND ${PYTHONPATH_CMD} ${TRITON_ROOT}/src/scripts/run_linux_test.sh
        COMMAND lcov --no-checksum --directory ${CMAKE_BINARY_DIR}/src/libtriton --capture --output-file coverage.info
        COMMAND lcov --remove coverage.info '/usr*' --remove coverage.info 'pintools*' --remove coverage.info 'examples*' -o coverage.info
        COMMAND genhtml coverage.info -o coverage
        COMMAND ${CMAKE_COMMAND} -E echo "-- Report generated in ${CMAKE_CURRENT_BINARY_DIR}/coverage/index.html"
    )
  else()
    # Special handling of Linux test to check if pin can be attached on other binaries.
    add_custom_target(check
        COMMAND ${PYTHONPATH_CMD} ${TRITON_ROOT}/src/scripts/run_linux_test.sh
        DEPENDS test-python
    )
  endif()
else()
    add_custom_target(check
        COMMAND ${PYTHONPATH_CMD} ctest --output-on-failure
        DEPENDS test-python
    )
endif()

# Defaut build type as Release
if(NOT CMAKE_BUILD_TYPE AND NOT CMAKE_CONFIGURATION_TYPES)
    set(CMAKE_BUILD_TYPE Release)
endif()

if(GCOV)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -g -O0 --coverage")
endif()

# Specific OSX POLICY
if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    if(POLICY CMP0025)
        cmake_policy(SET CMP0025 OLD) # report Apple's Clang as just Clang
    endif()
    if(POLICY CMP0042)
        cmake_policy(SET CMP0042 NEW) # MACOSX_RPATH
    endif()
endif()

# Get architecture
if(CMAKE_SIZEOF_VOID_P EQUAL 8)
    set(ARCHITECTURE amd64)
else()
    set(ARCHITECTURE i386)
endif()

if(NOT ${ARCHITECTURE} STREQUAL "i386" AND "${TARGET}" MATCHES "ia32")
    set(ARCHITECTURE i386)
    if(${CMAKE_SYSTEM_NAME} MATCHES "Linux" OR ${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
        # Set appropriate compile and linker flags
        set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -m32")
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -m32")
        if(NOT STATICLIB)
            set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -m32")
        endif()
        set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -m32")
    endif()
endif()

# Read the build version
file(READ ${TRITON_ROOT}/.build_number BUILD_NUMBER)
set(VERSION_MAJOR 0)
set(VERSION_MINOR 9)
set(VERSION_BUILD ${BUILD_NUMBER})

# Custom cmake search
list(APPEND CMAKE_MODULE_PATH "${TRITON_ROOT}/CMakeModules/")

# Find Python
if(PYTHON_BINDINGS)
    find_package(PythonInterp ${PYTHON_VERSION} REQUIRED)
    if(NOT PYTHON_INCLUDE_DIRS)
        set(PYTHON_INCLUDE_DIRS "$ENV{PYTHON_INCLUDE_DIRS}")
    endif()
        if(NOT PYTHON_LIBRARIES)
            set(PYTHON_LIBRARIES "$ENV{PYTHON_LIBRARIES}")
        endif()
        if(NOT PYTHON_INCLUDE_DIRS AND NOT PYTHON_LIBRARIES)
            find_package(PythonLibs ${PYTHON_VERSION} REQUIRED)
        elseif(NOT (PYTHON_INCLUDE_DIRS AND PYTHON_LIBRARIES))
            message(FATAL_ERROR "Inconsistent PYTHON_INCLUDE_DIRS and PYTHON_LIBRARIES")
        endif()
    include_directories(${PYTHON_INCLUDE_DIRS})
    add_definitions("-DPYTHON_LIBRARIES=\"${PYTHON_LIBRARIES}\"")
endif()

# Find Z3
if(Z3_INTERFACE)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DZ3_INTERFACE")
    if(NOT Z3_INCLUDE_DIRS)
        set(Z3_INCLUDE_DIRS "$ENV{Z3_INCLUDE_DIRS}")
    endif()

    if(NOT Z3_LIBRARIES)
        set(Z3_LIBRARIES "$ENV{Z3_LIBRARIES}")
    endif()

    if(NOT Z3_INCLUDE_DIRS AND NOT Z3_LIBRARIES)
        find_package(Z3 REQUIRED)
        if(NOT Z3_FOUND)
            message(FATAL_ERROR "Z3 not found")
        endif()
    endif()
    include_directories(${Z3_INCLUDE_DIRS})
    set(TRITON_Z3_INTERFACE ON)
endif()

# Find Capstone
if(NOT CAPSTONE_INCLUDE_DIRS)
    set(CAPSTONE_INCLUDE_DIRS "$ENV{CAPSTONE_INCLUDE_DIRS}")
endif()

if(NOT CAPSTONE_LIBRARIES)
    set(CAPSTONE_LIBRARIES "$ENV{CAPSTONE_LIBRARIES}")
endif()

if(NOT CAPSTONE_INCLUDE_DIRS AND NOT CAPSTONE_LIBRARIES)
    find_package(CAPSTONE REQUIRED)
    if(NOT CAPSTONE_FOUND)
        message(FATAL_ERROR "Capstone not found")
    endif()
endif()

include_directories(${CAPSTONE_INCLUDE_DIRS})

# Find boost
find_package(Boost 1.55.0 REQUIRED)
include_directories("${Boost_INCLUDE_DIRS}")

# Use the same ABI as pin
if(PINTOOL)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D_GLIBCXX_USE_CXX11_ABI=0")
endif()

# Add triton includes for every project
include_directories("${TRITON_ROOT}/src/libtriton/includes")

set(PROJECT_LIBTRITON "triton")
add_subdirectory(src)
add_subdirectory(doc)
