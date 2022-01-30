##
##  Copyright (C) - Triton
##
##  This program is under the terms of the BSD License.
##

##################################################################################### CMake libtriton

cmake_minimum_required(VERSION 3.15)

set(TRITON_ROOT "${CMAKE_CURRENT_LIST_DIR}")

# Read the build version
file(READ ${TRITON_ROOT}/.build_number BUILD_NUMBER)
set(VERSION_MAJOR 0)
set(VERSION_MINOR 9)
set(VERSION_BUILD ${BUILD_NUMBER})

# Used for write_basic_package_version_file()
project(triton VERSION ${VERSION_MAJOR}.${VERSION_MINOR})

# Define cmake options
include(CMakeDependentOption)

option(ASAN                 "Enable the ASAN linking"                  OFF)
option(BITWUZLA_INTERFACE   "Use Bitwuzla as SMT solver"               OFF)
option(BUILD_SHARED_LIBS    "Build a shared library"                   ON)
option(GCOV                 "Enable code coverage"                     OFF)
option(LLVM_INTERFACE       "Use LLVM for lifting"                     OFF)
option(MSVC_STATIC          "Use statically-linked runtime library"    OFF)
option(Z3_INTERFACE         "Use Z3 as SMT solver"                     ON)

# Define cmake dependent options
cmake_dependent_option(PYTHON_BINDINGS      "Enable Python bindings"                        ON BUILD_SHARED_LIBS OFF)
cmake_dependent_option(PYTHON_AUTOCOMPLETE  "Generate Python triton_autocomplete module"    OFF BUILD_SHARED_LIBS OFF)

#Enable ctest
include(CTest)
add_custom_target(check
    COMMAND ${CMAKE_COMMAND} -E env PYTHONPATH="${CMAKE_CURRENT_BINARY_DIR}/src/libtriton" ctest --output-on-failure
    DEPENDS triton
)

if(PYTHON_BINDINGS)
    message(STATUS "Compiling with Python bindings")
    set(PYTHONPATH_CMD ${CMAKE_COMMAND} -E env PYTHONPATH=${CMAKE_CURRENT_BINARY_DIR}/src/libtriton/${CMAKE_CFG_INTDIR}/)
    if(NOT PYTHON_VERSION)
        set(PYTHON_VERSION 3.6)
    endif()
    find_package(PythonInterp ${PYTHON_VERSION} REQUIRED)
    find_package(PythonLibs ${PYTHON_VERSION} REQUIRED)
    include_directories(${PYTHON_INCLUDE_DIRS})
    add_definitions("-DPYTHON_LIBRARIES=\"${PYTHON_LIBRARIES}\"")
    add_custom_target(test-python
        COMMAND ${PYTHONPATH_CMD} ${PYTHON_EXECUTABLE} -m unittest discover ${TRITON_ROOT}/src/testers/unittests
        DEPENDS python-triton
    )
    if(NOT GCOV)
        add_dependencies(check test-python)
    endif()
else()
    add_custom_target(test-python
        COMMAND echo "No python test as python support is disabled"
    )
endif()

if(${CMAKE_SYSTEM_NAME} MATCHES "Linux" AND GCOV)
    message(STATUS "Compiled with GCOV")
    add_custom_target(gcov-test
        COMMAND lcov --zerocounters --directory ${CMAKE_BINARY_DIR}/src/libtriton
        COMMAND lcov --capture --initial --directory ${CMAKE_BINARY_DIR}/src/libtriton --output-file app
        COMMAND ${CMAKE_COMMAND} --build ${CMAKE_BINARY_DIR} --target test-python
        COMMAND ctest --output-on-failure
        COMMAND lcov --no-checksum --directory ${CMAKE_BINARY_DIR}/src/libtriton --capture --output-file coverage.info
        COMMAND lcov --remove coverage.info '/usr*' --remove coverage.info 'pintools*' --remove coverage.info 'examples*' -o coverage.info
        COMMAND genhtml coverage.info -o coverage
        COMMAND ${CMAKE_COMMAND} -E echo "-- Report generated in ${CMAKE_CURRENT_BINARY_DIR}/coverage/index.html"
    )
    add_dependencies(check gcov-test)
    add_compile_options(--coverage)
    add_link_options(--coverage)
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

# Custom cmake search
list(APPEND CMAKE_MODULE_PATH "${TRITON_ROOT}/CMakeModules/")

# Find Z3
if(Z3_INTERFACE)
    message(STATUS "Compiling with Z3 SMT solver")
    find_package(Z3 REQUIRED)
    include_directories(${Z3_INCLUDE_DIRS})
    set(TRITON_Z3_INTERFACE ON)
endif()

# Find bitwuzla
if(BITWUZLA_INTERFACE)
    message(STATUS "Compiling with Bitwuzla SMT solver")
    find_package(BITWUZLA REQUIRED)
    include_directories(${BITWUZLA_INCLUDE_DIRS})
    set(TRITON_BITWUZLA_INTERFACE ON)
endif()

# Find LLVM
if(LLVM_INTERFACE)
    message(STATUS "Compiling with LLVM")
    find_package(LLVM REQUIRED)
    include_directories(${LLVM_INCLUDE_DIRS})
    set(TRITON_LLVM_INTERFACE ON)
endif()

# Find Capstone
message(STATUS "Compiling with Capstone")
find_package(CAPSTONE REQUIRED)
include_directories(${CAPSTONE_INCLUDE_DIRS})

# Find boost
message(STATUS "Compiling with Boost headers")
find_package(Boost 1.55.0 REQUIRED)
include_directories("${Boost_INCLUDE_DIRS}")

add_subdirectory(src)
add_subdirectory(doc)
