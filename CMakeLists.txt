##
##  Copyright (C) - Triton
##
##  This program is under the terms of the BSD License.
##

##################################################################################### CMake libtriton

cmake_minimum_required(VERSION 2.8)
project(triton)

# Define cmake options
option(PINTOOL "Build Triton with the Pin tool as tracer" OFF)
option(KERNEL4 "Pin will run on a Linux's kernel v4" ON)
option(PYTHON_BINDINGS "Enable Python bindings into the libtriton" ON)
option(STATICLIB "Build a static library" OFF)
option(INCBUILD "Increment the build number" OFF)
option(GCOV "Enable code coverage" OFF)

if(PINTOOL AND NOT PYTHON_BINDINGS)
  MESSAGE(FATAL_ERROR "You can't have pintools without python binding.")
endif()

#Enable ctest
include(CTest)

set(PYTHONPATH_CMD ${CMAKE_COMMAND} -E env PYTHONPATH=${CMAKE_CURRENT_BINARY_DIR}/src/libtriton/${CMAKE_CFG_INTDIR}/)

if(PYTHON_BINDINGS)
    find_package(PythonInterp 2.7 REQUIRED)
    add_custom_target(test-python
      COMMAND ${PYTHONPATH_CMD} ${PYTHON_EXECUTABLE} -m unittest discover ${CMAKE_SOURCE_DIR}/src/testers/unittests
      DEPENDS python-triton
      )
else()
  add_custom_target(test-python
    COMMAND echo "No python test as python support is disabled")
endif()
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  if(GCOV)
     add_custom_target(check
         COMMAND lcov --zerocounters --directory ${CMAKE_BINARY_DIR}/src/libtriton
         COMMAND lcov --capture --initial --directory ${CMAKE_BINARY_DIR}/src/libtriton --output-file app
         COMMAND ${CMAKE_COMMAND} --build ${CMAKE_BINARY_DIR} --target test-python
         #COMMAND ${PYTHONPATH_CMD} ctest
         COMMAND lcov --no-checksum --directory ${CMAKE_BINARY_DIR}/src/libtriton --capture --output-file coverage.info
         COMMAND lcov --remove coverage.info '/usr*' --remove coverage.info 'pintools*' --remove coverage.info 'examples*' -o coverage.info
         COMMAND genhtml coverage.info -o coverage
         COMMAND ${CMAKE_COMMAND} -E echo "-- Report generated in ${CMAKE_CURRENT_BINARY_DIR}/coverage/index.html"
         )
  else()
    # Special handling of Linux test to check if pin can be attached on other binaries.
    add_custom_target(check
      COMMAND ${PYTHONPATH_CMD} ${CMAKE_SOURCE_DIR}/src/scripts/run_linux_test.sh
      DEPENDS test-python)
  endif()
else()
  add_custom_target(check
    COMMAND ${PYTHONPATH_CMD} ctest
    DEPENDS test-python)
endif()

set(CMAKE_BUILD_TYPE Release)

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

if(${TARGET} MATCHES "ia32")
    set(ARCHITECTURE i386)
endif()

# Triton version
if(INCBUILD)
    # Get and increment the build number
    file(READ ${CMAKE_SOURCE_DIR}/.build_number BUILD_NUMBER)
    math(EXPR NEW_BUILD_NUMBER "${BUILD_NUMBER} + 1")
    file(WRITE ${CMAKE_SOURCE_DIR}/.build_number ${NEW_BUILD_NUMBER})
endif()

file(READ ${CMAKE_SOURCE_DIR}/.build_number BUILD_NUMBER)
set(VERSION_MAJOR 0)
set(VERSION_MINOR 4)
set(VERSION_BUILD ${BUILD_NUMBER})

if(INCBUILD)
    # Update the PROJECT_NUMBER variable inside the Doxyfile
    file(READ ${CMAKE_SOURCE_DIR}/Doxyfile DOXYFILE)
    STRING(REGEX REPLACE "PROJECT_NUMBER[ ]*=[ ]*\"[a-zA-Z0-9. ]*\"" "PROJECT_NUMBER = \"version ${VERSION_MAJOR}.${VERSION_MINOR} build ${VERSION_BUILD}\"" PROJECT_NUMBER ${DOXYFILE})
    file(WRITE ${CMAKE_SOURCE_DIR}/Doxyfile ${PROJECT_NUMBER})
endif()

# Custom cmake search
list(APPEND CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/CMakeModules/")

# Find Python 2.7
if(PYTHON_BINDINGS)
  if(NOT PYTHON_INCLUDE_DIRS)
    set(PYTHON_INCLUDE_DIRS "$ENV{PYTHON_INCLUDE_DIRS}")
  endif()
  if(NOT STATICLIB) # Only if building dynamic library
    if(NOT PYTHON_LIBRARIES)
      set(PYTHON_LIBRARIES "$ENV{PYTHON_LIBRARIES}")
    endif()
    if(NOT PYTHON_INCLUDE_DIRS AND NOT PYTHON_LIBRARIES)
        find_package(PythonLibs 2.7 REQUIRED)
    elseif(NOT (PYTHON_INCLUDE_DIRS AND PYTHON_LIBRARIES))
        message(FATAL_ERROR "Inconsistent PYTHON_INCLUDE_DIRS and PYTHON_LIBRARIES")
    endif()
  endif()
  include_directories(${PYTHON_INCLUDE_DIRS})
  add_definitions("-DPYTHON_LIBRARIES=\"${PYTHON_LIBRARIES}\"")
endif()

# Use the same ABI as pin
if(PINTOOL)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D_GLIBCXX_USE_CXX11_ABI=0")
endif()

# Add triton includes for every project
include_directories("${CMAKE_SOURCE_DIR}/src/libtriton/includes")

set(PROJECT_LIBTRITON "triton")
add_subdirectory(src)
