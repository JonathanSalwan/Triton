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


# Get architecture
if(CMAKE_SIZEOF_VOID_P EQUAL 8)
    set(ARCHITECTURE amd64)
else()
    set(ARCHITECTURE i386)
endif()

if(${TARGET} MATCHES "ia32")
    set(ARCHITECTURE i386)
endif()


# Define if the library will be STATIC or DYNAMIC
if(STATICLIB)
    set(LIBTRITON_KIND_LINK STATIC)
else()
    set(LIBTRITON_KIND_LINK SHARED)
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


# Python bindings option
if(PYTHON_BINDINGS)
    add_definitions(-DTRITON_PYTHON_BINDINGS)
endif()


# Triton project
set(CMAKE_BUILD_TYPE Release)
set(PROJECT_LIBTRITON "triton")


# Default flags
# To fix old python version bug http://bugs.python.org/issue21958
if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
    set(LIBTRITON_CXX_FLAGS "-DHAVE_ROUND /MT")
endif()


# Global UNIX CXX Flags
if(CMAKE_COMPILER_IS_GNUCXX OR "${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang")
    # Flags
    set(LIBTRITON_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${FLAG_CXX}")
    set(LIBTRITON_CXX_FLAGS "${LIBTRITON_CXX_FLAGS} -Wall -Wextra -Werror -Wno-unused-parameter -Wno-unknown-pragmas -Wno-tautological-compare")
    set(LIBTRITON_CXX_FLAGS "${LIBTRITON_CXX_FLAGS} -O3")
    set(LIBTRITON_CXX_FLAGS "${LIBTRITON_CXX_FLAGS} -fno-stack-protector -fomit-frame-pointer -fno-strict-aliasing")
    set(LIBTRITON_CXX_FLAGS "${LIBTRITON_CXX_FLAGS} -fPIC -std=c++11")
endif()


# 32-bits
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux" OR ${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    if(${ARCHITECTURE} STREQUAL "i386")
        set(LIBTRITON_CXX_FLAGS "${LIBTRITON_CXX_FLAGS} -m32")
    endif()
endif()


# Use the same ABI as pin
if(PINTOOL)
    set(LIBTRITON_CXX_FLAGS "${LIBTRITON_CXX_FLAGS} -D_GLIBCXX_USE_CXX11_ABI=0")
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


# Find boost
find_package(Boost 1.55.0 REQUIRED)
include_directories("${Boost_INCLUDE_DIRS}")


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
    endif()
  endif()
  include_directories(${PYTHON_INCLUDE_DIRS})
endif()


# Find Z3
if(NOT Z3_INCLUDE_DIRS)
  set(Z3_INCLUDE_DIRS "$ENV{Z3_INCLUDE_DIRS}")
endif()
if(NOT STATICLIB) # Only if building dynamic library
  if(NOT Z3_LIBRARIES)
    set(Z3_LIBRARIES "$ENV{Z3_LIBRARIES}")
  endif()
  if(NOT Z3_INCLUDE_DIRS AND NOT Z3_LIBRARIES)
      find_package(Z3 REQUIRED)
      if(NOT Z3_FOUND)
          message(FATAL_ERROR "Z3 not found")
      endif()
  endif()
endif()
include_directories(${Z3_INCLUDE_DIRS})


# Find Capstone
if(NOT CAPSTONE_INCLUDE_DIRS)
  set(CAPSTONE_INCLUDE_DIRS "$ENV{CAPSTONE_INCLUDE_DIRS}")
endif()
if(NOT STATICLIB) # Only if building dynamic library
  if(NOT CAPSTONE_LIBRARIES)
    set(CAPSTONE_LIBRARIES "$ENV{CAPSTONE_LIBRARIES}")
  endif()
  if(NOT CAPSTONE_INCLUDE_DIRS AND NOT CAPSTONE_LIBRARIES)
      find_package(CAPSTONE REQUIRED)
      if(NOT CAPSTONE_FOUND)
          message(FATAL_ERROR "Capstone not found")
      endif()
  endif()
endif()
include_directories(${CAPSTONE_INCLUDE_DIRS})


# Add Triton includes
include_directories("${CMAKE_SOURCE_DIR}/src/libtriton/includes")


# Note: Windows ?!
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux" OR ${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    # Triton have to generate a syscalls table from the kernel source
    # This following code tries to find the unistd_64.h or unistd_32.h header depending on the architecture.
    if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
        FILE(GLOB_RECURSE syscalls32_table_files /usr/include/*unistd_32.h)
        FILE(GLOB_RECURSE syscalls64_table_files /usr/include/*unistd_64.h)
    endif()

    if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
        FILE(
            GLOB_RECURSE
            syscalls64_table_files
            /usr/include/sys/syscall.h
        )
    endif()

    LIST(GET syscalls64_table_files 0 syscalls64_table_file)
    # If the unistd_64.h or syscall.h is not found, we exit
    if(NOT EXISTS ${syscalls64_table_file})
        message(FATAL_ERROR "unistd_64.h or syscall.h is missing, please check the INSTALL file")
    endif()

    # We generate the syscalls64.cpp from the unistd_64.h or syscall.h.
    # Added python after COMMAND since to be sure that if ${CMAKE_SOURCE_DIR}/src/scripts/extract_syscall.py doesn't have X rights it gets executed
    execute_process(
        COMMAND python ${CMAKE_SOURCE_DIR}/src/scripts/extract_syscall.py ${syscalls64_table_file} 64
        OUTPUT_FILE ${CMAKE_SOURCE_DIR}/src/libtriton/os/unix/syscalls64.cpp
    )

    # If the syscalls64.cpp has not been created, we exit
    if(NOT EXISTS "${CMAKE_SOURCE_DIR}/src/libtriton/os/unix/syscalls64.cpp")
        message(FATAL_ERROR "./src/libtriton/os/unix/syscalls64.cpp is missing, please check the INSTALL file")
    endif()
endif()


# Syscall 32 is only available for linux users
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
    LIST(GET syscalls32_table_files 0 syscalls32_table_file)
    # If the unistd_32.h is not found, we exit
    if(NOT EXISTS ${syscalls32_table_file})
        message(FATAL_ERROR "unistd_32.h is missing, please check the INSTALL file")
    endif()

    # We generate the syscalls64.cpp from the unistd_32.h
    # Added python after COMMAND since to be sure that if ${CMAKE_SOURCE_DIR}/src/scripts/extract_syscall.py doesn't have X rights it gets executed
    execute_process(
        COMMAND python ${CMAKE_SOURCE_DIR}/src/scripts/extract_syscall.py ${syscalls32_table_file} 32
        OUTPUT_FILE ${CMAKE_SOURCE_DIR}/src/libtriton/os/unix/syscalls32.cpp
    )

    # If the syscalls32.cpp has not been created, we exit
    if(NOT EXISTS "${CMAKE_SOURCE_DIR}/src/libtriton/os/unix/syscalls32.cpp")
        message(FATAL_ERROR "./src/libtriton/os/unix/syscalls32.cpp is missing, please check the INSTALL file")
    endif()
endif()


# We generate the version numbers information
configure_file(
    ${CMAKE_SOURCE_DIR}/src/libtriton/includes/version.hpp.in
    ${CMAKE_SOURCE_DIR}/src/libtriton/includes/version.hpp
    IMMEDIATE @ONLY
)


# Define all source files
file(
    GLOB_RECURSE
    LIBTRITON_SOURCE_FILES
    ${CMAKE_SOURCE_DIR}/src/libtriton/*
)


# Define all headers files
file(
    GLOB_RECURSE
    LIBTRITON_HEADERS_FILES
    ${CMAKE_SOURCE_DIR}/src/libtriton/includes/*
)


# Define gloabl shared linker flags
set(LIBTRITON_SHARED_LINKER_FLAGS " ")


# Special cases for MinGW
if(${CMAKE_SYSTEM_NAME} MATCHES "Windows" AND "${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU")
    set(LIBTRITON_OTHER_LIBS "-lgomp")
    if (NOT STATICLIB)
        set(LIBTRITON_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -Wl,--export-all-symbols")
    endif()
endif()


# Define library's properties
add_library(${PROJECT_LIBTRITON} ${LIBTRITON_KIND_LINK} ${LIBTRITON_SOURCE_FILES})
set_target_properties(${PROJECT_LIBTRITON} PROPERTIES COMPILE_FLAGS ${LIBTRITON_CXX_FLAGS})
set_target_properties(${PROJECT_LIBTRITON} PROPERTIES LINK_FLAGS ${LIBTRITON_SHARED_LINKER_FLAGS})


# Link Triton's dependencies
target_link_libraries(
    ${PROJECT_LIBTRITON}
    ${PYTHON_LIBRARIES}
    ${Boost_LIBRARIES}
    ${Z3_LIBRARIES}
    ${CAPSTONE_LIBRARIES}
    ${LIBTRITON_OTHER_LIBS}
)


# Add the install targets
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
    set(TRITON_HEADER_INSTALL /usr/include/triton)
    set(TRITON_LIB_INSTALL /lib)
endif()

if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    set(TRITON_HEADER_INSTALL /usr/local/include/triton)
    set(TRITON_LIB_INSTALL /usr/local/lib)
endif()

if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
    if(NOT INSTALL_PREFIX)
        set(INSTALL_PREFIX C:\\Triton)
    endif()
    set(TRITON_HEADER_INSTALL ${INSTALL_PREFIX}\\include\\triton)
    set(TRITON_LIB_INSTALL ${INSTALL_PREFIX}\\lib)
endif()

install (TARGETS ${PROJECT_LIBTRITON} DESTINATION ${TRITON_LIB_INSTALL})
install (FILES ${LIBTRITON_HEADERS_FILES} DESTINATION ${TRITON_HEADER_INSTALL})


# Install Python bindings
if(PYTHON_BINDINGS)
    configure_file(
        ${CMAKE_SOURCE_DIR}/src/scripts/setup.py.in
        ${CMAKE_BINARY_DIR}/setup.py
        IMMEDIATE @ONLY
    )
    configure_file(
        ${CMAKE_SOURCE_DIR}/src/scripts/libTriton_units_testing.py.in
        ${CMAKE_SOURCE_DIR}/src/testers/libTriton_units_testing.py
        IMMEDIATE @ONLY
    )
    find_program(ENV_BINARY "env")
    if(UNIX)
      install (CODE "execute_process(COMMAND ${ENV_BINARY} python2 ${CMAKE_BINARY_DIR}/setup.py install)")
    endif()
endif()






##################################################################################### CMake libpintool

if(PINTOOL)
    set(PROJECT_PINTOOL "pintool")
    add_definitions(-DTRITON_PINTOOL)

    # Root directory of the Pin toolkit
    set(PIN_ROOT "${CMAKE_SOURCE_DIR}/../../..")


    # Specific Linux CXX Flags
    if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
        if(${ARCHITECTURE} STREQUAL "i386")
            set(PINTOOL_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DBIGARRAY_MULTIPLIER=1 -DUSING_XED -DTARGET_IA32 -DHOST_IA32 -DTARGET_LINUX -m32 -D_GLIBCXX_USE_CXX11_ABI=0")
        endif()

        if(${ARCHITECTURE} STREQUAL "amd64")
            set(PINTOOL_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DBIGARRAY_MULTIPLIER=1 -DUSING_XED -DTARGET_IA32E -DHOST_IA32E -DTARGET_LINUX -D_GLIBCXX_USE_CXX11_ABI=0")
        endif()

        set(PINTOOL_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -Wl,--hash-style=sysv -Wl,-Bsymbolic -fPIC")
    endif()


    # Specific OSX CXX Flags
    if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
        if(${ARCHITECTURE} STREQUAL "i386")
            set(PINTOOL_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DBIGARRAY_MULTIPLIER=1 -DTARGET_IA32 -DHOST_IA32E -DTARGET_MAC")
        endif()

        if(${ARCHITECTURE} STREQUAL "amd64")
            set(PINTOOL_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DBIGARRAY_MULTIPLIER=1 -DTARGET_IA32E -DHOST_IA32E -DTARGET_MAC")
        endif()

        set(PINTOOL_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -Wl,-Bsymbolic -fPIC")
    endif()


    # Specific Windows CXX Flags
    if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
        if(${ARCHITECTURE} STREQUAL "i386")
            set(PINTOOL_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DBIGARRAY_MULTIPLIER=1 -DUSING_XED -DTARGET_IA32 -DHOST_IA32 -DTARGET_WINDOWS -D_SECURE_SCL=0 -DHAVE_ROUND /MT")
        endif()

        if(${ARCHITECTURE} STREQUAL "amd64")
            set(PINTOOL_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DBIGARRAY_MULTIPLIER=1 -DUSING_XED -DTARGET_IA32E -DHOST_IA32E -DTARGET_WINDOWS -D_SECURE_SCL=0 -DHAVE_ROUND /MT")
        endif()

        set(PINTOOL_SHARED_LINKER_FLAGS " ")
    endif()


    # Global UNIX CXX Flags
    if(CMAKE_COMPILER_IS_GNUCXX)
        set(PINTOOL_CXX_FLAGS "${PINTOOL_CXX_FLAGS} -std=c++11 -fabi-version=2")
    elseif("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang")
        set(PINTOOL_CXX_FLAGS "${PINTOOL_CXX_FLAGS} -std=c++11")
    endif()


    # Includes directories (Pin)
    if(${ARCHITECTURE} STREQUAL "i386")
        include_directories("${PIN_ROOT}/extras/xed-ia32/include")
    endif()

    if(${ARCHITECTURE} STREQUAL "amd64")
        include_directories("${PIN_ROOT}/extras/xed-intel64/include")
    endif()

    include_directories("${PIN_ROOT}/source/include/pin")
    include_directories("${PIN_ROOT}/source/include/pin/gen")
    include_directories("${PIN_ROOT}/extras/components/include")
    include_directories("${PIN_ROOT}/source/tools/InstLib")


    # Libs directories (Pin)
    if(${ARCHITECTURE} STREQUAL "i386")
        link_directories("${PIN_ROOT}/ia32/lib")
        link_directories("${PIN_ROOT}/ia32/lib-ext")
        link_directories("${PIN_ROOT}/extras/xed-ia32/lib")
    endif()

    if(${ARCHITECTURE} STREQUAL "amd64")
        link_directories("${PIN_ROOT}/intel64/lib")
        link_directories("${PIN_ROOT}/intel64/lib-ext")
        link_directories("${PIN_ROOT}/extras/xed-intel64/lib")
    endif()

    if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
        if(${ARCHITECTURE} STREQUAL "i386")
            link_directories("${PIN_ROOT}/ia32/runtime/glibc")
        endif()
        if(${ARCHITECTURE} STREQUAL "amd64")
            link_directories("${PIN_ROOT}/intel64/runtime/glibc")
        endif()
    endif()


    # Pintool source files
    configure_file(
        ${CMAKE_SOURCE_DIR}/src/tracer/pin/init.in
        ${CMAKE_SOURCE_DIR}/src/tracer/pin/init.cpp
        IMMEDIATE @ONLY
    )

    file(
        GLOB_RECURSE
        PINTOOL_SOURCE_FILES
        ${CMAKE_SOURCE_DIR}/src/tracer/pin/*
    )
    list(REMOVE_ITEM PINTOOL_SOURCE_FILES ${CMAKE_SOURCE_DIR}/src/tracer/pin/init.in)

    add_library(${PROJECT_PINTOOL} SHARED ${PINTOOL_SOURCE_FILES})
    set_target_properties(${PROJECT_PINTOOL} PROPERTIES COMPILE_FLAGS ${PINTOOL_CXX_FLAGS})
    set_target_properties(${PROJECT_PINTOOL} PROPERTIES LINK_FLAGS ${PINTOOL_SHARED_LINKER_FLAGS})

    if(${CMAKE_SYSTEM_NAME} MATCHES "Linux" OR ${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
        target_link_libraries(${PROJECT_PINTOOL} pin xed pindwarf dl ${PROJECT_LIBTRITON})
    endif()

    if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
        if(${ARCHITECTURE} STREQUAL "i386")
            target_link_libraries(${PROJECT_PINTOOL} pin pinvm xed ntdll-32 ${PROJECT_LIBTRITON})
        endif()
        if(${ARCHITECTURE} STREQUAL "amd64")
            target_link_libraries(${PROJECT_PINTOOL} pin pinvm xed ntdll-64 ${PROJECT_LIBTRITON})
        endif()
    endif()


    # Generate the triton's shortcut script
    set(PIN_BIN_PATH ${PIN_ROOT}/pin.sh)
    set(PINTOOL_PATH ${CMAKE_BINARY_DIR}/${CMAKE_SHARED_LIBRARY_PREFIX}${PROJECT_PINTOOL}${CMAKE_SHARED_LIBRARY_SUFFIX})
    set(FLAG_IFEELLUCKY "")


    # Pin flag for kernel 4.x
    if(KERNEL4)
        set(FLAG_IFEELLUCKY "-ifeellucky")
    endif()


    # Generate Triton pintool script
    if(${CMAKE_SYSTEM_NAME} MATCHES "Linux" OR ${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
        configure_file(
            ${CMAKE_SOURCE_DIR}/src/scripts/triton.in
            ${CMAKE_SOURCE_DIR}/triton
            IMMEDIATE @ONLY
        )

        configure_file(
            ${CMAKE_SOURCE_DIR}/src/scripts/tritonAttach.in
            ${CMAKE_SOURCE_DIR}/tritonAttach
            IMMEDIATE @ONLY
        )
    endif()
endif()
