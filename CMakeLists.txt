##
##  Copyright (C) - Triton
##
##  This program is under the terms of the LGPLv3 License.
##

##################################################################################### CMake libtriton

cmake_minimum_required(VERSION 2.8)
project(triton)

# Define cmake options
option(PINTOOL "Build Triton with the Pin tool as tracer" OFF)
option(KERNEL4 "Pin will run on a Linux's kernel v4" OFF)
option(PYTHON_BINDINGS "Enable Python bindings into the libtriton" ON)


# Get and increment the build number
file(READ ${CMAKE_SOURCE_DIR}/.build_number BUILD_NUMBER)
math(EXPR NEW_BUILD_NUMBER "${BUILD_NUMBER} + 1")
file(WRITE ${CMAKE_SOURCE_DIR}/.build_number ${NEW_BUILD_NUMBER})


# Get architecture
if(CMAKE_SIZEOF_VOID_P EQUAL 8)
    set(ARCHITECTURE amd64)
else(CMAKE_SIZEOF_VOID_P EQUAL 8)
    set(ARCHITECTURE i386)
endif(CMAKE_SIZEOF_VOID_P EQUAL 8)

if(${TARGET} MATCHES "ia32")
    set(ARCHITECTURE i386)
endif()


# Triton version
set(VERSION_MAJOR 0)
set(VERSION_MINOR 3)
set(VERSION_BUILD ${NEW_BUILD_NUMBER})


# Update the PROJECT_NUMBER variable inside the Doxyfile
file(READ ${CMAKE_SOURCE_DIR}/Doxyfile DOXYFILE)
STRING(REGEX REPLACE "PROJECT_NUMBER[ ]*=[ ]*\"[a-zA-Z0-9. ]*\"" "PROJECT_NUMBER = \"version ${VERSION_MAJOR}.${VERSION_MINOR} build ${VERSION_BUILD}\"" PROJECT_NUMBER ${DOXYFILE})
file(WRITE ${CMAKE_SOURCE_DIR}/Doxyfile ${PROJECT_NUMBER})


# Custom cmake search
list(APPEND CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/CMakeModules/")


# Python bindings option
if(PYTHON_BINDINGS)
    add_definitions(-DTRITON_PYTHON_BINDINGS)
endif(PYTHON_BINDINGS)


# Triton project
set(CMAKE_BUILD_TYPE Release)
set(PROJECT_LIBTRITON "triton")


# Default flags
# To fix old python version bug http://bugs.python.org/issue21958
if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
    set(LIBTRITON_CXX_FLAGS "-DHAVE_ROUND /MT")
endif(${CMAKE_SYSTEM_NAME} MATCHES "Windows")


# Global UNIX CXX Flags
if(CMAKE_COMPILER_IS_GNUCXX OR "${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang")
    # Flags
    set(LIBTRITON_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${FLAG_CXX}")
    set(LIBTRITON_CXX_FLAGS "${LIBTRITON_CXX_FLAGS} -Wall -Werror -Wno-unknown-pragmas -Wno-tautological-compare")
    set(LIBTRITON_CXX_FLAGS "${LIBTRITON_CXX_FLAGS} -O3 -g3 -ggdb3")
    set(LIBTRITON_CXX_FLAGS "${LIBTRITON_CXX_FLAGS} -fno-stack-protector -fomit-frame-pointer -fno-strict-aliasing")
    set(LIBTRITON_CXX_FLAGS "${LIBTRITON_CXX_FLAGS} -fPIC -std=c++11")
endif(CMAKE_COMPILER_IS_GNUCXX OR "${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang")


# 32-bits
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux" OR ${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    if(${ARCHITECTURE} STREQUAL "i386")
        set(LIBTRITON_CXX_FLAGS "${LIBTRITON_CXX_FLAGS} -m32")
    endif(${ARCHITECTURE} STREQUAL "i386")
endif(${CMAKE_SYSTEM_NAME} MATCHES "Linux" OR ${CMAKE_SYSTEM_NAME} MATCHES "Darwin")


# Use the same ABI as pin
if(PINTOOL)
    set(LIBTRITON_CXX_FLAGS "${LIBTRITON_CXX_FLAGS} -D_GLIBCXX_USE_CXX11_ABI=0")
endif(PINTOOL)


# Specific OSX POLICY
if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    if(POLICY CMP0025)
        cmake_policy(SET CMP0025 OLD) # report Apple's Clang as just Clang
    endif()
    if(POLICY CMP0042)
        cmake_policy(SET CMP0042 NEW) # MACOSX_RPATH
    endif()
endif(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")


# Find boost
find_package(Boost 1.55.0 REQUIRED)
include_directories(${Boost_INCLUDE_DIRS})


# Find Python 2.7
find_package(PythonLibs 2.7 REQUIRED)
include_directories(${PYTHON_INCLUDE_DIRS})


# Find Z3
find_package(Z3 REQUIRED)
include_directories(${Z3_INCLUDE_DIRS})
if (NOT Z3_FOUND)
    message(FATAL_ERROR "Z3 not found")
endif()


# Find Capstone
find_package(CAPSTONE REQUIRED)
include_directories(${CAPSTONE_INCLUDE_DIRS})
if (NOT CAPSTONE_FOUND)
    message(FATAL_ERROR "Capstone not found")
endif()


# Add Triton includes
include_directories("${CMAKE_SOURCE_DIR}/src/libtriton/includes")


# Note: Windows ?!
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux" OR ${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    # Triton have to generate a syscalls table from the kernel source
    # This following code tries to find the unistd_64.h or unistd_32.h header depending on the architecture.
    if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
        FILE(GLOB_RECURSE syscalls32_table_files /usr/include/*unistd_32.h)
        FILE(GLOB_RECURSE syscalls64_table_files /usr/include/*unistd_64.h)
    endif(${CMAKE_SYSTEM_NAME} MATCHES "Linux")

    if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
        FILE(
            GLOB_RECURSE
            syscalls64_table_files
            /usr/include/sys/syscall.h
        )
    endif(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")

    LIST(GET syscalls64_table_files 0 syscalls64_table_file)
    # If the unistd_64.h or syscall.h is not found, we exit
    if (NOT EXISTS ${syscalls64_table_file})
        message(FATAL_ERROR "unistd_64.h or syscall.h is missing, please check the INSTALL file")
    endif()

    # We generate the syscalls64.cpp from the unistd_64.h or syscall.h.
    # Added python after COMMAND since to be sure that if ${CMAKE_SOURCE_DIR}/src/scripts/extract_syscall.py doesn't have X rights it gets executed
    execute_process(
        COMMAND python ${CMAKE_SOURCE_DIR}/src/scripts/extract_syscall.py ${syscalls64_table_file} 64
        OUTPUT_FILE ${CMAKE_SOURCE_DIR}/src/libtriton/os/unix/syscalls64.cpp
    )

    # If the syscalls64.cpp has not been created, we exit
    if (NOT EXISTS "${CMAKE_SOURCE_DIR}/src/libtriton/os/unix/syscalls64.cpp")
        message(FATAL_ERROR "./src/libtriton/os/unix/syscalls64.cpp is missing, please check the INSTALL file")
    endif()
endif(${CMAKE_SYSTEM_NAME} MATCHES "Linux" OR ${CMAKE_SYSTEM_NAME} MATCHES "Darwin")


# Syscall 32 is only available for linux users
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
    LIST(GET syscalls32_table_files 0 syscalls32_table_file)
    # If the unistd_32.h is not found, we exit
    if (NOT EXISTS ${syscalls32_table_file})
        message(FATAL_ERROR "unistd_32.h is missing, please check the INSTALL file")
    endif()

    # We generate the syscalls64.cpp from the unistd_32.h
    # Added python after COMMAND since to be sure that if ${CMAKE_SOURCE_DIR}/src/scripts/extract_syscall.py doesn't have X rights it gets executed
    execute_process(
        COMMAND python ${CMAKE_SOURCE_DIR}/src/scripts/extract_syscall.py ${syscalls32_table_file} 32
        OUTPUT_FILE ${CMAKE_SOURCE_DIR}/src/libtriton/os/unix/syscalls32.cpp
    )

    # If the syscalls32.cpp has not been created, we exit
    if (NOT EXISTS "${CMAKE_SOURCE_DIR}/src/libtriton/os/unix/syscalls32.cpp")
        message(FATAL_ERROR "./src/libtriton/os/unix/syscalls32.cpp is missing, please check the INSTALL file")
    endif()
endif(${CMAKE_SYSTEM_NAME} MATCHES "Linux")


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


# Build the SHARED library for *NIX and STATIC for Windows
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux" OR ${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    add_library(${PROJECT_LIBTRITON} SHARED ${LIBTRITON_SOURCE_FILES})
endif(${CMAKE_SYSTEM_NAME} MATCHES "Linux" OR ${CMAKE_SYSTEM_NAME} MATCHES "Darwin")

if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
    add_library(${PROJECT_LIBTRITON} STATIC ${LIBTRITON_SOURCE_FILES})
endif(${CMAKE_SYSTEM_NAME} MATCHES "Windows")

set_target_properties(${PROJECT_LIBTRITON} PROPERTIES COMPILE_FLAGS ${LIBTRITON_CXX_FLAGS})


# Link Triton's dependencies
target_link_libraries(
    ${PROJECT_LIBTRITON}
    ${PYTHON_LIBRARIES}
    ${Boost_LIBRARIES}
    ${Z3_LIBRARIES}
    ${CAPSTONE_LIBRARIES}
)


# Add the install targets
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
    set(TRITON_HEADER_INSTALL /usr/include/triton)
    set(TRITON_LIB_INSTALL /lib)
endif(${CMAKE_SYSTEM_NAME} MATCHES "Linux")

if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    set(TRITON_HEADER_INSTALL /usr/local/include/triton)
    set(TRITON_LIB_INSTALL /usr/local/lib)
endif(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")

if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
    set(TRITON_HEADER_INSTALL C:\\Triton\\include\\triton)
    set(TRITON_LIB_INSTALL C:\\Triton\\lib)
endif(${CMAKE_SYSTEM_NAME} MATCHES "Windows")

install (TARGETS ${PROJECT_LIBTRITON} DESTINATION ${TRITON_LIB_INSTALL})
install (FILES ${LIBTRITON_HEADERS_FILES} DESTINATION ${TRITON_HEADER_INSTALL})






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
        endif(${ARCHITECTURE} STREQUAL "i386")

        if(${ARCHITECTURE} STREQUAL "amd64")
            set(PINTOOL_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DBIGARRAY_MULTIPLIER=1 -DUSING_XED -DTARGET_IA32E -DHOST_IA32E -DTARGET_LINUX -D_GLIBCXX_USE_CXX11_ABI=0")
        endif(${ARCHITECTURE} STREQUAL "amd64")

        set(PINTOOL_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -Wl,--hash-style=sysv -Wl,-Bsymbolic -fPIC")
    endif(${CMAKE_SYSTEM_NAME} MATCHES "Linux")


    # Specific OSX CXX Flags
    if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
        if(${ARCHITECTURE} STREQUAL "i386")
            set(PINTOOL_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DBIGARRAY_MULTIPLIER=1 -DTARGET_IA32 -DHOST_IA32E -DTARGET_MAC")
        endif(${ARCHITECTURE} STREQUAL "i386")

        if(${ARCHITECTURE} STREQUAL "amd64")
            set(PINTOOL_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DBIGARRAY_MULTIPLIER=1 -DTARGET_IA32E -DHOST_IA32E -DTARGET_MAC")
        endif(${ARCHITECTURE} STREQUAL "amd64")

        set(PINTOOL_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -Wl,-Bsymbolic -fPIC")
    endif(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")


    # Specific Windows CXX Flags
    if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
        if(${ARCHITECTURE} STREQUAL "i386")
            set(PINTOOL_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DBIGARRAY_MULTIPLIER=1 -DUSING_XED -DTARGET_IA32 -DHOST_IA32 -DTARGET_WINDOWS -D_SECURE_SCL=0 -DHAVE_ROUND /MT")
        endif(${ARCHITECTURE} STREQUAL "i386")

        if(${ARCHITECTURE} STREQUAL "amd64")
            set(PINTOOL_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DBIGARRAY_MULTIPLIER=1 -DUSING_XED -DTARGET_IA32E -DHOST_IA32E -DTARGET_WINDOWS -D_SECURE_SCL=0 -DHAVE_ROUND /MT")
        endif(${ARCHITECTURE} STREQUAL "amd64")

        set(PINTOOL_SHARED_LINKER_FLAGS " ")
    endif(${CMAKE_SYSTEM_NAME} MATCHES "Windows")


    # Global UNIX CXX Flags
    if(CMAKE_COMPILER_IS_GNUCXX)
        set(PINTOOL_CXX_FLAGS "${PINTOOL_CXX_FLAGS} -std=c++11 -fabi-version=2")
    elseif("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang")
        set(PINTOOL_CXX_FLAGS "${PINTOOL_CXX_FLAGS} -std=c++11")
    endif()


    # Includes directories (Pin)
    if(${ARCHITECTURE} STREQUAL "i386")
        include_directories("${PIN_ROOT}/extras/xed-ia32/include")
    endif(${ARCHITECTURE} STREQUAL "i386")

    if(${ARCHITECTURE} STREQUAL "amd64")
        include_directories("${PIN_ROOT}/extras/xed-intel64/include")
    endif(${ARCHITECTURE} STREQUAL "amd64")

    include_directories("${PIN_ROOT}/source/include/pin")
    include_directories("${PIN_ROOT}/source/include/pin/gen")
    include_directories("${PIN_ROOT}/extras/components/include")
    include_directories("${PIN_ROOT}/source/tools/InstLib")


    # Libs directories (Pin)
    if(${ARCHITECTURE} STREQUAL "i386")
        link_directories("${PIN_ROOT}/ia32/lib")
        link_directories("${PIN_ROOT}/ia32/lib-ext")
        link_directories("${PIN_ROOT}/extras/xed-ia32/lib")
    endif(${ARCHITECTURE} STREQUAL "i386")

    if(${ARCHITECTURE} STREQUAL "amd64")
        link_directories("${PIN_ROOT}/intel64/lib")
        link_directories("${PIN_ROOT}/intel64/lib-ext")
        link_directories("${PIN_ROOT}/extras/xed-intel64/lib")
    endif(${ARCHITECTURE} STREQUAL "amd64")

    if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
        if(${ARCHITECTURE} STREQUAL "i386")
            link_directories("${PIN_ROOT}/ia32/runtime/glibc")
        endif(${ARCHITECTURE} STREQUAL "i386")
        if(${ARCHITECTURE} STREQUAL "amd64")
            link_directories("${PIN_ROOT}/intel64/runtime/glibc")
        endif(${ARCHITECTURE} STREQUAL "amd64")
    endif(${CMAKE_SYSTEM_NAME} MATCHES "Linux")


    # To prevent error c2872 ambiguous symbol in Windows we need to change the (U?INT\d+?) variables to PIN_(U?INT\d+?) in PIN.
    # We wrote a python script to do it for you.
    if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
        execute_process(COMMAND python ${CMAKE_SOURCE_DIR}/src/scripts/replace_UINT_PIN.py ${PIN_ROOT})
    endif(${CMAKE_SYSTEM_NAME} MATCHES "Windows")


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
    endif(${CMAKE_SYSTEM_NAME} MATCHES "Linux" OR ${CMAKE_SYSTEM_NAME} MATCHES "Darwin")

    if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
        if(${ARCHITECTURE} STREQUAL "i386")
            target_link_libraries(${PROJECT_PINTOOL} pin pinvm xed ntdll-32 ${PROJECT_LIBTRITON})
        endif(${ARCHITECTURE} STREQUAL "i386")
        if(${ARCHITECTURE} STREQUAL "amd64")
            target_link_libraries(${PROJECT_PINTOOL} pin pinvm xed ntdll-64 ${PROJECT_LIBTRITON})
        endif(${ARCHITECTURE} STREQUAL "amd64")
    endif(${CMAKE_SYSTEM_NAME} MATCHES "Windows")


    # Generate the triton's shortcut script
    set(PIN_BIN_PATH ${PIN_ROOT}/pin.sh)
    set(PINTOOL_PATH ${CMAKE_BINARY_DIR}/${CMAKE_SHARED_LIBRARY_PREFIX}${PROJECT_PINTOOL}${CMAKE_SHARED_LIBRARY_SUFFIX})
    set(FLAG_IFEELLUCKY "")


    # Pin flag for kernel 4.x
    if(KERNEL4)
        set(FLAG_IFEELLUCKY "-ifeellucky")
    endif(KERNEL4)


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
    endif(${CMAKE_SYSTEM_NAME} MATCHES "Linux" OR ${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
endif(PINTOOL)

