cmake_minimum_required(VERSION 2.8)
project(triton)

# Get and increment the build number
file(READ ${CMAKE_SOURCE_DIR}/.build_number BUILD_NUMBER)
math(EXPR NEW_BUILD_NUMBER "${BUILD_NUMBER} + 1")
file(WRITE ${CMAKE_SOURCE_DIR}/.build_number ${NEW_BUILD_NUMBER})

# Triton version
set(VERSION_MAJOR 0)
set(VERSION_MINOR 0)
set(VERSION_BUILD ${BUILD_NUMBER})

set(CMAKE_BUILD_TYPE Release)
set(PROJECT_NAME "triton")

# Root directory of the Pin toolkit
set(PIN_ROOT "${CMAKE_SOURCE_DIR}/../../..")

# Global UNIX CXX Flags
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Werror -Wno-unknown-pragmas")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O3")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${FLAG_CXX}")

# Specific Linux CXX Flags
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DBIGARRAY_MULTIPLIER=1 -DUSING_XED -DTARGET_IA32E -DHOST_IA32E -DTARGET_LINUX")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-stack-protector -fomit-frame-pointer -fno-strict-aliasing")
    set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -Wl,--hash-style=sysv -Wl,-Bsymbolic")
endif(${CMAKE_SYSTEM_NAME} MATCHES "Linux")

# Specific OSX CXX Flags
if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DBIGARRAY_MULTIPLIER=1 -DTARGET_IA32E -DHOST_IA32E -DTARGET_MAC")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fomit-frame-pointer -fno-strict-aliasing")
    set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -Wl,-exported_symbols_list")
endif(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")

# Conventions
add_definitions(-fPIC)
add_definitions(-std=c++11)

# Includes directories (Pin and Triton)
include_directories("${PIN_ROOT}/source/include/pin")
include_directories("${PIN_ROOT}/source/include/pin/gen")
include_directories("${PIN_ROOT}/extras/components/include")
include_directories("${PIN_ROOT}/extras/xed-intel64/include")
include_directories("${PIN_ROOT}/source/tools/InstLib")
include_directories("./src/includes")

# Libs directories (Pin)
link_directories("${PIN_ROOT}/intel64/lib")
link_directories("${PIN_ROOT}/intel64/lib-ext")
link_directories("${PIN_ROOT}/intel64/runtime/glibc")
link_directories("${PIN_ROOT}/extras/xed-intel64/lib")

# Triton have to generate a syscalls table from the kernel source
# This following code tries to find the unistd_64.h header.
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
    FILE(
        GLOB_RECURSE
        syscalls_table_files
        /usr/include/*unistd_64.h
    )
endif(${CMAKE_SYSTEM_NAME} MATCHES "Linux")

if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    FILE(
        GLOB_RECURSE
        syscalls_table_files
        /usr/include/sys/syscall.h
    )
endif(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")

LIST(GET syscalls_table_files 0 syscalls_table_file)

# If the unistd_64.h or syscall.h is not found, we exit
if (NOT EXISTS ${syscalls_table_file})
    message(FATAL_ERROR "unistd_64.h or syscall.h is missing, please check the INSTALL file")
endif()

# We generate the syscalls.cpp from the unistd_64.h
execute_process(
    COMMAND ${CMAKE_SOURCE_DIR}/scripts/extract_syscall.py ${syscalls_table_file}
    OUTPUT_FILE ${CMAKE_SOURCE_DIR}/src/utils/syscalls.cpp
)

# If the syscalls.cpp has not been created, we exit
if (NOT EXISTS "${CMAKE_SOURCE_DIR}/src/utils/syscalls.cpp")
    message(FATAL_ERROR "./src/utils/syscalls.cpp is missing, please check the INSTALL file")
endif()

# We generate the version numbers information
configure_file(
    ${CMAKE_SOURCE_DIR}/src/includes/Version.h.in
    ${CMAKE_SOURCE_DIR}/src/includes/Version.h
)

# Define all source files
file(
    GLOB_RECURSE
    triton_source_files
    ./src/*
)

# Build the pintool as shared library
add_library(${PROJECT_NAME} SHARED ${triton_source_files})

# Link Triton's dependencies and Pin lib
target_link_libraries(
    ${PROJECT_NAME}
    pin
    xed
    pindwarf
    dl
    z3
    python2.7
    boost_filesystem
)

# Generate the triton's shortcut script
set(PIN_BIN_PATH ${PIN_ROOT}/pin.sh)
set(TRITON_LIB_PATH ${CMAKE_BINARY_DIR}/${CMAKE_SHARED_LIBRARY_PREFIX}${PROJECT_NAME}${CMAKE_SHARED_LIBRARY_SUFFIX})
configure_file(
    ${CMAKE_SOURCE_DIR}/scripts/triton.in
    ${CMAKE_SOURCE_DIR}/triton
    IMMEDIATE @ONLY
)

