cmake_minimum_required(VERSION 2.8)
project(triton)

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
set(VERSION_MINOR 2)
set(VERSION_BUILD ${BUILD_NUMBER})

set(CMAKE_BUILD_TYPE Release)
set(PROJECT_NAME "triton")

# Custom cmake search
list(APPEND CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/CMakeModules/")

# Root directory of the Pin toolkit
set(PIN_ROOT "${CMAKE_SOURCE_DIR}/../../..")

# Global UNIX CXX Flags
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Werror -Wno-unknown-pragmas")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O3")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${FLAG_CXX}")

# Specific Linux CXX Flags
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
    if(${ARCHITECTURE} STREQUAL "i386")
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DBIGARRAY_MULTIPLIER=1 -DUSING_XED -DTARGET_IA32 -DHOST_IA32 -DTARGET_LINUX -m32")
    endif(${ARCHITECTURE} STREQUAL "i386")
    if(${ARCHITECTURE} STREQUAL "amd64")
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DBIGARRAY_MULTIPLIER=1 -DUSING_XED -DTARGET_IA32E -DHOST_IA32E -DTARGET_LINUX")
    endif(${ARCHITECTURE} STREQUAL "amd64")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-stack-protector -fomit-frame-pointer -fno-strict-aliasing -fabi-version=2 -D_GLIBCXX_USE_CXX11_ABI=0")
    set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -Wl,--hash-style=sysv -Wl,-Bsymbolic")
endif(${CMAKE_SYSTEM_NAME} MATCHES "Linux")

# Specific OSX CXX Flags
if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    if(${ARCHITECTURE} STREQUAL "i386")
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DBIGARRAY_MULTIPLIER=1 -DTARGET_IA32 -DHOST_IA32E -DTARGET_MAC")
    endif(${ARCHITECTURE} STREQUAL "i386")
    if(${ARCHITECTURE} STREQUAL "amd64")
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DBIGARRAY_MULTIPLIER=1 -DTARGET_IA32E -DHOST_IA32E -DTARGET_MAC")
    endif(${ARCHITECTURE} STREQUAL "amd64")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fomit-frame-pointer -fno-strict-aliasing")
    set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS}")
    if(POLICY CMP0025)
        cmake_policy(SET CMP0025 OLD) # report Apple's Clang as just Clang
    endif()
    if(POLICY CMP0042)
        cmake_policy(SET CMP0042 NEW) # MACOSX_RPATH
    endif()
endif(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")

# Conventions
add_definitions(-fPIC)
add_definitions(-std=c++11)

# Find Python 2.7
find_package(PythonLibs 2.7 REQUIRED)
include_directories(${PYTHON_INCLUDE_DIRS})

# Find boost
find_package(Boost 1.53.0 REQUIRED)
include_directories(${Boost_INCLUDE_DIRS})

# Check if the user want a light version of Triton
if(${LIGHT_VERSION} MATCHES "yes")
    # define LIGHT_VERSION
    add_definitions(-DLIGHT_VERSION)
else()
    # Find Z3
    find_package(Z3 REQUIRED)
    include_directories(${Z3_INCLUDE_DIRS})
    if (NOT Z3_FOUND)
        message(FATAL_ERROR "Z3 not found")
    endif()
endif()

# Includes directories (Pin and Triton)
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
include_directories("./src/includes")

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

# Triton have to generate a syscalls table from the kernel source
# This following code tries to find the unistd_64.h or unistd_32.h header depending on the architecture.
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
    if(ARCHITECTURE STREQUAL "i386")
        FILE(GLOB_RECURSE syscalls_table_files /usr/include/*unistd_32.h)
    endif(ARCHITECTURE STREQUAL "i386")
    if(ARCHITECTURE STREQUAL "amd64")
        FILE(GLOB_RECURSE syscalls_table_files /usr/include/*unistd_64.h)
    endif(ARCHITECTURE STREQUAL "amd64")
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

# We generate the syscalls.cpp from the unistd_64.h or unistd_64.h.
# Added python after COMMAND since to be sure that if ${CMAKE_SOURCE_DIR}/scripts/extract_syscall.py doesn't have X rights it gets executed
execute_process(
    COMMAND python ${CMAKE_SOURCE_DIR}/scripts/extract_syscall.py ${syscalls_table_file}
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
    ${PYTHON_LIBRARIES}
    ${Boost_LIBRARIES}
)

# Link Triton's dependencies and Pin lib if it's not the light version
if(NOT LIGHT_VERSION)
    target_link_libraries(
        ${PROJECT_NAME}
        ${Z3_LIBRARIES}
    )
endif()

# Generate the triton's shortcut script
set(PIN_BIN_PATH ${PIN_ROOT}/pin.sh)
set(TRITON_LIB_PATH ${CMAKE_BINARY_DIR}/${CMAKE_SHARED_LIBRARY_PREFIX}${PROJECT_NAME}${CMAKE_SHARED_LIBRARY_SUFFIX})
set(FLAG_IFEELLUCKY "")

if(${KERNEL4} MATCHES "yes")
    set(FLAG_IFEELLUCKY "-ifeellucky")
endif()

configure_file(
    ${CMAKE_SOURCE_DIR}/scripts/triton.in
    ${CMAKE_SOURCE_DIR}/triton
    IMMEDIATE @ONLY
)

configure_file(
    ${CMAKE_SOURCE_DIR}/scripts/tritonAttach.in
    ${CMAKE_SOURCE_DIR}/tritonAttach
    IMMEDIATE @ONLY
)

