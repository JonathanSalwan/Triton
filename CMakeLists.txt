cmake_minimum_required(VERSION 2.6)
project(triton)

set(VERSION_MAJOR 0)
set(VERSION_MINOR 1)
set(VERSION_PATCH 1)

set(CMAKE_BUILD_TYPE Release)
set(PROJECT_NAME "triton")
set(PIN_ROOT "${CMAKE_SOURCE_DIR}/../../..")

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Werror -Wno-unknown-pragmas")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O3")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${FLAG_CXX}")

if(CMAKE_COMPILER_IS_GNUCXX)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DBIGARRAY_MULTIPLIER=1 -DUSING_XED -DTARGET_IA32E -DHOST_IA32E -DTARGET_LINUX")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-stack-protector -fomit-frame-pointer -fno-strict-aliasing")
    set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -Wl,--hash-style=sysv -Wl,-Bsymbolic")
endif(CMAKE_COMPILER_IS_GNUCXX)

add_definitions(-fPIC)
add_definitions(-std=c++11)

include_directories("${PIN_ROOT}/source/include/pin")
include_directories("${PIN_ROOT}/source/include/pin/gen")
include_directories("${PIN_ROOT}/extras/components/include")
include_directories("${PIN_ROOT}/extras/xed-intel64/include")
include_directories("${PIN_ROOT}/source/tools/InstLib")
include_directories("./src/includes")

link_directories("${PIN_ROOT}/intel64/lib")
link_directories("${PIN_ROOT}/intel64/lib-ext")
link_directories("${PIN_ROOT}/intel64/runtime/glibc")
link_directories("${PIN_ROOT}/extras/xed-intel64/lib")

FILE(
    GLOB_RECURSE
    syscalls_table_file
    /usr/include/*/unistd_64.h
)

if (NOT EXISTS ${syscalls_table_file})
    message(FATAL_ERROR "unistd_64.h is missing, please check the INSTALL file")
endif()

execute_process(
    COMMAND ${CMAKE_SOURCE_DIR}/scripts/extract_syscall.py ${syscalls_table_file}
    OUTPUT_FILE ${CMAKE_SOURCE_DIR}/src/utils/syscalls.cpp
)

if (NOT EXISTS "${CMAKE_SOURCE_DIR}/src/utils/syscalls.cpp")
    message(FATAL_ERROR "./src/utils/syscalls.cpp is missing, please check the INSTALL file")
endif()

file(
    GLOB_RECURSE
    triton_source_files
    ./src/*
)

add_library(${PROJECT_NAME} SHARED ${triton_source_files})

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

execute_process(
    COMMAND cp ${CMAKE_SOURCE_DIR}/scripts/triton ${CMAKE_SOURCE_DIR}/triton
    COMMAND sed -i s@TRITON_LIB_PATH=@TRITON_LIB_PATH=${CMAKE_BINARY_DIR}/${CMAKE_SHARED_LIBRARY_PREFIX}${PROJECT_NAME}${CMAKE_SHARED_LIBRARY_SUFFIX}@g ${CMAKE_SOURCE_DIR}/triton
    COMMAND sed -i s@PIN_BIN_PATH=@PIN_BIN_PATH=${PIN_ROOT}/pin.sh@g ${CMAKE_SOURCE_DIR}/triton
    COMMAND chmod 755 ${CMAKE_SOURCE_DIR}/triton
)

