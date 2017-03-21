##################################################################################### CMake libpintool

set(PROJECT_PINTOOL "pintool")
add_definitions(-DTRITON_PINTOOL)

# Root directory of the Pin toolkit
set(PIN_ROOT "${CMAKE_SOURCE_DIR}/../../.." CACHE PATH "Path to pin root directory")

# Specific Linux CXX Flags
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
    if(${ARCHITECTURE} STREQUAL "i386")
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DBIGARRAY_MULTIPLIER=1 -DUSING_XED -DTARGET_IA32 -DHOST_IA32 -DTARGET_LINUX -m32 -D_GLIBCXX_USE_CXX11_ABI=0 -fPIC")
    endif()

    if(${ARCHITECTURE} STREQUAL "amd64")
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DBIGARRAY_MULTIPLIER=1 -DUSING_XED -DTARGET_IA32E -DHOST_IA32E -DTARGET_LINUX -D_GLIBCXX_USE_CXX11_ABI=0 -fPIC")
    endif()

    set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -Wl,--hash-style=sysv -Wl,-Bsymbolic -fPIC")
endif()


# Specific OSX CXX Flags
if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    if(${ARCHITECTURE} STREQUAL "i386")
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DBIGARRAY_MULTIPLIER=1 -DTARGET_IA32 -DHOST_IA32E -DTARGET_MAC")
    endif()

    if(${ARCHITECTURE} STREQUAL "amd64")
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DBIGARRAY_MULTIPLIER=1 -DTARGET_IA32E -DHOST_IA32E -DTARGET_MAC")
    endif()

    set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -Wl,-Bsymbolic -fPIC")
endif()


# Specific Windows CXX Flags
if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
    if(${ARCHITECTURE} STREQUAL "i386")
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DBIGARRAY_MULTIPLIER=1 -DUSING_XED -DTARGET_IA32 -DHOST_IA32 -DTARGET_WINDOWS -D_SECURE_SCL=0 -DHAVE_ROUND /MT")
    endif()

    if(${ARCHITECTURE} STREQUAL "amd64")
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DBIGARRAY_MULTIPLIER=1 -DUSING_XED -DTARGET_IA32E -DHOST_IA32E -DTARGET_WINDOWS -D_SECURE_SCL=0 -DHAVE_ROUND /MT")
    endif()

    set(CMAKE_SHARED_LINKER_FLAGS " ")
endif()


# Global UNIX CXX Flags
if(CMAKE_COMPILER_IS_GNUCXX)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11 -fabi-version=2")
elseif("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")
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
file(
    GLOB_RECURSE
    PINTOOL_SOURCE_FILES
    ${CMAKE_SOURCE_DIR}/src/tracer/pin/*
)

add_library(${PROJECT_PINTOOL} SHARED ${PINTOOL_SOURCE_FILES})

if(${CMAKE_SYSTEM_NAME} MATCHES "Linux" OR ${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    target_link_libraries(${PROJECT_PINTOOL} pin xed pindwarf dl ${PROJECT_LIBTRITON})
elseif(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
    if(${ARCHITECTURE} STREQUAL "i386")
        target_link_libraries(${PROJECT_PINTOOL} pin pinvm xed ntdll-32 ${PROJECT_LIBTRITON})
    endif()
    if(${ARCHITECTURE} STREQUAL "amd64")
        target_link_libraries(${PROJECT_PINTOOL} pin pinvm xed ntdll-64 ${PROJECT_LIBTRITON})
    endif()
endif()


# Generate the triton's shortcut script
set(PIN_BIN_PATH ${PIN_ROOT}/pin.sh)
set(PINTOOL_PATH ${CMAKE_CURRENT_BINARY_DIR}/${CMAKE_SHARED_LIBRARY_PREFIX}${PROJECT_PINTOOL}${CMAKE_SHARED_LIBRARY_SUFFIX})
set(FLAG_IFEELLUCKY "")


# Pin flag for kernel 4.x
if(KERNEL4)
    set(FLAG_IFEELLUCKY "-ifeellucky")
endif()


# Generate Triton pintool script
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux" OR ${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    configure_file(
        ${CMAKE_SOURCE_DIR}/src/scripts/triton.in
        ${CMAKE_BINARY_DIR}/triton
        IMMEDIATE @ONLY
    )

    configure_file(
        ${CMAKE_SOURCE_DIR}/src/scripts/tritonAttach.in
        ${CMAKE_BINARY_DIR}/tritonAttach
        IMMEDIATE @ONLY
    )
endif()
