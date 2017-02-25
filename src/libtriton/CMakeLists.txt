# Define if the library will be STATIC or DYNAMIC
if(STATICLIB)
    set(LIBTRITON_KIND_LINK STATIC)
else()
    set(LIBTRITON_KIND_LINK SHARED)
endif()

# Python bindings option
if(PYTHON_BINDINGS)
    add_definitions(-DTRITON_PYTHON_BINDINGS)
endif()


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
    ${CMAKE_SOURCE_DIR}/src/libtriton/includes/triton/version.hpp.in
    ${CMAKE_SOURCE_DIR}/src/libtriton/includes/triton/version.hpp
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
    ${CMAKE_SOURCE_DIR}/src/libtriton/includes/triton/*
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

# Find boost
find_package(Boost 1.55.0 REQUIRED)
include_directories("${Boost_INCLUDE_DIRS}")


# Define library's properties
add_library(${PROJECT_LIBTRITON} ${LIBTRITON_KIND_LINK} ${LIBTRITON_SOURCE_FILES})
set_target_properties("${PROJECT_LIBTRITON}" PROPERTIES COMPILE_FLAGS "${LIBTRITON_CXX_FLAGS}")
set_target_properties("${PROJECT_LIBTRITON}" PROPERTIES LINK_FLAGS "${LIBTRITON_SHARED_LINKER_FLAGS}")


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
install (TARGETS ${PROJECT_LIBTRITON} DESTINATION lib)
install (FILES ${LIBTRITON_HEADERS_FILES} DESTINATION include)


# Install Python bindings
if(PYTHON_BINDINGS)
    configure_file(
        ${CMAKE_SOURCE_DIR}/src/scripts/setup.py.in
        ${CMAKE_BINARY_DIR}/setup.py
        IMMEDIATE @ONLY
    )
    find_package(PythonInterp 2.7 REQUIRED)
    install (CODE "execute_process(COMMAND ${PYTHON_EXECUTABLE} ${CMAKE_BINARY_DIR}/setup.py install)")
endif()

