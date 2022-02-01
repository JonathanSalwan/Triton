# - Try to find LLVM
# Once done, this will define
#
#  LLVM_INCLUDE_DIRS - the LLVM include directories
#  LLVM_LIBRARIES - link these to use LLVM

if(NOT LLVM_INCLUDE_DIRS)
    set(LLVM_INCLUDE_DIRS "$ENV{LLVM_INCLUDE_DIRS}")
endif()

if(NOT LLVM_LIBRARIES)
    set(LLVM_LIBRARIES "$ENV{LLVM_LIBRARIES}")
endif()

if(NOT LLVM_INCLUDE_DIRS AND NOT LLVM_LIBRARIES)
    message(FATAL_ERROR "LLVM not found")
else()
    message(STATUS "LLVM includes directory defined: ${LLVM_INCLUDE_DIRS}")
    message(STATUS "LLVM libraries defined: ${LLVM_LIBRARIES}")
endif()
