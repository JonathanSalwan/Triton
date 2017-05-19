# Define if the library will be STATIC or DYNAMIC
if(STATICLIB)
    set(LIBTRITON_KIND_LINK STATIC)
else()
    set(LIBTRITON_KIND_LINK SHARED)
endif()

# Default flags
# To fix old python version bug http://bugs.python.org/issue21958
if(${CMAKE_SYSTEM_NAME} MATCHES "Windows" AND NOT ${CMAKE_CXX_COMPILER_ID} MATCHES "GNU")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DHAVE_ROUND /MT")
endif()

if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
  set(PYTHON_SUFFIX .pyd)
else()
  set(PYTHON_SUFFIX .so)
endif()

# Global UNIX CXX Flags
if(CMAKE_COMPILER_IS_GNUCXX OR ${CMAKE_CXX_COMPILER_ID} MATCHES "Clang")
    # Flags
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra -Werror -Wno-unused-parameter -Wno-unknown-pragmas -Wno-tautological-compare")
    if(NOT GCOV)
      set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O3")
    endif()
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-stack-protector -fomit-frame-pointer -fno-strict-aliasing")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fPIC -std=c++11")
endif()

# 32-bits
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux" OR ${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    if(${ARCHITECTURE} STREQUAL "i386")
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -m32")
    endif()
endif()

# Add Triton includes
include_directories("${CMAKE_SOURCE_DIR}/src/libtriton/includes")
include_directories("${CMAKE_BINARY_DIR}/src/libtriton/includes")

# Define all source files
set(LIBTRITON_SOURCE_FILES
  api/api.cpp
  arch/architecture.cpp
  arch/immediate.cpp
  arch/irBuilder.cpp
  arch/operandWrapper.cpp
  arch/registerSpecification.cpp
  arch/bitsVector.cpp
  arch/instruction.cpp
  arch/memoryAccess.cpp
  arch/register.cpp
  arch/x86/x8664Cpu.cpp
  arch/x86/x86Cpu.cpp
  arch/x86/x86Semantics.cpp
  arch/x86/x86Specifications.cpp
  ast/ast.cpp
  ast/astDictionaries.cpp
  ast/astGarbageCollector.cpp
  ast/representations/astPythonRepresentation.cpp
  ast/representations/astRepresentation.cpp
  ast/representations/astSmtRepresentation.cpp
  ast/z3/tritonToZ3Ast.cpp
  ast/z3/z3Interface.cpp
  ast/z3/z3Result.cpp
  ast/z3/z3ToTritonAst.cpp
  callbacks/callbacks.cpp
  engines/solver/solverEngine.cpp
  engines/solver/solverModel.cpp
  engines/symbolic/pathConstraint.cpp
  engines/symbolic/pathManager.cpp
  engines/symbolic/symbolicEngine.cpp
  engines/symbolic/symbolicExpression.cpp
  engines/symbolic/symbolicSimplification.cpp
  engines/symbolic/symbolicVariable.cpp
  engines/taint/taintEngine.cpp
  format/abstractBinary.cpp
  format/elf/elf.cpp
  format/elf/elfDynamicTable.cpp
  format/elf/elfHeader.cpp
  format/elf/elfProgramHeader.cpp
  format/elf/elfRelocationTable.cpp
  format/elf/elfSectionHeader.cpp
  format/elf/elfSymbolTable.cpp
  format/memoryMapping.cpp
  format/pe/peBuilder.cpp
  format/pe/pe.cpp
  format/pe/peDataDirectory.cpp
  format/pe/peExportDirectory.cpp
  format/pe/peFileHeader.cpp
  format/pe/peHeader.cpp
  format/pe/peImportDirectory.cpp
  format/pe/peOptionalHeader.cpp
  format/pe/peSectionHeader.cpp
  modes/modes.cpp
  os/unix/syscallNumberToString.cpp
  utils/coreUtils.cpp
)

if(PYTHON_BINDINGS)
    set(LIBTRITON_PYTHON_SOURCE_FILES
      bindings/python/init.cpp
      bindings/python/modules/astCallbacks.cpp
      bindings/python/modules/tritonCallbacks.cpp
      bindings/python/namespaces/initArchNamespace.cpp
      bindings/python/namespaces/initAstNodeNamespace.cpp
      bindings/python/namespaces/initAstRepresentationNamespace.cpp
      bindings/python/namespaces/initCallbackNamespace.cpp
      bindings/python/namespaces/initCpuSizeNamespace.cpp
      bindings/python/namespaces/initElfNamespace.cpp
      bindings/python/namespaces/initModeNamespace.cpp
      bindings/python/namespaces/initOperandNamespace.cpp
      bindings/python/namespaces/initPeNamespace.cpp
      bindings/python/namespaces/initRegNamespace.cpp
      bindings/python/namespaces/initSymExprNamespace.cpp
      bindings/python/namespaces/initSyscallNamespace.cpp
      bindings/python/namespaces/initVersionNamespace.cpp
      bindings/python/namespaces/initX86OpcodesNamespace.cpp
      bindings/python/namespaces/initX86PrefixesNamespace.cpp
      bindings/python/objects/pyAstNode.cpp
      bindings/python/objects/pyBitvector.cpp
      bindings/python/objects/pyElf.cpp
      bindings/python/objects/pyElfDynamicTable.cpp
      bindings/python/objects/pyElfHeader.cpp
      bindings/python/objects/pyElfProgramHeader.cpp
      bindings/python/objects/pyElfRelocationTable.cpp
      bindings/python/objects/pyElfSectionHeader.cpp
      bindings/python/objects/pyElfSymbolTable.cpp
      bindings/python/objects/pyImmediate.cpp
      bindings/python/objects/pyInstruction.cpp
      bindings/python/objects/pyMemoryAccess.cpp
      bindings/python/objects/pyPathConstraint.cpp
      bindings/python/objects/pyPe.cpp
      bindings/python/objects/pyPeExportEntry.cpp
      bindings/python/objects/pyPeExportTable.cpp
      bindings/python/objects/pyPeHeader.cpp
      bindings/python/objects/pyPeImportLookup.cpp
      bindings/python/objects/pyPeImportTable.cpp
      bindings/python/objects/pyPeSectionHeader.cpp
      bindings/python/objects/pyRegister.cpp
      bindings/python/objects/pySolverModel.cpp
      bindings/python/objects/pySymbolicExpression.cpp
      bindings/python/objects/pySymbolicVariable.cpp
      bindings/python/pyXFunctions.cpp
      bindings/python/utils.cpp
    )
else()
    set(LIBTRITON_PYTHON_SOURCE_FILES)
endif()

# Triton have to generate a syscalls table from the kernel source
# This following code tries to find the unistd_64.h or unistd_32.h header depending on the architecture.
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
    FILE(GLOB_RECURSE syscalls32_table_files /usr/include/*unistd_32.h)
    FILE(GLOB_RECURSE syscalls64_table_files /usr/include/*unistd_64.h)
endif()

if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    FILE(GLOB_RECURSE syscalls64_table_files /usr/include/sys/syscall.h)
endif()

# Create syscall generted file directory
file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/os/unix/)

set(EXTRACT_SYSCALL_SCRIPT ${CMAKE_SOURCE_DIR}/src/scripts/extract_syscall.py)

macro(gen_syscall bits)
    LIST(GET syscalls${bits}_table_files 0 syscalls${bits}_table_file)
    # If the unistd_64.h or syscall.h is not found, we exit
    if(NOT EXISTS ${syscalls${bits}_table_file})
        message(FATAL_ERROR "unistd_${bits}.h or syscall.h is missing")
    endif()

    set(OUT_SYSCALL${bits} ${CMAKE_CURRENT_BINARY_DIR}/os/unix/syscalls${bits}.cpp)

    # We generate the syscalls${bits}.cpp from the unistd_${bits}.h or syscall.h.
    # Added python after COMMAND since to be sure that if ${CMAKE_SOURCE_DIR}/src/scripts/extract_syscall.py doesn't have X rights it gets executed
    add_custom_command(
      OUTPUT ${OUT_SYSCALL${bits}}
      COMMAND ${PYTHON_EXECUTABLE} ${EXTRACT_SYSCALL_SCRIPT} ${syscalls${bits}_table_file} ${bits} > ${OUT_SYSCALL${bits}}
      MAIN_DEPENDENCY ${EXTRACT_SYSCALL_SCRIPT}
      DEPENDS ${syscalls${bits}_table_file}
    )
    add_custom_target(gen-syscall${bits} DEPENDS ${OUT_SYSCALL${bits}})
    set(LIBTRITON_SOURCE_FILES ${LIBTRITON_SOURCE_FILES} ${OUT_SYSCALL${bits}})
endmacro()

# Note: Windows ?!
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux" OR ${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    gen_syscall(64)
else()
    add_custom_target(gen-syscall64
      COMMAND echo "No syscall64 to extract on your plateform")
endif()

# Syscall 32 is only available for linux users
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
    gen_syscall(32)
else()
    add_custom_target(gen-syscall32
      COMMAND echo "No syscall32 to extract on your plateform")
endif()

# We generate the version numbers information
configure_file(
    ${CMAKE_CURRENT_SOURCE_DIR}/includes/triton/version.hpp.in
    ${CMAKE_CURRENT_BINARY_DIR}/includes/triton/version.hpp
    IMMEDIATE @ONLY
)

# Define gloabl shared linker flags
set(LIBTRITON_SHARED_LINKER_FLAGS " ")

# Special cases for MinGW
if(${CMAKE_SYSTEM_NAME} MATCHES "Windows" AND ${CMAKE_CXX_COMPILER_ID} MATCHES "GNU")
    set(LIBTRITON_OTHER_LIBS "-lgomp")
    if (NOT STATICLIB)
      set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -Wl,--export-all-symbols")
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
add_library(${PROJECT_LIBTRITON} ${LIBTRITON_KIND_LINK} ${LIBTRITON_SOURCE_FILES} ${LIBTRITON_PYTHON_SOURCE_FILES})
add_dependencies(${PROJECT_LIBTRITON} gen-syscall32 gen-syscall64)

# Link Triton's dependencies
target_link_libraries(
    ${PROJECT_LIBTRITON}
    ${PYTHON_LIBRARIES}
    ${Boost_LIBRARIES}
    ${Z3_LIBRARIES}
    ${CAPSTONE_LIBRARIES}
    ${LIBTRITON_OTHER_LIBS}
)
add_dependencies(check triton)

# Add the install targets
install (TARGETS ${PROJECT_LIBTRITON} DESTINATION lib)
install (DIRECTORY ${CMAKE_SOURCE_DIR}/src/libtriton/includes/triton DESTINATION include)
install (DIRECTORY ${CMAKE_BINARY_DIR}/src/libtriton/includes/triton DESTINATION include)

# Install Python bindings
if(PYTHON_BINDINGS)
    add_custom_target(python-triton ALL
      COMMAND ${CMAKE_COMMAND} -E copy "${CMAKE_CURRENT_BINARY_DIR}/${CMAKE_CFG_INTDIR}/${CMAKE_SHARED_MODULE_PREFIX}triton${CMAKE_SHARED_LIBRARY_SUFFIX}" "${CMAKE_CURRENT_BINARY_DIR}/${CMAKE_CFG_INTDIR}/triton${PYTHON_SUFFIX}"
      DEPENDS triton
    )

    execute_process (COMMAND ${PYTHON_EXECUTABLE} -c "from distutils.sysconfig import get_python_lib; print get_python_lib()" OUTPUT_VARIABLE PYTHON_SITE_PACKAGES OUTPUT_STRIP_TRAILING_WHITESPACE)
    if(${CMAKE_SYSTEM_NAME} MATCHES "Windows" AND NOT ${CMAKE_CXX_COMPILER_ID} MATCHES "GNU")
        install (FILES ${CMAKE_CURRENT_BINARY_DIR}/\${CMAKE_INSTALL_CONFIG_NAME}/triton${PYTHON_SUFFIX} DESTINATION ${PYTHON_SITE_PACKAGES})
    else()
        install (FILES ${CMAKE_CURRENT_BINARY_DIR}/triton${PYTHON_SUFFIX} DESTINATION ${PYTHON_SITE_PACKAGES})
    endif()
endif()

