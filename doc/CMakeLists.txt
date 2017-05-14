##
##  Copyright (C) - Triton
##
##  This program is under the terms of the BSD License.
##

##################################################################################### CMake libtriton

add_custom_target(gen_doc_from_spec
    COMMAND ${PYTHON_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/extract_doc.py ${CMAKE_SOURCE_DIR}/src/libtriton/includes/triton/x86.spec "${CMAKE_CURRENT_BINARY_DIR}"
    DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/extract_doc.py
    DEPENDS ${CMAKE_SOURCE_DIR}/src/libtriton/includes/triton/x86.spec
)

add_custom_target(doc
  COMMAND doxygen ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile
  DEPENDS gen_doc_from_spec
)

configure_file(
    ${CMAKE_CURRENT_SOURCE_DIR}/Doxyfile.in
    ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile
    IMMEDIATE @ONLY
)
