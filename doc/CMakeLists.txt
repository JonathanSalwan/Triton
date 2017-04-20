##
##  Copyright (C) - Triton
##
##  This program is under the terms of the BSD License.
##

##################################################################################### CMake libtriton

add_custom_target(doc
  COMMAND doxygen ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile
  )

configure_file(
    ${CMAKE_CURRENT_SOURCE_DIR}/Doxyfile.in
    ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile
    IMMEDIATE @ONLY
)
