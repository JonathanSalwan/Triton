##
##  Copyright (C) - Triton
##
##  This program is under the terms of the BSD License.
##

##################################################################################### CMake libtriton

add_custom_target(gen_x86_doc_from_spec
    COMMAND ${PYTHON_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/extract_doc.py ${TRITON_ROOT}/src/libtriton/includes/triton/x86.spec "${CMAKE_CURRENT_BINARY_DIR}"
    DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/extract_doc.py
    DEPENDS ${TRITON_ROOT}/src/libtriton/includes/triton/x86.spec
)

add_custom_target(gen_aarch64_doc_from_spec
    COMMAND ${PYTHON_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/extract_doc.py ${TRITON_ROOT}/src/libtriton/includes/triton/aarch64.spec "${CMAKE_CURRENT_BINARY_DIR}"
    DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/extract_doc.py
    DEPENDS ${TRITON_ROOT}/src/libtriton/includes/triton/aarch64.spec
)

add_custom_target(gen_arm32_doc_from_spec
    COMMAND ${PYTHON_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/extract_doc.py ${TRITON_ROOT}/src/libtriton/includes/triton/arm32.spec "${CMAKE_CURRENT_BINARY_DIR}"
    DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/extract_doc.py
    DEPENDS ${TRITON_ROOT}/src/libtriton/includes/triton/arm32.spec
)

add_custom_target(doc
    COMMAND doxygen ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile
    DEPENDS gen_x86_doc_from_spec
    DEPENDS gen_aarch64_doc_from_spec
    DEPENDS gen_arm32_doc_from_spec
)

if(PYTHON_BINDINGS_AUTOCOMPLETE)
    add_custom_target(python_autocomplete
        COMMAND ${PYTHON_EXECUTABLE} ${CMAKE_CURRENT_LIST_DIR}/autocomplete/generate_autocomplete.py "--basedir" "${CMAKE_CURRENT_BINARY_DIR}" "$<$<BOOL:${BITWUZLA_INTERFACE}>:--bitwuzla>" "$<$<BOOL:${Z3_INTERFACE}>:--z3>"
        DEPENDS gen_x86_doc_from_spec
        DEPENDS gen_aarch64_doc_from_spec
        DEPENDS gen_arm32_doc_from_spec
    )
    if (NOT DEFINED PYTHON_SITE_PACKAGES)
        execute_process(COMMAND ${PYTHON_EXECUTABLE} -c "from sysconfig import get_path; print(get_path('platlib'))" OUTPUT_VARIABLE PYTHON_SITE_PACKAGES OUTPUT_STRIP_TRAILING_WHITESPACE)
    endif()
    install(
        FILES ${CMAKE_CURRENT_BINARY_DIR}/triton_autocomplete/triton.pyi
        DESTINATION ${PYTHON_SITE_PACKAGES}
    )
endif()

configure_file(
    ${CMAKE_CURRENT_SOURCE_DIR}/Doxyfile.in
    ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile
    IMMEDIATE @ONLY
)
