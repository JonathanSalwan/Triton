# Global UNIX CXX Flags
if(CMAKE_COMPILER_IS_GNUCXX OR ${CMAKE_CXX_COMPILER_ID} MATCHES "Clang")
    # Flags
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra -Werror")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fPIC -std=c++11")
    if(NOT GCOV)
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O3")
    endif()
endif()

# 32-bits
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux" OR ${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    if(${ARCHITECTURE} STREQUAL "i386")
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -m32")
    endif()
endif()

SET(LIBTRITONAST_SOURCE_FILES 
    context.cpp
    nodes.cpp
    representations/python.cpp
    representations/representation.cpp
    representations/smt.cpp
    solvers/model.cpp
    solvers/z3/solver.cpp
    solvers/z3/tritonToZ3Ast.cpp
    solvers/z3/z3Interface.cpp
    solvers/z3/z3ToTritonAst.cpp
    )

add_library(tritonast ${LIBTRITONAST_SOURCE_FILES})
target_link_libraries(
    tritonast
    ${Boost_LIBRARIES}
    ${Z3_LIBRARIES}
)

install (TARGETS tritonast DESTINATION lib)
install (DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/include/tritonast DESTINATION include)
