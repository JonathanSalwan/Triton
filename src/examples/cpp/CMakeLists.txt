enable_testing()

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11 -fPIC")

add_executable(taint_reg taint_reg.cpp)
target_link_libraries(taint_reg triton)
add_test(TaintRegister taint_reg)
add_dependencies(check taint_reg)

add_executable(info_reg info_reg.cpp)
target_link_libraries(info_reg triton)
add_test(InfoRegister info_reg)
add_dependencies(check info_reg)

add_executable(ir ir.cpp)
target_link_libraries(ir triton)
add_test(IR ir)
add_dependencies(check ir)

add_executable(simplification simplification.cpp)
target_link_libraries(simplification triton)
add_test(Simplification simplification)
add_dependencies(check simplification)

add_executable(constraint constraint.cpp)
target_link_libraries(constraint triton)
add_test(Constraint constraint)
add_dependencies(check constraint)

add_executable(parsing_elf parsing_elf.cpp)
target_link_libraries(parsing_elf triton)
add_test(ParsingElf parsing_elf ${CMAKE_SOURCE_DIR}/src/samples/crackmes/crackme_xor)
add_dependencies(check parsing_elf)
