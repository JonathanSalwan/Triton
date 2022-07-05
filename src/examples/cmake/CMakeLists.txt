# This is an example about how to compile Triton using its config file.
cmake_minimum_required(VERSION 3.20)
project(myproject)

find_package(triton REQUIRED CONFIG)
link_libraries(${TRITON_LIBRARIES})

add_executable(myproject
    myproject.cpp
)
