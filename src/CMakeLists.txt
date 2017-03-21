add_subdirectory(libtriton)

if(PINTOOL)
  add_subdirectory(tracer)
endif()

if(NOT ${CMAKE_SYSTEM_NAME} MATCHES "Windows")
  # Disable exemples for windows as linkage doesn't work. Exported function should
  # be marked as exported on windows.
  add_subdirectory(examples)
else()
  enable_testing()
  add_test(DummyTest echo "Windows is awesome")
endif()
add_subdirectory(testers)
