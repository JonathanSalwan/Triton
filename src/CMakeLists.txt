add_subdirectory(libtriton)

if(BUILD_EXAMPLES)
    if(NOT ${CMAKE_SYSTEM_NAME} MATCHES "Windows")
        # Disable examples for windows as linkage doesn't work. Exported function should
        # be marked as exported on windows.
        add_subdirectory(examples)
    else()
        enable_testing()
        add_test(DummyTest echo "Windows is awesome")
    endif()
endif()

if(ENABLE_TEST)
    add_subdirectory(testers)
endif()
