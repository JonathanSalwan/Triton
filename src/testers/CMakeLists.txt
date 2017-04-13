if(PINTOOL AND ${CMAKE_SYSTEM_NAME} MATCHES "Linux")
    enable_testing()

    set(TRITON_SCRIPT ${CMAKE_BINARY_DIR}/triton)

    #add_test(PinToolCheckSemantic ${TRITON_SCRIPT} ${CMAKE_CURRENT_SOURCE_DIR}/check_semantics.py ${CMAKE_SOURCE_DIR}/src/samples/ir_test_suite/ir)
    #add_test(PinToolCheckSemanticQemu ${TRITON_SCRIPT} ${CMAKE_CURRENT_SOURCE_DIR}/qemu-test-x86_64.py ${CMAKE_SOURCE_DIR}/src/samples/ir_test_suite/qemu-test-x86_64)
    add_test(PinToolAstDict                     sh -c "${TRITON_SCRIPT} ${CMAKE_SOURCE_DIR}/src/examples/pin/ast_dictionaries.py ${CMAKE_SOURCE_DIR}/src/samples/crackmes/crackme_xor elite | grep Win")
    add_test(PinToolBlackList                   sh -c "${TRITON_SCRIPT} ${CMAKE_SOURCE_DIR}/src/examples/pin/blacklist.py ${CMAKE_SOURCE_DIR}/src/samples/crackmes/crackme_xor a | grep fail") # FAIL
    add_test(PinToolCallBackImage               sh -c "${TRITON_SCRIPT} ${CMAKE_SOURCE_DIR}/src/examples/pin/callback_image.py ${CMAKE_SOURCE_DIR}/src/samples/ir_test_suite/ir | grep \"Image size:  3791264\"") # WIN OR FAIL, DUNNO
    add_test(PinToolCallBackRoutine             sh -c "${TRITON_SCRIPT} ${CMAKE_SOURCE_DIR}/src/examples/pin/callback_routine.py ${CMAKE_SOURCE_DIR}/src/samples/vulns/testSuite | grep malloc") # WIN OR FAIL, DUNNO
    add_test(PinToolCallBackSyscall             sh -c "${TRITON_SCRIPT} ${CMAKE_SOURCE_DIR}/src/examples/pin/callback_syscall.py ${CMAKE_SOURCE_DIR}/src/samples/crackmes/crackme_xor a | grep fail") # FAIL
    add_test(PinToolCrackMeHashCollision        sh -c "${TRITON_SCRIPT} ${CMAKE_SOURCE_DIR}/src/examples/pin/crackme_hash_collision.py ${CMAKE_SOURCE_DIR}/src/samples/crackmes/crackme_hash aaaaa | grep fail") # FAIL
    #    add_test(PinToolInjectModelWithSnapShot sh -c "${TRITON_SCRIPT} ${CMAKE_SOURCE_DIR}/src/examples/pin/inject_model_with_snapshot.py ${CMAKE_SOURCE_DIR}/src/samples/crackmes/crackme_xor a | grep Win")
    add_test(PinToolIr                          sh -c "${TRITON_SCRIPT} ${CMAKE_SOURCE_DIR}/src/examples/pin/ir.py ${CMAKE_SOURCE_DIR}/src/samples/crackmes/crackme_xor a | grep \"syscall\"") # WiIN OR FAIL, DUNNO
    add_test(PinToolRuntimeMemoryTainting       sh -c "${TRITON_SCRIPT} ${CMAKE_SOURCE_DIR}/src/examples/pin/runtime_memory_tainting.py ${CMAKE_SOURCE_DIR}/src/samples/crackmes/crackme_xor a | grep fail") # FAIL
    add_test(PinToolRuntimeRegisterModification sh -c "${TRITON_SCRIPT} ${CMAKE_SOURCE_DIR}/src/examples/pin/runtime_register_modification.py ${CMAKE_SOURCE_DIR}/src/samples/crackmes/crackme_xor a | grep Win")
    add_test(PinToolStrLen                      sh -c "${TRITON_SCRIPT} ${CMAKE_SOURCE_DIR}/src/examples/pin/strlen.py ${CMAKE_SOURCE_DIR}/src/samples/others/strlen 1 | grep pointer") # FAIL
    add_test(PinToolSymOnlyOnTainted            sh -c "${TRITON_SCRIPT} ${CMAKE_SOURCE_DIR}/src/examples/pin/sym_only_on_tainted.py ${CMAKE_SOURCE_DIR}/src/samples/crackmes/crackme_xor a | grep fail") # FAIL
endif()
