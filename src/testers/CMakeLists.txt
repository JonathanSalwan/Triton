# Pintool
# FIXME: python3
if(PINTOOL AND ${CMAKE_SYSTEM_NAME} MATCHES "Linux" AND NOT PYTHON36)
    enable_testing()

    set(TRITON_SCRIPT ${CMAKE_BINARY_DIR}/triton)

    add_test(PinToolCheckUnsupportedSemantic    sh -c "${TRITON_SCRIPT} ${CMAKE_CURRENT_LIST_DIR}/unsuported_semantics.py ${TRITON_ROOT}/src/samples/ir_test_suite/ir | tee /tmp/tester_triton_xxx && ! grep -nr KO /tmp/tester_triton_xxx")
    add_test(PinToolCheckSemantic               sh -c "${TRITON_SCRIPT} ${CMAKE_CURRENT_LIST_DIR}/check_semantics.py ${TRITON_ROOT}/src/samples/ir_test_suite/ir | tee /tmp/tester_triton_xxx && ! grep -nr KO /tmp/tester_triton_xxx")
    add_test(PinToolCheckSemanticQemu           sh -c "${TRITON_SCRIPT} ${CMAKE_CURRENT_LIST_DIR}/qemu-test-x86_64.py ${TRITON_ROOT}/src/samples/ir_test_suite/qemu-test-x86_64| tee /tmp/tester_triton_xxx && ! grep -nr KO /tmp/tester_triton_xxx")
    add_test(PinToolBlackList                   sh -c "${TRITON_SCRIPT} ${TRITON_ROOT}/src/examples/pin/blacklist.py ${TRITON_ROOT}/src/samples/crackmes/crackme_xor a | tee /tmp/tester_triton_xxx && grep -nr fail /tmp/tester_triton_xxx") # FAIL
    add_test(PinToolCallBackConcreteNeeds       sh -c "${TRITON_SCRIPT} ${TRITON_ROOT}/src/examples/pin/callback_concrete_needs.py ${TRITON_ROOT}/src/samples/ir_test_suite/ir | tee /tmp/tester_triton_xxx && grep -nr \"Need concrete register value\" /tmp/tester_triton_xxx") # WIN OR FAIL, DUNNO
    add_test(PinToolCallBackImage               sh -c "${TRITON_SCRIPT} ${TRITON_ROOT}/src/examples/pin/callback_image.py ${TRITON_ROOT}/src/samples/ir_test_suite/ir | tee /tmp/tester_triton_xxx && grep -nr \"Image size:\" /tmp/tester_triton_xxx") # WIN OR FAIL, DUNNO
    add_test(PinToolCallBackRoutine             sh -c "${TRITON_SCRIPT} ${TRITON_ROOT}/src/examples/pin/callback_routine.py ${TRITON_ROOT}/src/samples/vulns/testSuite | tee /tmp/tester_triton_xxx && grep -nr malloc /tmp/tester_triton_xxx") # WIN OR FAIL, DUNNO
    add_test(PinToolCallBackSyscall             sh -c "${TRITON_SCRIPT} ${TRITON_ROOT}/src/examples/pin/callback_syscall.py ${TRITON_ROOT}/src/samples/crackmes/crackme_xor a | tee /tmp/tester_triton_xxx && grep -nr fail /tmp/tester_triton_xxx") # FAIL
    add_test(PinToolCallBackSignals             sh -c "${TRITON_SCRIPT} ${TRITON_ROOT}/src/examples/pin/callback_signals.py ${TRITON_ROOT}/src/samples/others/signals | tee /tmp/tester_triton_xxx && grep -nr UNSET /tmp/tester_triton_xxx") # WIN
    add_test(PinToolCountInst                   sh -c "${TRITON_SCRIPT} ${TRITON_ROOT}/src/examples/pin/count_inst.py ${TRITON_ROOT}/src/samples/crackmes/crackme_hash aaaaa | tee /tmp/tester_triton_xxx && grep -nr \"Instruction count\" /tmp/tester_triton_xxx") # FAIL, nuber of line change...
    add_test(PinToolCrackMeHashCollision        sh -c "${TRITON_SCRIPT} ${TRITON_ROOT}/src/examples/pin/crackme_hash_collision.py ${TRITON_ROOT}/src/samples/crackmes/crackme_hash aaaaa | tee /tmp/tester_triton_xxx && grep -nr fail /tmp/tester_triton_xxx") # FAIL
    add_test(PinToolInjectModelWithSnapShot     sh -c "${TRITON_SCRIPT} ${TRITON_ROOT}/src/examples/pin/inject_model_with_snapshot.py ${TRITON_ROOT}/src/samples/crackmes/crackme_xor a | tee /tmp/tester_triton_xxx && grep -nr Win /tmp/tester_triton_xxx")
    add_test(PinToolIr                          sh -c "${TRITON_SCRIPT} ${TRITON_ROOT}/src/examples/pin/ir.py ${TRITON_ROOT}/src/samples/crackmes/crackme_xor a | tee /tmp/tester_triton_xxx && grep -nr \"syscall\" /tmp/tester_triton_xxx") # WiIN OR FAIL, DUNNO
    add_test(PinToolMainAndStack                sh -c "${TRITON_SCRIPT} ${TRITON_ROOT}/src/examples/pin/looking_for_stack_base_and_main_addr.py ${TRITON_ROOT}/src/samples/crackmes/crackme_xor a | tee /tmp/tester_triton_xxx && grep -nr 4005b3 /tmp/tester_triton_xxx") # WIN
    add_test(PinToolPathConstraints             sh -c "${TRITON_SCRIPT} ${TRITON_ROOT}/src/examples/pin/path_constraints.py ${TRITON_ROOT}/src/samples/crackmes/crackme_xor eli | tee /tmp/tester_triton_xxx && grep -nr \"SymVar_3:8 = 0x74 (t)\" /tmp/tester_triton_xxx") # WIN
    add_test(PinToolRuntimeMemoryTainting       sh -c "${TRITON_SCRIPT} ${TRITON_ROOT}/src/examples/pin/runtime_memory_tainting.py ${TRITON_ROOT}/src/samples/crackmes/crackme_xor a | tee /tmp/tester_triton_xxx && grep -nr fail /tmp/tester_triton_xxx") # FAIL
    add_test(PinToolRuntimeRegisterModification sh -c "${TRITON_SCRIPT} ${TRITON_ROOT}/src/examples/pin/runtime_register_modification.py ${TRITON_ROOT}/src/samples/crackmes/crackme_xor a | tee /tmp/tester_triton_xxx && grep -nr Win /tmp/tester_triton_xxx")
    add_test(PinToolStrLen                      sh -c "${TRITON_SCRIPT} ${TRITON_ROOT}/src/examples/pin/strlen.py ${TRITON_ROOT}/src/samples/others/strlen 1 | tee /tmp/tester_triton_xxx && grep -nr pointer /tmp/tester_triton_xxx") # FAIL
    add_test(PinToolSymOnlyOnTainted            sh -c "${TRITON_SCRIPT} ${TRITON_ROOT}/src/examples/pin/sym_only_on_tainted.py ${TRITON_ROOT}/src/samples/crackmes/crackme_xor a | tee /tmp/tester_triton_xxx && grep -nr fail /tmp/tester_triton_xxx") # FAIL
    add_test(PinToolReadFromFile                sh -c "${TRITON_SCRIPT} ${TRITON_ROOT}/src/examples/pin/symbolize_input_file.py ${TRITON_ROOT}/src/samples/others/read_from_file | tee /tmp/tester_triton_xxx && grep -nr Model /tmp/tester_triton_xxx") # WIN
    add_test(PinToolTraceInst                   sh -c "${TRITON_SCRIPT} ${TRITON_ROOT}/src/examples/pin/trace_inst.py ${TRITON_ROOT}/src/samples/crackmes/crackme_xor a | tee /tmp/tester_triton_xxx && grep -nr syscall /tmp/tester_triton_xxx") # WIN OR FAIL, DUNNO
endif()

# Misc
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux" AND PYTHON_BINDINGS)
    enable_testing()
    add_test(UnicornAArch64Semantics sh -c "${PYTHON_EXECUTABLE} ${CMAKE_CURRENT_LIST_DIR}/unicorn_test_aarch64.py")
endif()
