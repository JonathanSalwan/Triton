#!/usr/bin/env sh
val=$(cat /proc/sys/kernel/yama/ptrace_scope)
if test "$val" = "0"
then
    ctest --output-on-failure
else
    ctest -E "^PinTool" --output-on-failure
    echo ""
    echo "/!\\ PinTool tests were not run as ptrace scope is not set to 0"
    echo ""
fi
