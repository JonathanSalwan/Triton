#!/usr/bin/env sh
val=$(cat /proc/sys/kernel/yama/ptrace_scope)
if test "$val" = "0" 
then
    ctest
else
    ctest -E "^PinTool"
    echo ""
    echo "/!\\ PinTool tests were not run as ptrace scope is not set to 0"
    echo ""
fi
