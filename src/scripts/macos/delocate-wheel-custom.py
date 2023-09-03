import sys

from delocate.cmd.delocate_wheel import main
import delocate.delocating


def filter_system_libs(libname):
    copy_lib = not (libname.startswith('/usr/lib') or
                libname.startswith('/System') or
                libname.find('libpython') >= 0)

    print(f'[filter_system_libs] libname: {libname}, copy_lib: {copy_lib}')

    return copy_lib


def delocate_wheel(in_wheel,
                   out_wheel=None,
                   lib_sdir='.dylibs',
                   lib_filt_func=None,
                   copy_filt_func=filter_system_libs,
                   require_archs=None,
                   check_verbose=None,
                   executable_path=None,
                   ignore_missing=False):
    return delocate.delocating.delocate_wheel(in_wheel,
                                              out_wheel,
                                              lib_sdir,
                                              lib_filt_func,
                                              copy_filt_func,
                                              require_archs,
                                              check_verbose,
                                              executable_path,
                                              ignore_missing)

delocate.cmd.delocate_wheel.delocate_wheel = delocate_wheel


if __name__ == '__main__':
    sys.exit(main())
