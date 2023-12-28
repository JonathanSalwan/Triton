##
##  Copyright (C) - Triton
##
##  This program is under the terms of the Apache License 2.0.
##

import os
import platform
import re
import subprocess
import sys

from distutils.file_util import copy_file
from distutils.version import LooseVersion
from setuptools import Extension
from setuptools import setup
from setuptools.command.build_ext import build_ext


VERSION_MAJOR = 1
VERSION_MINOR = 0
VERSION_PATCH = 0

RELEASE_CANDIDATE = 3

VERSION = f'{VERSION_MAJOR}.{VERSION_MINOR}.{VERSION_PATCH}' + \
            f'rc{RELEASE_CANDIDATE}' if RELEASE_CANDIDATE else ''

def is_cmake_true(value):
    """Check if CMake would parse the value as True or False. Might not be completely accurate.
    Based on https://cmake.org/cmake/help/latest/command/if.html#basic-expressions"""
    if(value in ['ON', 'YES', 'TRUE', 'Y']):
        return True
    try:
        float(value)
        if(int(value) == 0):
            return False
        return True
    except:
        return False

class CMakeExtension(Extension):
    def __init__(self, name, sourcedir=''):
        Extension.__init__(self, name, sources=[])
        self.sourcedir = os.path.abspath(sourcedir)


class CMakeBuild(build_ext):

    def run(self):
        ext = self.extensions[0]
        self.build_extension(ext)
        self.copy_extension_to_source(ext)
        self.copy_autocomplete()


    def build_extension(self, ext):
        # Set platform-agnostric arguments.
        cmake_args = [
            # General arguments.
            '-DPYTHON_EXECUTABLE=' + sys.executable,
            '-DCMAKE_BUILD_TYPE=Release',
        ]

        # Interfaces can be defined using environment variables.
        # Interfaces by default:
        #
        #   Z3_INTERFACE=On
        #   LLVM_INTERFACE=Off
        #   BITWUZLA_INTERFACE=Off
        #   BOOST_INTERFACE=Off
        #
        for arg, value in [('Z3_INTERFACE', 'On'), ('LLVM_INTERFACE', 'Off'), ('BITWUZLA_INTERFACE', 'Off'), ('BOOST_INTERFACE', 'Off')]:
            if os.getenv(arg):
                cmake_args += [f'-D{arg}=' + os.getenv(arg)]
            else:
                cmake_args += [f'-D{arg}={value}']

        build_args = []

        env = os.environ.copy()
        env['CXXFLAGS'] = '{} -DVERSION_INFO=\\"{}\\"'.format(env.get('CXXFLAGS', ''), self.distribution.get_version())

        # Set platform-specific arguments.
        if platform.system() == "Linux":
            build_args += ['--', '-j4']

        elif platform.system() == "Darwin":
            build_args += ['--', '-j4']

        elif platform.system() == "Windows":
            cmake_args += [
                '-G Visual Studio 17 2022',
            ]
            build_args += ['--', '/m:4']

        else:
            raise Exception(f'Platform not supported: {platform.system()}')

        # Custom Python paths.
        if os.getenv('PYTHON_LIBRARIES'):
            cmake_args += ['-DPYTHON_LIBRARIES=' + os.getenv('PYTHON_LIBRARIES')]

        if os.getenv('PYTHON_INCLUDE_DIRS'):
            cmake_args += ['-DPYTHON_INCLUDE_DIRS=' + os.getenv('PYTHON_INCLUDE_DIRS')]

        if os.getenv('PYTHON_LIBRARY'):
            cmake_args += ['-DPYTHON_LIBRARY=' + os.getenv('PYTHON_LIBRARY')]

        if os.getenv('PYTHON_VERSION'):
            cmake_args += ['-DPYTHON_VERSION=' + os.getenv('PYTHON_VERSION')]

        # Custom Z3 paths.
        if os.getenv('Z3_LIBRARIES'):
            cmake_args += ['-DZ3_LIBRARIES=' + os.getenv('Z3_LIBRARIES')]

        if os.getenv('Z3_INCLUDE_DIRS'):
            cmake_args += ['-DZ3_INCLUDE_DIRS=' + os.getenv('Z3_INCLUDE_DIRS')]

        # Custom Bitwuzla paths.
        if os.getenv('BITWUZLA_LIBRARIES'):
            cmake_args += ['-DBITWUZLA_LIBRARIES=' + os.getenv('BITWUZLA_LIBRARIES')]

        if os.getenv('BITWUZLA_INCLUDE_DIRS'):
            cmake_args += ['-DBITWUZLA_INCLUDE_DIRS=' + os.getenv('BITWUZLA_INCLUDE_DIRS')]

        # Custom Capstone paths.
        if os.getenv('CAPSTONE_LIBRARIES'):
            cmake_args += ['-DCAPSTONE_LIBRARIES=' + os.getenv('CAPSTONE_LIBRARIES')]

        if os.getenv('CAPSTONE_INCLUDE_DIRS'):
            cmake_args += ['-DCAPSTONE_INCLUDE_DIRS=' + os.getenv('CAPSTONE_INCLUDE_DIRS')]

        # Custom LLVM paths.
        if os.getenv('LLVM_LIBRARIES'):
            cmake_args += ['-DLLVM_LIBRARIES=' + os.getenv('LLVM_LIBRARIES')]

        if os.getenv('LLVM_INCLUDE_DIRS'):
            cmake_args += ['-DLLVM_INCLUDE_DIRS=' + os.getenv('LLVM_INCLUDE_DIRS')]

        # Custom CMake prefix path.
        if os.getenv('CMAKE_PREFIX_PATH'):
            cmake_args += ['-DCMAKE_PREFIX_PATH=' + os.getenv('CMAKE_PREFIX_PATH')]

        # Autocomplete stub generation. Enabled by default.
        python_autocomplete_value = os.getenv('PYTHON_BINDINGS_AUTOCOMPLETE', default='ON').upper()
        if python_autocomplete_value:
            cmake_args += ['-DPYTHON_BINDINGS_AUTOCOMPLETE=' + python_autocomplete_value]

        # Create temp and lib folders.
        if not os.path.exists(self.build_temp):
            os.makedirs(self.build_temp)

        if not os.path.exists(self.build_lib):
            os.makedirs(self.build_lib)

        subprocess.check_call(['cmake', ext.sourcedir] + cmake_args, cwd=self.build_temp, env=env)
        subprocess.check_call(['cmake', '--build', '.', '--config', 'Release', '--target', 'python-triton'] + build_args, cwd=self.build_temp)

        # The autocomplete file has to be built separately.
        if (is_cmake_true(python_autocomplete_value)):
            subprocess.check_call(['cmake', '--build', '.', '--config', 'Release', '--target', 'python_autocomplete'], cwd=self.build_temp)

    def copy_extension_to_source(self, ext):
        fullname = self.get_ext_fullname(ext.name)
        filename = self.get_ext_filename(fullname)

        if platform.system() == "Linux":
            src_filename = os.path.join(self.build_temp + '/src/libtriton', 'triton.so')
            dst_filename = os.path.join(self.build_lib, os.path.basename(filename))
        elif platform.system() == "Darwin":
            src_filename = os.path.join(self.build_temp + '/src/libtriton', 'libtriton.dylib')
            dst_filename = os.path.join(self.build_lib, os.path.basename(filename))
        elif platform.system() == "Windows":
            src_filename = os.path.join(self.build_temp + '\\src\\libtriton\\Release', 'triton.pyd')
            dst_filename = os.path.join(self.build_lib, os.path.basename(filename))
        else:
            raise Exception(f'Platform not supported: {platform.system()}')

        copy_file(src_filename, dst_filename, verbose=self.verbose, dry_run=self.dry_run)

    def copy_autocomplete(self):
        src_filename = os.path.join(self.build_temp + '/doc/triton_autocomplete', 'triton.pyi')
        if(os.path.exists(src_filename)):
            copy_file(src_filename, self.build_lib, verbose=self.verbose, dry_run=self.dry_run)

with open("README.md", "r") as f:
    long_description = f.read()


setup(
    name="triton-library",
    version=VERSION,
    author="The Triton's community",
    author_email="tritonlibrary@gmail.com",
    description="Triton is a dynamic binary analysis library",
    long_description=long_description,
    long_description_content_type="text/markdown",
    license = "Apache License Version 2.0",
    license_files = ('LICENSE.txt',),
    classifiers=[
        "Programming Language :: C++",
        "Programming Language :: Python :: 3",
        "Topic :: Security",
        "Topic :: Software Development :: Libraries",
    ],
    python_requires='>=3.6',
    project_urls={
        'Homepage': 'https://triton-library.github.io/',
        'Source': 'https://github.com/jonathansalwan/Triton',
    },
    ext_modules=[
        CMakeExtension('triton', sourcedir='.')
    ],
    cmdclass=dict(build_ext=CMakeBuild),
    zip_safe=False,
    install_requires=[]
)
