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


class CMakeExtension(Extension):
    def __init__(self, name, sourcedir=''):
        Extension.__init__(self, name, sources=[])
        self.sourcedir = os.path.abspath(sourcedir)


class CMakeBuild(build_ext):
    def run(self):
        ext = self.extensions[0]
        self.build_extension(ext)
        self.copy_extension_to_source(ext)

    def build_extension(self, ext):
        ext_dir = os.path.abspath(os.path.dirname(self.get_ext_fullpath(ext.name)))

        # Set platform-agnostric arguments.
        cmake_args = [
            # General arguments.
            '-DCMAKE_LIBRARY_OUTPUT_DIRECTORY=' + ext_dir,
            '-DPYTHON_EXECUTABLE=' + sys.executable,
            '-DCMAKE_BUILD_TYPE=Release',
            # Common arguments.
            '-DZ3_INTERFACE=On',
            '-DBOOST_INTERFACE=Off',
            '-DLLVM_INTERFACE=Off',
        ]

        build_args = []

        env = os.environ.copy()
        env['CXXFLAGS'] = '{} -DVERSION_INFO=\\"{}\\"'.format(env.get('CXXFLAGS', ''), self.distribution.get_version())

        # Set platform-specific arguments.
        if platform.system() == "Linux":
            cmake_args += [
                '-DBITWUZLA_INTERFACE=Off',
            ]
            build_args += ['--', '-j4']
        elif platform.system() == "Windows":
            cmake_args += [
                '-DBITWUZLA_INTERFACE=Off',
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

        # Create temp and lib folders.
        if not os.path.exists(self.build_temp):
            os.makedirs(self.build_temp)

        if not os.path.exists(self.build_lib):
            os.makedirs(self.build_lib)

        subprocess.check_call(['cmake', ext.sourcedir] + cmake_args, cwd=self.build_temp, env=env)
        subprocess.check_call(['cmake', '--build', '.', '--config', 'Release', '--target', 'python-triton'] + build_args, cwd=self.build_temp)

    def copy_extension_to_source(self, ext):
        fullname = self.get_ext_fullname(ext.name)
        filename = self.get_ext_filename(fullname)

        if platform.system() == "Linux":
            src_filename = os.path.join(self.build_temp + '/src/libtriton', 'triton.so')
            dst_filename = os.path.join(self.build_lib, os.path.basename(filename))
        elif platform.system() == "Windows":
            src_filename = os.path.join(self.build_temp + '\\src\\libtriton\\Release', 'triton.pyd')
            dst_filename = os.path.join(self.build_lib, os.path.basename(filename))
        else:
            raise Exception(f'Platform not supported: {platform.system()}')

        copy_file(src_filename, dst_filename, verbose=self.verbose, dry_run=self.dry_run)


with open("README.md", "r") as f:
    long_description = f.read()


setup(
    name="triton-library",
    version="1.0.0",
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
