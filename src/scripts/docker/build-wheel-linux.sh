#! /usr/bin/env bash

# This file is meant to be used inside the docker image build by the
# `build-docker-image.sh` script. This file build triton-library for Python
# 3.8, 3.9, 3.10, 3.11, 3.12, and 3.13. It is used by the Build Python
# Package Github workflow but can also be used locally by running:
#
# $ docker pull quay.io/pypa/manylinux_2_34_x86_64
# $ ./src/scripts/docker/build-docker-image.sh
# $ cd /tmp
# $ wget -q https://github.com/llvm/llvm-project/releases/download/llvmorg-14.0.0/clang+llvm-14.0.0-x86_64-linux-gnu-ubuntu-18.04.tar.xz
# $ tar xf clang+llvm-14.0.0-x86_64-linux-gnu-ubuntu-18.04.tar.xz
# $ cd -
# $ docker run \
#       --rm \
#       -v $(pwd):/src \
#       -v /tmp/clang+llvm-14.0.0-x86_64-linux-gnu-ubuntu-18.04:/llvm \
#       build-triton-linux-x86_64 bash /src/src/scripts/docker/build-wheel-linux.sh
#
# You'll find the .whl packages in the wheelhouse folder.

set -e
# set -x  # Debugging

DEPENDENCIES_DIR=/tmp/triton-dependencies
LLVM_DIR=/llvm
SOURCE_DIR=/src
WHEEL_DIR=$SOURCE_DIR/wheelhouse

# Show Python versions.
ls -al /opt/_internal/

# Set environment variables for building Triton.
echo "[+] Setup environment variables"
export Z3_INCLUDE_DIRS=$DEPENDENCIES_DIR/z3-4.12.2-x64-glibc-2.31/include
export Z3_LIBRARIES=$DEPENDENCIES_DIR/z3-4.12.2-x64-glibc-2.31/bin/libz3.so
export CAPSTONE_INCLUDE_DIRS=/usr/include
export CAPSTONE_LIBRARIES=/usr/lib/libcapstone.so
export BITWUZLA_INTERFACE=On
export BITWUZLA_INCLUDE_DIRS=$DEPENDENCIES_DIR/bitwuzla/install/include
export BITWUZLA_LIBRARIES=$DEPENDENCIES_DIR/bitwuzla/install/lib64/libbitwuzla.so
export LLVM_INTERFACE=ON
export CMAKE_PREFIX_PATH=$LLVM_DIR

# Build Triton Python wheel package for Python 3.9.
echo "[+] Build Triton wheel package for Python 3.9"
cd $SOURCE_DIR
rm -rf $SOURCE_DIR/build
rm -rf $SOURCE_DIR/triton_library.egg-info
export PYTHON_BINARY=/opt/_internal/cpython-3.9.*/bin/python
export PYTHON_INCLUDE_DIRS=$($PYTHON_BINARY -c "from sysconfig import get_paths; print(get_paths()['include'])")
export PYTHON_LIBRARY=$($PYTHON_BINARY -c "from sysconfig import get_paths; print(get_paths()['include'])")

$PYTHON_BINARY -m build --wheel --outdir $WHEEL_DIR/linux_x86_64

# Build Triton Python wheel package for Python 3.10.
echo "[+] Build Triton wheel package for Python 3.10"
cd $SOURCE_DIR
rm -rf $SOURCE_DIR/build
rm -rf $SOURCE_DIR/triton_library.egg-info
export PYTHON_BINARY=/opt/_internal/cpython-3.10.*/bin/python
export PYTHON_INCLUDE_DIRS=$($PYTHON_BINARY -c "from sysconfig import get_paths; print(get_paths()['include'])")
export PYTHON_LIBRARY=$($PYTHON_BINARY -c "from sysconfig import get_paths; print(get_paths()['include'])")

$PYTHON_BINARY -m build --wheel --outdir $WHEEL_DIR/linux_x86_64

# Build Triton Python wheel package for Python 3.11.
echo "[+] Build Triton wheel package for Python 3.11"
cd $SOURCE_DIR
rm -rf $SOURCE_DIR/build
rm -rf $SOURCE_DIR/triton_library.egg-info
export PYTHON_BINARY=/opt/_internal/cpython-3.11.*/bin/python
export PYTHON_INCLUDE_DIRS=$($PYTHON_BINARY -c "from sysconfig import get_paths; print(get_paths()['include'])")
export PYTHON_LIBRARY=$($PYTHON_BINARY -c "from sysconfig import get_paths; print(get_paths()['include'])")

$PYTHON_BINARY -m build --wheel --outdir $WHEEL_DIR/linux_x86_64

# Build Triton Python wheel package for Python 3.12.
echo "[+] Build Triton wheel package for Python 3.12"
cd $SOURCE_DIR
rm -rf $SOURCE_DIR/build
rm -rf $SOURCE_DIR/triton_library.egg-info
export PYTHON_BINARY=/opt/_internal/cpython-3.12.*/bin/python
export PYTHON_INCLUDE_DIRS=$($PYTHON_BINARY -c "from sysconfig import get_paths; print(get_paths()['include'])")
export PYTHON_LIBRARY=$($PYTHON_BINARY -c "from sysconfig import get_paths; print(get_paths()['include'])")

$PYTHON_BINARY -m build --wheel --outdir $WHEEL_DIR/linux_x86_64

# Build Triton Python wheel package for Python 3.13.
echo "[+] Build Triton wheel package for Python 3.13"
cd $SOURCE_DIR
rm -rf $SOURCE_DIR/build
rm -rf $SOURCE_DIR/triton_library.egg-info
export PYTHON_BINARY=/opt/_internal/cpython-3.13.*/bin/python
export PYTHON_INCLUDE_DIRS=$($PYTHON_BINARY -c "from sysconfig import get_paths; print(get_paths()['include'])")
export PYTHON_LIBRARY=$($PYTHON_BINARY -c "from sysconfig import get_paths; print(get_paths()['include'])")

$PYTHON_BINARY -m build --wheel --outdir $WHEEL_DIR/linux_x86_64

# Repair wheels.
echo "[+] Repair wheel packages"
cd $SOURCE_DIR
for whl in $WHEEL_DIR/linux_x86_64/*.whl; do
    auditwheel repair --plat manylinux_2_34_x86_64 "$whl" --wheel-dir $WHEEL_DIR/manylinux_2_34_x86_64
done

echo "[+] Remove build directory"
rm -rf $SOURCE_DIR/build
rm -rf $SOURCE_DIR/triton_library.egg-info

echo "[+] Change permissions for directories"
chown -R 1000:1000 $WHEEL_DIR
