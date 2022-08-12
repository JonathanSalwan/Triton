#! /usr/bin/env bash

# This file is meant to be used inside the docker image build by the
# `build-docker-image.sh` script. This file build triton-library for Python 3.8,
# 3.9 and 3.10. It is used by the Build Python Package Github workflow but can
# also be used locally by running:
#
# $ docker pull quay.io/pypa/manylinux_2_24_x86_64
# $ ./build-docker-image.sh
# $ docker run --rm -v $(pwd):/src build-triton-linux-x86_64 bash /src/src/scripts/docker/build-wheel-linux.sh
#
# You'll find the .whl packages in the wheel-final folder.

set -ex

# Create deps folder.
cd /src
mkdir -p deps
cd deps

# Download and build GMP.
wget https://gmplib.org/download/gmp/gmp-6.2.1.tar.xz
tar xvf gmp-6.2.1.tar.xz
cd gmp-6.2.1/
./configure --enable-cxx
make
make check
make install
cd ..

# Download and build Bitwuzla.
git clone https://github.com/bitwuzla/bitwuzla.git
cd bitwuzla
./contrib/setup-cadical.sh
./contrib/setup-btor2tools.sh
./contrib/setup-symfpu.sh
./configure.sh --shared --prefix $(pwd)/install
cd build
make
make install
cd ../..

# Download Z3.
wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.17/z3-4.8.17-x64-glibc-2.31.zip
unzip z3-4.8.17-x64-glibc-2.31.zip

# Install Capstone.
wget https://github.com/aquynh/capstone/archive/4.0.2.tar.gz
tar -xf ./4.0.2.tar.gz
cd ./capstone-4.0.2
bash ./make.sh
sudo make install
cd ..

# Download LLVM.
wget https://github.com/llvm/llvm-project/releases/download/llvmorg-12.0.1/clang+llvm-12.0.1-x86_64-linux-gnu-ubuntu-16.04.tar.xz
tar -xf clang+llvm-12.0.1-x86_64-linux-gnu-ubuntu-16.04.tar.xz

# Set environment variables for building Triton.
export Z3_INCLUDE_DIRS=$(pwd)/z3-4.8.17-x64-glibc-2.31/include
export Z3_LIBRARIES=$(pwd)/z3-4.8.17-x64-glibc-2.31/bin/libz3.a
export CAPSTONE_INCLUDE_DIRS=/usr/include
export CAPSTONE_LIBRARIES=/usr/lib/libcapstone.a
export BITWUZLA_INTERFACE=On
export BITWUZLA_INCLUDE_DIRS=$(pwd)/bitwuzla/install/include
export BITWUZLA_LIBRARIES=$(pwd)/bitwuzla/install/lib/libbitwuzla.so
export LLVM_INTERFACE=ON
export CMAKE_PREFIX_PATH=$($(pwd)/clang+llvm-12.0.1-x86_64-linux-gnu-ubuntu-/bin/llvm-config --prefix)

cd ..

# Build Triton Python wheel package for Python 3.8.
export PYTHON_BINARY=/opt/python/cp38-cp38/bin/python
export PYTHON_INCLUDE_DIRS=$($PYTHON_BINARY -c "from sysconfig import get_paths; print(get_paths()['include'])")
export PYTHON_LIBRARY=$($PYTHON_BINARY -c "from sysconfig import get_paths; print(get_paths()['include'])")

$PYTHON_BINARY setup.py bdist_wheel --dist-dir wheel-temp

# Build Triton Python wheel package for Python 3.9.
export PYTHON_BINARY=/opt/python/cp39-cp39/bin/python
export PYTHON_INCLUDE_DIRS=$($PYTHON_BINARY -c "from sysconfig import get_paths; print(get_paths()['include'])")
export PYTHON_LIBRARY=$($PYTHON_BINARY -c "from sysconfig import get_paths; print(get_paths()['include'])")

$PYTHON_BINARY setup.py bdist_wheel --dist-dir wheel-temp

# Build Triton Python wheel package for Python 3.10.
export PYTHON_BINARY=/opt/python/cp310-cp310/bin/python
export PYTHON_INCLUDE_DIRS=$($PYTHON_BINARY -c "from sysconfig import get_paths; print(get_paths()['include'])")
export PYTHON_LIBRARY=$($PYTHON_BINARY -c "from sysconfig import get_paths; print(get_paths()['include'])")

$PYTHON_BINARY setup.py bdist_wheel --dist-dir wheel-temp

# Repair wheels.
for whl in wheel-temp/*.whl; do
    auditwheel repair "$whl" -w wheel-final
done

chown -R 1000:1000 build
chown -R 1000:1000 deps
chown -R 1000:1000 triton_library.egg-info
chown -R 1000:1000 wheel-final
chown -R 1000:1000 wheel-temp
