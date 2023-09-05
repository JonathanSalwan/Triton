#! /usr/bin/env bash

# This file is meant to be used inside the docker image build by the
# `build-docker-image.sh` script. This file build triton-library for Python 3.8,
# 3.9, 3.10 and 3.11. It is used by the Build Python Package Github workflow but can
# also be used locally by running:
#
# $ docker pull quay.io/pypa/manylinux_2_24_x86_64
# $ ./src/scripts/docker/build-docker-image.sh
# $ docker run --rm -v $(pwd):/src build-triton-linux-x86_64 bash /src/src/scripts/docker/build-wheel-linux.sh
#
# You'll find the .whl packages in the wheel-final folder.

set -e
# set -x  # Debugging

DEPENDENCIES_DIR=/tmp/triton-dependencies
SOURCE_DIR=/src
WHEEL_DIR=$SOURCE_DIR/wheelhouse

# Set environment variables for building Triton.
echo "[+] Setup environment variables"
export Z3_INCLUDE_DIRS=$DEPENDENCIES_DIR/z3-4.8.17-x64-glibc-2.31/include
export Z3_LIBRARIES=$DEPENDENCIES_DIR/z3-4.8.17-x64-glibc-2.31/bin/libz3.a
export CAPSTONE_INCLUDE_DIRS=/usr/include
export CAPSTONE_LIBRARIES=/usr/lib/libcapstone.a
export BITWUZLA_INTERFACE=On
export BITWUZLA_INCLUDE_DIRS=$DEPENDENCIES_DIR/bitwuzla/install/include
export BITWUZLA_LIBRARIES=$DEPENDENCIES_DIR/bitwuzla/install/lib64/libbitwuzla.so
export LLVM_INTERFACE=ON
export CMAKE_PREFIX_PATH=$($DEPENDENCIES_DIR/clang+llvm-12.0.1-x86_64-linux-gnu-ubuntu-/bin/llvm-config --prefix)



#miniconda
wget --quiet https://repo.anaconda.com/miniconda/Miniconda3-latest-Linux-x86_64.sh -O ~/miniconda.sh && \
bash ~/miniconda.sh -b -p /opt/conda && \
bash rm ~/miniconda.sh


export PATH="/opt/conda/bin:$PATH"
/opt/conda/bin/conda init bash
source activate
conda deactivate
conda create -n py38 python=3.8
conda create -n py39 python=3.9
conda create -n py310 python=3.10
conda create -n py311 python=3.11


# Build Triton Python wheel package for Python 3.8.
echo "[+] Build Triton wheel package for Python 3.8"
cd $SOURCE_DIR
#export PYTHON_BINARY=/opt/_internal/cpython-3.8.17/bin/python
#export PYTHON_INCLUDE_DIRS=$($PYTHON_BINARY -c "from sysconfig import get_paths; print(get_paths()['include'])")
#export PYTHON_LIBRARY=$($PYTHON_BINARY -c "from sysconfig import get_paths; print(get_paths()['include'])")
conda activate py38
python -m pip install build
python --version
python -m build --wheel --outdir $WHEEL_DIR/linux_x86_64

# Build Triton Python wheel package for Python 3.9.
echo "[+] Build Triton wheel package for Python 3.9"
cd $SOURCE_DIR
#export PYTHON_BINARY=/opt/_internal/cpython-3.9.17/bin/python
#export PYTHON_INCLUDE_DIRS=$($PYTHON_BINARY -c "from sysconfig import get_paths; print(get_paths()['include'])")
#export PYTHON_LIBRARY=$($PYTHON_BINARY -c "from sysconfig import get_paths; print(get_paths()['include'])")
conda activate py39
python -m pip install build
python --version
python -m build --wheel --outdir $WHEEL_DIR/linux_x86_64

# Build Triton Python wheel package for Python 3.10.
echo "[+] Build Triton wheel package for Python 3.10"
cd $SOURCE_DIR
#export PYTHON_BINARY=/opt/_internal/cpython-3.10.12/bin/python
#export PYTHON_INCLUDE_DIRS=$($PYTHON_BINARY -c "from sysconfig import get_paths; print(get_paths()['include'])")
#export PYTHON_LIBRARY=$($PYTHON_BINARY -c "from sysconfig import get_paths; print(get_paths()['include'])")
conda activate py310
python -m pip install build
python --version
python -m build --wheel --outdir $WHEEL_DIR/linux_x86_64

# Build Triton Python wheel package for Python 3.11.
echo "[+] Build Triton wheel package for Python 3.11"
cd $SOURCE_DIR
#export PYTHON_BINARY=/opt/_internal/cpython-3.11.4/bin/python
#export PYTHON_INCLUDE_DIRS=$($PYTHON_BINARY -c "from sysconfig import get_paths; print(get_paths()['include'])")
#export PYTHON_LIBRARY=$($PYTHON_BINARY -c "from sysconfig import get_paths; print(get_paths()['include'])")
conda activate py311
python -m pip install build
python --version
python -m build --wheel --outdir $WHEEL_DIR/linux_x86_64

python -m pip install auditwheel
# Repair wheels.
echo "[+] Repair wheel packages"
cd $SOURCE_DIR
for whl in $WHEEL_DIR/linux_x86_64/*.whl; do
    auditwheel repair "$whl" --wheel-dir $WHEEL_DIR/manylinux_2_28_x86_64
done

echo "[+] Remove build directory"
rm -rf $SOURCE_DIR/build
rm -rf $SOURCE_DIR/triton_library.egg-info

echo "[+] Change permissions for directories"
chown -R 1000:1000 $WHEEL_DIR
